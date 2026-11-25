/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSums
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.AlgebraicGeometry.PerfectObjectCompact
import WeilConjectures.AlgebraicGeometry.PerfectComplexRepresentatives
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import WeilConjectures.AlgebraicGeometry.SupportedDerivedGeneratedPerfect
import WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated
import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSumsAux
import WeilConjectures.AlgebraicGeometry.PerfectThickClosure
import WeilConjectures.CategoryTheory.CompactGeneratorAmbientThick

/-! # Small representatives of compact quasi-coherent derived objects

Source: Stacks Project, Tags 09M1 and 09IS; perfect-complex representative argument.
(blueprint: lem-sc-derived-qcoh-compact-representatives).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Derived categories exist on all open subschemes of a Noetherian scheme.
Source: Grothendieck abelianity of sheaves of modules on a small ringed site
and `HasDerivedCategory.ofIsGrothendieckAbelian`.
(blueprint: lem-sc-derived-qcoh-compact-open-categories) -/
theorem noetherian_open_derived_categories_exists (X : Scheme.{u}) [IsNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    Nonempty (∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))) := by
  exact nonempty_derivedOpenLocalization X

/-- Perfectness is unchanged by an isomorphism of ambient derived objects. -/
private theorem perfect_of_iso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    {E F : schemeDerivedCategory X} (e : E ≅ F) (hE : Scheme.IsPerfect X E) :
    Scheme.IsPerfect X F := by
  intro x
  obtain ⟨U, hx, K, hK, ⟨eK⟩⟩ := hE x
  exact ⟨U, hx, K, hK, ⟨((SheafOfModules.overFunctor.{u}
    (moduleRings X.toRingedSpace) U).mapDerivedCategory.mapIso e.symm) ≪≫ eK⟩⟩

/-- The concrete perfect-complex closure theorem supplies Mathlib's thick-property API. -/
private theorem perfect_thick_property (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (G : schemeDerivedCategory X) (hG : Scheme.IsPerfect X G) :
    (Scheme.perfectSubcategory X).IsTriangulated ∧
      (Scheme.perfectSubcategory X).IsStableUnderRetracts := by
  let : Zero (schemeDerivedCategory X) := HasZeroObject.zero' (schemeDerivedCategory X)
  obtain ⟨htri, hsum, hshift, _⟩ := Scheme.perfect_thick_closure.{u, w, u} X
  let Q := Scheme.perfectSubcategory X
  have hiso : Q.IsClosedUnderIsomorphisms := by
    constructor
    intro E F e hE
    exact perfect_of_iso X e hE
  let := hiso
  have hret : Q.IsStableUnderRetracts := by
    constructor
    intro E F r hF
    obtain ⟨Z, a, b, ht⟩ := Pretriangulated.distinguished_cocone_triangle r.i
    let T := Pretriangulated.Triangle.mk r.i a b
    have hb : T.mor₃ = 0 :=
      T.mor₃_eq_zero_of_mono₁ ht (show Mono r.i from inferInstance)
    obtain ⟨e, _, _⟩ := Pretriangulated.exists_iso_binaryBiproduct_of_distTriang T ht hb
    exact (hsum E Z (perfect_of_iso X e hF)).1
  let := hret
  have hzero : Q.ContainsZero :=
    ⟨0, isZero_zero _, Q.prop_of_retract ((isZero_zero _).retract G) hG⟩
  let := hzero
  have hsh : Q.IsStableUnderShift ℤ := by
    constructor
    intro n
    exact ObjectProperty.IsStableUnderShiftBy.mk (fun E hE ↦ hshift E n hE)
  let := hsh
  have hcone : Q.IsTriangulatedClosed₂ := by
    apply ObjectProperty.IsTriangulatedClosed₂.mk'
    intro T ht h₁ h₃
    exact (htri T ht).2.2 h₁ h₃
  let := hcone
  exact ⟨ObjectProperty.IsTriangulated.mk, hret⟩

/-- Compact objects in the quasi-coherent derived category are perfect.
Source: Stacks Project, Tag 09M1, converse direction of
`perfect-proposition-compact-is-perfect`; restriction to affine opens and the
finite-projective criterion reduce compactness to perfectness.
(blueprint: lem-sc-derived-qcoh-compact-is-perfect)
Proof: Use the existing perfect supported generator with empty excluded open to obtain
an explicit generator telescope for P. Compactness factors the identity through a finite
thick construction from that generator. Perfectness is closed under shifts, triangles
and retracts, so the ambient thick envelope consists of perfect objects. The retract
closure is derived from the split-triangle biproduct decomposition, and the zero object
is a retract of the perfect generator. This route does not require comparing open models. -/
theorem compact_isPerfect_of_isNoetherian (X : Scheme.{u}) [IsNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [hOpen : ∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let _ : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
    ∀ P : schemeDerivedQCohCategory X, IsCompactObject P → Scheme.IsPerfect X P.obj := by
  let _ : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
  dsimp only
  intro P hP
  have hqc : (schemeDerivedQCohProperty X).IsTriangulated := by
    simpa using supported_qcoh_isTriangulated X Set.univ
  let := hqc
  have hqciso : (schemeDerivedQCohProperty X).IsClosedUnderIsomorphisms := by
    constructor
    intro E F e hE n
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).mapIso e) (hE n)
  let := hqciso
  let (I : Type u) :
      (schemeDerivedQCohProperty X).IsClosedUnderColimitsOfShape (Discrete I) :=
    schemeDerivedQCohClosedUnderCoproducts X I
  obtain ⟨G, hG, _, hbuild⟩ := supported_derived_generated_perfect X ⊥ (by simp)
  obtain ⟨K, t, hzero, hsteps, S, ⟨hS⟩, s, q, r, hs, hT⟩ := hbuild P (by simp)
  have hmem := compact_generator_ambient_thick (schemeDerivedQCohProperty X) G
    (perfectObjectCompact X G hG) P hP K t hzero hsteps S hS s q r hs hT
  obtain ⟨hperftri, hperfretract⟩ := perfect_thick_property X G.obj hG
  let := hperftri
  let := hperfretract
  have hle : (ObjectProperty.singleton G.obj).triangEnvelope ≤
      Scheme.perfectSubcategory X :=
    (ObjectProperty.triangEnvelope_le_iff _).2 (by
      intro E hE
      rw [ObjectProperty.singleton_iff] at hE
      subst E
      exact hG)
  exact hle P.obj hmem

/-- Noetherian schemes have a universe-small family of perfect representatives.
Source: Stacks Project, Tags 08EB and 09M1, together with the finite affine
cover gluing argument of `lem-pc-perfect-complexes-compact-set`.
(blueprint: lem-sc-derived-qcoh-perfect-representatives-noetherian)
The affine representatives glue over a finite affine cover; the required
derived categories on opens and the compact and separated instances are
provided by the Noetherian hypotheses. -/
theorem noetherian_perfect_representatives (X : Scheme.{u}) [IsNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [hOpen : ∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    ∃ (S : Type u) (G : S → schemeDerivedQCohCategory X),
      (∀ s : S, Scheme.IsPerfect X (G s).obj) ∧
      ∀ P : schemeDerivedQCohCategory X, Scheme.IsPerfect X P.obj →
        ∃ s, Nonempty (P ≅ G s) := by
  exact Scheme.exists_perfectComplex_representatives X

/-- Perfect objects on a Noetherian scheme are compact in its QCoh derived category.
Source: Stacks Project, Tag 09M1, the perfect-to-compact implication, using
tensor-Hom duality and preservation of coproducts.
(blueprint: lem-sc-derived-qcoh-perfect-compact-noetherian)
This is the Noetherian specialization of `perfectObjectCompact`; all local
derived-category and quasi-compactness infrastructure is discharged in the
intermediate theorem. -/
theorem noetherian_perfect_compact (X : Scheme.{u}) [IsNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [hOpen : ∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let _ : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
    ∀ (P : schemeDerivedQCohCategory X), Scheme.IsPerfect X P.obj → IsCompactObject P := by
  exact perfectObjectCompact X

/-- Compact objects of the quasi-coherent derived category have small representatives.
Source: Stacks Project, Tags 09M1 and 09IS, and the set-of-representatives argument
of `lem-pc-perfect-complexes-compact-set`.
(blueprint: lem-sc-derived-qcoh-compact-representatives).

Proof: Noetherian schemes are quasi-compact and quasi-separated. First work in
small-Hom derived models on X and on all its opens: K-injective resolutions give
these models and localization equivalences to the supplied derived category.
Compact objects are perfect by Tag 09M1: restriction to an affine open preserves
compactness since its right adjoint commutes with sums, and the affine module
criterion identifies compact objects with bounded finite-projective complexes.
Perfect complexes have a universe-u set of representatives: on affines encode
bounded finite-projective complexes by summands of finite free modules and their
matrices; glue across a finite affine cover using Mayer-Vietoris triangles and
small Hom sets. Every representative is compact by perfectObjectCompact.
Transport the representatives and their isomorphisms back along the localization
equivalence. Its additive Hom equivalences and preservation of coproducts identify
the compactness comparison maps, so compactness is preserved and reflected.
The zero object is included, including when X is empty; no nonempty indexing type
is assumed. All choices occur inside an existence theorem, not in a definition. -/
theorem derivedQCoh_compact_representatives (X : Scheme.{u}) [IsNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    let _ : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
    ∃ (S : Type u) (G : S → schemeDerivedQCohCategory X),
      (∀ s, IsCompactObject (G s)) ∧
      ∀ P : schemeDerivedQCohCategory X, IsCompactObject P →
        ∃ s, Nonempty (P ≅ G s) := by
  let _ : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
  let _ : ∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    Classical.choice (noetherian_open_derived_categories_exists X)
  obtain ⟨S, G, hperf, hrep⟩ := noetherian_perfect_representatives X
  refine ⟨S, G, ?_, ?_⟩
  · intro s
    exact noetherian_perfect_compact X (G s) (hperf s)
  · intro P hP
    obtain ⟨s, hs⟩ := hrep P (compact_isPerfect_of_isNoetherian X P hP)
    exact ⟨s, hs⟩

end AlgebraicGeometry
