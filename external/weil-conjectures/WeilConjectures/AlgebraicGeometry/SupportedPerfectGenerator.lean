/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Topology.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.SupportedPerfectDetectorAffine
import WeilConjectures.AlgebraicGeometry.SupportedPerfectDetectorGluing
import WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated

/-! # Perfect generators with support

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.15.4 (Tag 0A9A)
(blueprint: lem-pc-supported-perfect-generator).

Support on `T` is the stalkwise form of the existing support statements: every cohomology
sheaf has zero stalk at every point outside `T`. `D_QCoh,T(O_X)` is the full subcategory
of `D(O_X)` on objects with quasi-coherent cohomology supported on `T`. The weak generator
condition (`def-pc-generators`) is expressed by the shifted-Hom vanishing criterion, as in
`AlgebraicGeometry.perfect_generator_pullback`; Hom groups and shifts of the full
subcategory are those of the ambient derived category.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The full subcategory of quasi-coherent derived objects supported on a closed subset
with quasi-compact complement is triangulated and has a single perfect weak generator
supported on that subset.
Source: Stacks Project, Lemma 36.15.4 (Tag 0A9A).
(blueprint: lem-pc-supported-perfect-generator).

Proof:
1. If X is affine, its quasi-compact open complement of T is a finite union of principal
opens D(fᵢ). The Koszul complex on the fᵢ is perfect and supported on T, since each fᵢ acts
null-homotopically. Koszul orthogonality (lem-pc-perfect-generation-koszul-orthogonal)
identifies an object orthogonal to its shifts with the derived pushforward of its zero
restriction to the complement. Thus it generates the supported category.
2. Induct on a finite affine open cover. Write X = U ∪ V, with V affine and U the union
of the earlier members. Quasi-separatedness ensures U and its complement of T satisfy
the hypotheses. Choose a perfect supported generator P on U by induction.
3. Use lem-sc-perfect-support-map-lift with the zero map P → 0 to lift P to a summand
of Q|U, with Q perfect on X and supported on T.
4. Put Z = X minus U. The complement of Z ∩ T in V is quasi-compact. The affine
Koszul construction gives K supported on Z ∩ T. By lem-pc-supported-open-pushforward,
K' = R(V → X)₊K is perfect and equals extension by zero. Q ⊕ K' is perfect and supported.
5. If E is orthogonal to every shift of Q ⊕ K', open restriction adjunction gives
orthogonality to K on V. Koszul orthogonality identifies E|V with pushforward from
W = V minus (Z ∩ T). Supported-open pushforward identifies E|W with pushforward from
U ∩ V. Derived direct-image composition and open restriction base change show that
the unit E → R(U → X)₊(E|U) is an isomorphism on U and V, hence globally.
6. Adjunction gives Hom(Q[n], E) = Hom(Q|U[n], E|U), containing Hom(P[n], E|U) as a
summand. The latter groups vanish, so E|U = 0 by induction and E = 0 by step 5.
The weak-generator definition now yields the generator Q ⊕ K'.
7. Zero, shifts and extensions preserve quasi-coherence and support. For extensions,
use the long exact cohomology sequence and exact open restriction. Thus the full
subcategory inherits its triangulated structure from the ambient derived category. -/
theorem supported_perfect_generator (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ) :
    ObjectProperty.IsTriangulated (fun K : schemeDerivedCategory X ↦
      schemeDerivedQCohProperty X K ∧
        ∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).val.presheaf x))) ∧
    ∃ E : schemeDerivedQCohCategory X, Scheme.IsPerfect X E.obj ∧
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E.obj).val.presheaf x))) ∧
      ∀ K : schemeDerivedQCohCategory X,
        (∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K.obj).val.presheaf x))) →
        (IsZero K.obj ↔ ∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj)) := by
  classical
  refine ⟨supported_qcoh_isTriangulated X T, ?_⟩
  have detectors : ∀ (m : ℕ) (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
      [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
      [∀ U : Y.Opens,
        HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
      (s : Finset Y.affineOpens), s.card = m →
      (⨆ U ∈ s, (U : Y.Opens)) = ⊤ →
      ∀ (S : Set Y), IsClosed S → IsCompact Sᶜ →
        ∃ E : schemeDerivedQCohCategory Y, Scheme.IsPerfect Y E.obj ∧
          (∀ (n : ℤ) (x : Y), x ∉ S →
            Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj E.obj).val.presheaf x))) ∧
          ∀ K : schemeDerivedQCohCategory Y,
            (∀ (n : ℤ) (x : Y), x ∉ S →
              Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj K.obj).val.presheaf x))) →
            (∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj)) → IsZero K.obj := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro Y _ _ _ _ s hm hcover S hS hSc
      by_cases hsmall : s.card ≤ 1
      · exact supported_perfect_detector_affine Y s hcover hsmall S hS hSc
      · refine supported_perfect_detector_gluing Y s hcover (by omega) ?_ S hS hSc
        intro Z _ _ _ _ t ht htcover R hR hRc
        exact ih t.card (hm ▸ ht) Z t rfl htcover R hR hRc
  obtain ⟨s, hs, hcover⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := X) (U := ⊤)).mp
      (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X)))
  obtain ⟨E, hE, hET, hdetect⟩ :=
    detectors hs.toFinset.card X hs.toFinset rfl (by simpa using hcover.symm) T hT hTc
  refine ⟨E, hE, hET, ?_⟩
  intro K hKT
  refine ⟨?_, hdetect K hKT⟩
  intro hK n
  exact ⟨fun f g ↦ hK.eq_of_tgt f g⟩

end AlgebraicGeometry
