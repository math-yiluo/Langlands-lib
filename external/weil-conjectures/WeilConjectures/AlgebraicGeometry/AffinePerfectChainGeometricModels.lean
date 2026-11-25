/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.AffineSpecifiedModelChainComparison
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.PerfectAffineBoundedProjective
import WeilConjectures.AlgebraicGeometry.SchemeIsoPerfectTransport
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedLocalizations
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedEquivalence

/-! # Affine perfect models and geometric chain-map comparison

Source: Stacks Project, perfect.tex, Tags 09RE, 08EB, 06Z0 and 08DW.
(blueprint: lem-pc-affine-perfect-chain-geometric-models).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

-- Elaborating the affine models and their chosen derived-category comparisons needs this budget.
set_option backward.isDefEq.respectTransparency false in
/-- Affine finite-projective models with scalar/geometric Hom equivalences.
Source: Stacks Project, perfect.tex, Tag 09RE, affine calculation; Tags 08EB,
06Z0 and 08DW.
(blueprint: lem-pc-affine-perfect-chain-geometric-models).

Proof: Put B = Gamma(Y, O_Y) and identify Y with Spec B by Y.isoSpec.
The map s gives R(i) to B. On the tail define F(j) = B tensor over R(i)
with R(j), with maps induced by R. Extension of scalars is a left adjoint,
so colim F is B tensor over R(i) with c.pt. The tensor-product universal
property identifies Spec F(j) and Spec(colim F) with the given pullbacks.
Transport P and Q along Y.isoSpec. Scheme-isomorphism derived equivalence
preserves perfectness and quasi-coherent homology, and transport of localized
open sites supplies the chosen derived categories at the same Hom universe.
Apply the affine bounded-projective criterion to both objects, and transport
these complexes along F(i) iso B. This gives E and K and the stated bounds,
finiteness and projectivity. Projective terms are flat, and the bounded
complexes are K-flat, so affine derived pullback is termwise scalar extension.
At every stage and at the limit apply the affine quasi-coherent derived
equivalence, conjugating its Hom equivalence by these object comparisons;
fullness of the quasi-coherent subcategory gives the displayed equivalences.
Naturality of the tilde pullback comparison on chain maps says that extending
a chain map and then taking tilde equals pulling back its tilde. Tensor
associativity and the counit-pinned derived pullback composition comparison
identify the conjugations with perfectStageMap and perfectLimitMap. This gives
the two displayed equations. No Hom diagram or cocone is constructed here.
All universal-property constructions work for the zero ring; the tail's
initial object is i, so no choice of a nonempty point is used. -/
theorem exists_affinePerfectChainGeometricModels
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    [∀ A : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q) :
    ∃ (F : Set.Ici i ⥤ CommRingCat.{u})
      (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ),
      ((∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧
        ∀ n : ℤ, Module.Finite (F.obj ⟨i, le_rfl⟩) (E.X n) ∧
          Module.Projective (F.obj ⟨i, le_rfl⟩) (E.X n)) ∧
      ((∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)) ∧
        ∀ n : ℤ, Module.Finite (F.obj ⟨i, le_rfl⟩) (K.X n) ∧
          Module.Projective (F.obj ⟨i, le_rfl⟩) (K.X n)) ∧
      ∃ (stage : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          (DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
           DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)) ≃
          ((derivedPullback (pullback.fst s
            (Spec.map (R.map (homOfLE j.val.property))))).obj P ⟶
           (derivedPullback (pullback.fst s
            (Spec.map (R.map (homOfLE j.val.property))))).obj Q))
        (limit :
          (DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (colimit.ι F ⟨i, le_rfl⟩).hom) (.up ℤ)).obj E) ⟶
           DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (colimit.ι F ⟨i, le_rfl⟩).hom) (.up ℤ)).obj K)) ≃
          ((derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P ⟶
           (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q)),
        (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k)
          (f : ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)),
          stage k (DerivedCategory.Q.map (CochainComplex.scalarExtensionHom
              (F.map (homOfLE j.property)).hom (F.map (homOfLE hjk)).hom
              (F.map (homOfLE k.property)).hom
              (congrArg CommRingCat.Hom.hom (F.map_comp
                (homOfLE j.property) (homOfLE hjk))) E K f)) =
            perfectStageMap R s j.val.property hjk
              (stage j (DerivedCategory.Q.map f))) ∧
        (∀ (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i))
          (f : ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)),
          limit (DerivedCategory.Q.map (CochainComplex.scalarExtensionHom
              (F.map (homOfLE j.property)).hom (colimit.ι F j.val).hom
              (colimit.ι F ⟨i, le_rfl⟩).hom
              (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE j.property)).symm)
              E K f)) =
            perfectLimitMap R c s j.val.property
              (stage j (DerivedCategory.Q.map f))) := by
  let B := Scheme.Γ.obj (.op Y)
  let t : Spec B ≅ Y := Y.isoSpec.symm
  obtain ⟨e, ⟨he⟩⟩ := Scheme.exists_scheme_iso_derived_equivalence t
  classical
  let hopen := Classical.choice
    (Scheme.exists_scheme_iso_derived_localizations t).choose_spec
  let : ∀ U : (Spec B).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec B).toRingedSpace).over U)) := hopen
  have hP' := Scheme.scheme_iso_derived_inverse_preserves_perfect t e he P hP
  have hQ' := Scheme.scheme_iso_derived_inverse_preserves_perfect t e he Q hQ
  let P' : schemeDerivedQCohCategory (Spec B) :=
    ⟨e.inverse.obj P, schemeDerivedQCohProperty_of_isPerfect (Spec B) _ hP'⟩
  let Q' : schemeDerivedQCohCategory (Spec B) :=
    ⟨e.inverse.obj Q, schemeDerivedQCohProperty_of_isPerfect (Spec B) _ hQ'⟩
  let : ∀ U : (Spec (.of B)).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of B)).toRingedSpace).over U)) := hopen
  obtain ⟨E₀, hbE, hfE, hpE, ⟨hPE⟩⟩ :=
    (perfect_iff_affine_bounded_projective B P').mp hP'
  obtain ⟨K₀, hbK, hfK, hpK, ⟨hQK⟩⟩ :=
    (perfect_iff_affine_bounded_projective B Q').mp hQ'
  obtain ⟨F, r, hE, hK, stage, limit, hs, hl⟩ :=
    exists_affineSpecifiedModelChainComparison R c hc i Y s t e he P Q E₀ K₀
      ⟨hbE, fun n ↦ ⟨hfE n, hpE n⟩⟩ ⟨hbK, fun n ↦ ⟨hfK n, hpK n⟩⟩ hPE hQK
  exact ⟨F, _, _, hE, hK, stage, limit, hs, hl⟩

end AlgebraicGeometry
