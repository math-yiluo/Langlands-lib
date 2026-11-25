/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
public import WeilConjectures.AlgebraicGeometry.SfDiagonalKernelIntegrals
import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransport

/-! # Standard-chart projective-line coordinate integrals

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, trace base change and the two diagonal integrals.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

-- Use the derived-category instance witnesses captured by the library abbreviation.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local instance] MvPolynomial.gradedAlgebra

private noncomputable def renameGraded {σ τ : Type u} (e : σ ≃ τ) :
    MvPolynomial.homogeneousSubmodule σ (ULift.{u} ℤ) →+*ᵍ
      MvPolynomial.homogeneousSubmodule τ (ULift.{u} ℤ) where
  __ := (MvPolynomial.renameEquiv (ULift.{u} ℤ) e).toRingEquiv.toRingHom
  map_mem := fun h ↦ h.rename_isHomogeneous

private theorem rename_irrelevant {σ τ : Type u} (e : σ ≃ τ) :
    HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule τ (ULift.{u} ℤ)) ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule σ (ULift.{u} ℤ))).map (renameGraded e) := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_map,
    MvPolynomial.toIdeal_irrelevant_homogeneousSubmodule,
    MvPolynomial.toIdeal_irrelevant_homogeneousSubmodule]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have h := Ideal.mem_map_of_mem (renameGraded e)
    (Ideal.subset_span (Set.mem_range_self (f := MvPolynomial.X) (e.symm i)))
  simpa [renameGraded] using h

private noncomputable def renameProjIso {σ τ : Type u} (e : σ ≃ τ) :
    Proj.projectiveSpaceOverAffine τ (ULift.{u} ℤ) ≅
      Proj.projectiveSpaceOverAffine σ (ULift.{u} ℤ) where
  hom := Proj.map (renameGraded e) (rename_irrelevant e)
  inv := Proj.map (renameGraded e.symm) (rename_irrelevant e.symm)
  hom_inv_id := by
    rw [← Proj.map_comp]
    have h : (renameGraded e).comp (renameGraded e.symm) =
        GradedRingHom.id (MvPolynomial.homogeneousSubmodule τ (ULift.{u} ℤ)) := by
      ext i
      simp [renameGraded]
    simp only [h, Proj.map_id, Proj.projectiveSpaceOverAffine]
  inv_hom_id := by
    rw [← Proj.map_comp]
    have h : (renameGraded e.symm).comp (renameGraded e) =
        GradedRingHom.id (MvPolynomial.homogeneousSubmodule σ (ULift.{u} ℤ)) := by
      ext i
      simp [renameGraded]
    simp only [h, Proj.map_id, Proj.projectiveSpaceOverAffine]

@[irreducible]
private noncomputable def p1CoordinateIso (S : Scheme.{u}) :
    ProjectiveSpace (Option (ULift.{u} (Fin 1))) S ≅ ProjectiveLine S := by
  let e : ULift.{u} (Fin 2) ≃ Option (ULift.{u} (Fin 1)) :=
    Equiv.ulift.trans ((finSuccEquiv 1).trans (Equiv.optionCongr Equiv.ulift.symm))
  let i := renameProjIso e
  exact asIso (pullback.map _ _ _ _ (𝟙 S) i.hom (𝟙 _)
    (by simp) (by simp))

private theorem p1CoordinateIso_over (S : Scheme.{u}) :
    (p1CoordinateIso S).hom ≫ (ProjectiveLine S ↘ S) =
      (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S ↘ S) := by
  change _ ≫ pullback.fst _ _ = pullback.fst _ _
  simp only [p1CoordinateIso, asIso_hom, pullback.map, pullback.lift_fst,
    Category.comp_id]

private theorem finiteLine_lisse (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (S : Scheme.{u})
    (hInvertible : ∀ s : S, IsUnit (N : S.presheaf.stalk s)) :
    Scheme.IsLisseRankOneSheaf (Scheme.finiteEtaleTateLine S N A hA) := by
  obtain ⟨cover, hcover⟩ :=
    (Scheme.finite_etale_torsion_twist_line S N hN hInvertible A hA 1).1
  refine ⟨cover, fun i ↦ ?_⟩
  obtain ⟨ei⟩ := hcover i
  let U := cover.etalePrecoverageToEtale i
  let E := Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} A)
  let c := (Scheme.Etale.overEquiv U).constantSheafSheafCongrIso
    (S.smallEtaleTopology.over U) U.left.smallEtaleTopology (ModuleCat.{u + 1} A)
    Over.mkIdTerminal
  exact ⟨(Scheme.overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} A) U
    (Scheme.finiteEtaleTateLine S N A hA)).symm ≪≫
      E.functor.mapIso ei ≪≫ c.app (ModuleCat.of A A)⟩

private theorem conjugate_identity
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {U : C} {V : D} (c : F.obj U ≅ V) (g : U ⟶ U) (hg : g = 𝟙 U) :
    c.inv ≫ F.map g ≫ c.hom = 𝟙 V := by
  rw [hg, F.map_id, Category.id_comp, c.inv_hom_id]

/-- The arbitrary-base projective-line trace and supported diagonal, expressed in
standard-chart coordinates and the compact-support comparison conventions.
The conclusion consists only of coefficient pullback and two degree-zero integral
identities, with no unit, counit, adjunction, or claim about arbitrary complexes.

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, trace base-change normalization and diagonal integrals
(auxiliary; not a blueprint node).

Proof: The stalkwise invertibility hypothesis implies invertibility of N in the
global sections of S, since invertibility is local on the Zariski site. Apply
exists_arbitraryBaseFiniteP1Integrals. Rename the two homogeneous coordinates by
the equivalence from Option (ULift (Fin 1)) to ULift (Fin 2); graded polynomial
renaming induces an isomorphism of projective schemes over S. Transport the
splitting's trace and its supported Kummer diagonal along that isomorphism and
its self-product. Exact constant inverse image and the normalized finite Tate
line comparison identify B with q* (A_S(1)[2]), giving e. The finite twist line
theorem, transported from slice restriction to inverse image, gives its lisse
rank-one property. For each projection use the canonical projective-line chart
over P. The arbitrary-base trace base-change equation identifies the chart's
trace with inverse proper exchange followed by q* of the original trace, which
is precisely traceFirst or traceSecond. Exact closed direct image identifies the
supported Ext representative with the diagonalClass source. The composite
inverse-image/direct-image unit for p_i Delta = id identifies the source alpha
with diagonalFirst or idIsoDiagonalSnd. The proper forget-supports isomorphisms
intertwine these source comparisons and exchange maps with the compact-support
ones. Thus the two normalized integral equations from finiteP1DiagonalProperty
are exactly Integrals. All transport maps are the canonical ones, so both
equations use the same trace and supported class. Coordinate renaming and these
comparisons apply over the empty base as well; for N = 1 the coefficient ring
is zero and the identical equations hold in the zero module category. -/
theorem sfP1CoordinateIntegrals
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsAffine S]
    (hInvertible : ∀ s : S, IsUnit (N : S.presheaf.stalk s)) :
    ∃ d : TraceDiagonalDatum A
        (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S ↘ S)
        (((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateLine
            (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S) N A hA))⟦(2 : ℤ)⟧),
      ∃ e : (((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateLine
            (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S) N A hA))⟦(2 : ℤ)⟧) ≅
        (CoordinateTrace.pull A
          (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S ↘ S)).obj
            (CoordinateTrace.shiftedLine A (Scheme.finiteEtaleTateLine S N A hA) 1),
        Scheme.IsLisseRankOneSheaf (Scheme.finiteEtaleTateLine S N A hA) ∧
          SfDiagonalKernel.Integrals A d
            (CoordinateTrace.shiftedLine A (Scheme.finiteEtaleTateLine S N A hA) 1) e := by
  classical
  have hS : IsUnit (N : Γ(S, ⊤)) :=
    S.toRingedSpace.isUnit_of_isUnit_germ ⊤ (N : Γ(S, ⊤))
      (fun s _ ↦ by simpa only [map_natCast] using hInvertible s)
  obtain ⟨t, d, hbc, hd⟩ := exists_arbitraryBaseFiniteP1Integrals N hN A hA
  obtain ⟨hI, κ, hκ, hi⟩ := hd S hS
  obtain ⟨D, c, hfirst, hsecond⟩ := sfP1IntegralTransport A N hA t d hbc S
    (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S)
    (ProjectiveSpace (Option (ULift.{u} (Fin 1))) S ↘ S)
    (p1CoordinateIso S) (p1CoordinateIso_over S) hS κ
  refine ⟨D, (ordinaryFiniteShiftedLinePullback A N hA t _ hS).symm,
    finiteLine_lisse A N hN hA S hInvertible, ?_⟩
  constructor
  · exact hfirst.trans (conjugate_identity _ c _ (hi false).2)
  · exact hsecond.trans (conjugate_identity _ c _ (hi true).2)

end AlgebraicGeometry.Etale
