/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
import WeilConjectures.AlgebraicGeometry.CofilteredEtaleCohomologyCocone
import WeilConjectures.AlgebraicGeometry.IntegralCoverTrivialCohomology
import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FinitePresentationApproximation

/-!
# Finite covers kill classes with finite constant coefficients

Source: Stacks Project, Lemma 59.80.9 (Tag 09ZD), part (2)
(blueprint: lem-weil-pbc-integral-cover-kills-constant-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

-- Compare total derived global sections with classical right-derived evaluation,
-- then use the existing Ext/evaluation comparison.
private theorem subsingleton_H_of_isZero_derived_cohomology
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : IsZero ((cohomology AddCommGrpCat.{u + 1} X (q : ℤ)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F))) :
    Subsingleton (Sheaf.H F q) := by
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
      (Opposite.op (Scheme.Etale.mk (𝟙 X)))
  let eΓ : Γ ≅ E := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal _ X)
  let eR : Γ.rightDerived q ≅ E.rightDerived q :=
    { hom := eΓ.hom.rightDerived q
      inv := eΓ.inv.rightDerived q
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, eΓ.hom_inv_id]; simp
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, eΓ.inv_hom_id]; simp }
  have hz : IsZero ((Γ.rightDerived q).obj F) :=
    h.of_iso (Γ.homologyRightDerivedFunctorObjSingleFunctorIso F q).symm
  have hz' := hz.of_iso (eR.app F).symm
  have : Subsingleton ((E.rightDerived q).obj F) := AddCommGrpCat.subsingleton_of_isZero hz'
  cases q with
  | zero =>
    let a := (Sheaf.H.equiv₀ F (MorphismProperty.Over.mkIdTerminal _ X)).trans
      ((E.rightDerivedZeroIsoSelf.app F).addCommGroupIsoToAddEquiv.symm)
    exact a.injective.subsingleton
  | succ n =>
    obtain ⟨a⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
      X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X))
      (MorphismProperty.Over.mkIdTerminal _ X) F n
    exact a.injective.subsingleton

-- The cocone theorem supplies continuity; equality in its concrete filtered colimit
-- is witnessed at a stage. This avoids importing Gabber, which imports this module.
private theorem finite_stage_zero
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    {S : Scheme.{u}} (D : J ⥤ Scheme.{u}) (π : D ⟶ (Functor.const J).obj S)
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)] (c : Cone D) (hc : IsLimit c)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (x : Sheaf.H G q)
    (j₀ : J) (hx : cohomologyMap (c.π.app j₀ ≫ π.app j₀) G q x = 0) :
    ∃ j, cohomologyMap (π.app j) G q x = 0 := by
  obtain ⟨H, eH, r, hr, heH, B, hB, e, he⟩ :=
    exists_cofiltered_etale_cohomology_cocone D π c hc G q j₀
  have hzero : B.ι.app (Opposite.op j₀) (r j₀ x) =
      B.ι.app (Opposite.op j₀) (0 : H.obj (Opposite.op j₀)) := by
    apply (ConcreteCategory.bijective_of_isIso e.hom).1
    simpa only [map_zero] using (he j₀ x).trans hx
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  obtain ⟨j, f, hf⟩ := (hB.eq_iff' (r j₀ x) 0).mp hzero
  refine ⟨j.unop, ?_⟩
  have hj : r j.unop x = 0 := by
    rw [← hr j.unop j₀ f.unop x]
    simpa only [Quiver.Hom.op_unop, map_zero] using hf
  rw [← heH j.unop x, hj, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Stacks Project, Lemma 59.80.9 (Tag 09ZD), part (2)
(blueprint: lem-weil-pbc-integral-cover-kills-constant-cohomology).
A positive-degree class with finite constant abelian coefficients on a closed subscheme
of an affine scheme dies after base change to a finite surjective cover of finite presentation.
The constant-sheaf comparison identifies the inverse-image coefficients with the constant
sheaf on the fibre product.

Proof:
1. Apply `lem-weil-pbc-integral-cover-trivial-cohomology` (09ZD (1)) to obtain an integral
   surjective cover whose every closed subscheme has zero positive constant cohomology.
2. The base change of the closed immersion is closed
   (`lem-weil-pbc-closed-immersion-base-change`), so the class dies there. Identify the
   coefficients using `lemma-constructible-pullback-constant`; cohomology respects this
   identification by `proposition-cohomology-p-1-over-henselian--1`.
3. Write the integral cover as a nonempty directed limit of finite finitely presented covers
   by `lem-weil-pbc-integral-morphism-limit-of-finite` (09YZ). They are affine by
   `lem-weil-pbc-finite-morphism-permanence`; use `lem-weil-pbc-qcqs-over-affine` and
   `lem-weil-pbc-spec-colimit-limit` to identify the cover with the spectrum of the colimit
   of their rings (`def-weil-pbc-category-colimit`, `def-weil-affine-spectrum`).
4. Write the closed subscheme as Spec B for a quotient A → B. Base change is tensor product
   (`lem-weil-pbc-fibre-product-affine-spectra`), and the base-changed rings have the correct
   colimit by `lem-weil-pbc-filtered-colimit-tensor-varying-rings`.
5. Apply `lem-weil-pbc-etale-cohomology-limit-of-schemes` (03Q6/09YQ) to this ring system.
   Pullback functoriality makes the finite-stage classes compatible with the limit class.
6. The limit class is zero, hence a finite-stage class is zero by
   `def-weil-directed-colimit-abelian-groups`. Transport it back to the fibre product using
   `proposition-cohomology-p-1-over-henselian--1`.
7. That stage is finite and finitely presented; it is surjective because the integral
   surjective cover factors through it. It is the required cover. -/
theorem exists_isFinite_surjective_constant_cohomology_eq_zero
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
    (M : AddCommGrpCat.{u + 1}) [Finite M] (q : ℕ) (hq : 1 ≤ q)
    (ξ : Sheaf.H ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsFinite f ∧ Surjective f ∧ LocallyOfFinitePresentation f ∧
        Sheaf.H.map
          ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
            (pullback.snd f i)).hom.app M) q
          (cohomologyMap (pullback.snd f i)
            ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q ξ) = 0 := by
  classical
  obtain ⟨T, π, hπ, hsurj, hvanish⟩ := exists_integral_cover_trivial_cohomology X
  let : IsIntegralHom π := hπ
  have hzero := hvanish (pullback π i) (pullback.fst π i) M (q : ℤ) (by omega)
  have hsub := subsingleton_H_of_isZero_derived_cohomology (pullback π i) _ q hzero
  have hξ : cohomologyMap (pullback.snd π i)
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q ξ = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      ((Sheaf.functorH _ q).mapIso
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (pullback.snd π i)).app M)).hom).1
    simp only [map_zero]
    exact hsub.elim _ _
  obtain ⟨F, hfp⟩ := π.exists_finiteApproximation_of_isIntegralHom
  -- Apply scheme continuity directly to the base-changed approximation.
  -- Pullback preserves limits in Over; forgetting preserves connected limits.
  let s : F.D ⟶ (Functor.const F.I).obj X :=
    { app := F.p
      naturality := fun _ _ g ↦ by simp [F.map_p g] }
  let cX := Cone.mk T F.π
  let cOver := Over.liftCone F.D s cX π F.π_p
  let b := Over.pullback i ⋙ Over.forget Z
  let D := Over.lift F.D s ⋙ b
  let c : Cone D := b.mapCone cOver
  have : Nonempty F.I := IsCofiltered.nonempty
  have : IsConnected F.I := IsCofiltered.isConnected F.I
  have hc : IsLimit c :=
    isLimitOfPreserves b (Over.isLimitLiftCone F.D s cX π F.π_p F.isLimit)
  let v : D ⟶ (Functor.const F.I).obj Z :=
    { app := fun j ↦ pullback.snd (F.p j) i
      naturality := by
        intro j k g
        change pullback.lift _ (pullback.snd (F.p j) i) _ ≫ pullback.snd (F.p k) i = _
        exact pullback.lift_snd _ _ _ }
  have (j : F.I) : IsAffine (F.D.obj j) := isAffine_of_isAffineHom (F.p j)
  have : IsAffine Z := isAffine_of_isAffineHom i
  have (j : F.I) : IsAffine (D.obj j) := by
    change IsAffine (pullback (F.p j) i)
    infer_instance
  have {j k : F.I} (g : j ⟶ k) : IsAffineHom (D.map g) := inferInstance
  let j₀ : F.I := Classical.choice (IsCofiltered.nonempty (C := F.I))
  have hcξ : cohomologyMap (c.π.app j₀ ≫ v.app j₀)
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q ξ = 0 := by
    have heq : c.π.app j₀ ≫ v.app j₀ = pullback.snd π i := by
      change pullback.lift _ (pullback.snd π i) _ ≫ pullback.snd (F.p j₀) i = _
      exact pullback.lift_snd _ _ _
    rw [heq]
    exact hξ
  obtain ⟨j, hj⟩ := finite_stage_zero D v c hc _ q ξ j₀ hcξ
  refine ⟨F.D.obj j, F.p j, inferInstance, ?_, hfp j, ?_⟩
  · have : Surjective (F.π.app j ≫ F.p j) := by rw [F.π_p]; exact hsurj
    exact Surjective.of_comp (F.π.app j) (F.p j)
  · change Sheaf.H.map _ q (cohomologyMap (v.app j) _ q ξ) = 0
    rw [hj, map_zero]

end AlgebraicGeometry.Etale
