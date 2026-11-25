/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRealizationDataSupplement
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantModuleModel
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantResolutionTensorCalculation
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantDerivedTensorTower
import WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.FiniteFreeResolution
import WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Single
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Homology.FullSubcategory
/-!
# Completed constant realization of finite complexes
Source: Stacks Project, proetale.tex, Tags 09BT and 09BV; sites-modules.tex,
Tags 093J--093M; algebra.tex, Tag 00MB
(blueprint: lem-weil-pbc-completed-constant-finite-complex-realization).
Positive quotient levels are indexed by `n : ℕ`, with exponent `n + 1`.
The comparison is stated on finite-free resolutions of bounded finite complexes.
Naturality on the category of resolutions includes independence of the resolution.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u v w vD vE
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
private theorem completedConstant_eval_step
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) (n : ℕ) :
    (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 2)).toRingHom) ≫
        CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1)) =
      CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom := by
  ext x
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I A x
  change Ideal.Quotient.factorPowSucc I (n + 1)
    (AdicCompletion.evalₐ I (n + 2) (AdicCompletion.mk I A s)) =
      AdicCompletion.evalₐ I (n + 1) (AdicCompletion.mk I A s)
  simp only [AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk _ (s.val (n + 2)) = Ideal.Quotient.mk _ (s.val (n + 1))
  apply Ideal.Quotient.eq.mpr
  have hs := (Submodule.Quotient.eq _).mp
    (AdicCompletion.AdicCauchySequence.mk_eq_mk (Nat.le_succ (n + 1)) s)
  simpa [smul_eq_mul, Ideal.mul_top] using hs

private theorem completedConstant_scalar_exists
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    ∃ φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I,
      ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
        (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom) := by
  let c := constantSheaf (ProEt.topology X) CommRingCat.{u + 1}
  let π : (Functor.const ℕᵒᵖ).obj (adicLisseConstantRing X (AdicCompletion I A)) ⟶
      adicLisseRingSystem X I := NatTrans.ofOpSequence
    (fun n ↦ c.map (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom))
    (fun n ↦ by
      simp only [Functor.const_obj_map, adicLisseRingSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact (congrArg c.map (completedConstant_eval_step I n)).symm.trans
        (c.map_comp _ _))
  exact ⟨limit.lift _ ⟨_, π⟩, fun n ↦ limit.lift_π _ _⟩

private theorem completedConstant_pullback_iso
    (X T : Scheme.{u}) (f : X ⟶ T) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hfinite : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) :
    ∃ β : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (adicLisseCompletedRing T I) ⟶ adicLisseCompletedRing X I,
      IsIso β ∧ ∀ n : ℕ, β ≫ limit.π (adicLisseRingSystem X I) (op n) =
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (limit.π (adicLisseRingSystem T I) (op n)) ≫
            proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
              (CommRingCat.of (A ⧸ I ^ (n + 1))) := by
  let Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1} := Functor.ofOpSequence
    (X := fun n ↦ CommRingCat.of (A ⧸ I ^ (n + 1)))
    (fun n ↦ CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1)))
  let e (Z : Scheme.{u}) : adicLisseRingSystem Z I ≅ proEtaleCoefficientTower Z Q := by
    let a : adicLisseRingSystem Z I ⟶ proEtaleCoefficientTower Z Q :=
      NatTrans.ofOpSequence (fun n ↦ 𝟙 _) (fun n ↦ by
        simp [adicLisseRingSystem, proEtaleCoefficientTower, Q])
    have (n : ℕᵒᵖ) : IsIso (a.app n) := inferInstanceAs (IsIso (𝟙 _))
    have : IsIso a := NatIso.isIso_of_isIso_app a
    exact asIso a
  have (n : ℕᵒᵖ) : Finite (Q.obj n) := hfinite n.unop
  have : IsIso (proEtaleProfiniteComparison f Q) :=
    (proEtale_profinite_coefficient_inverse_image Q).2.1 X T f
  let F := proEtaleSheafInverseImage f CommRingCat.{u + 1}
  let β := F.map (lim.mapIso (e T)).hom ≫ proEtaleProfiniteComparison f Q ≫
    (lim.mapIso (e X)).inv
  refine ⟨β, inferInstance, ?_⟩
  intro n
  dsimp only [β]
  simp only [Category.assoc, Functor.mapIso_inv]
  change F.map (lim.mapIso (e T)).hom ≫ proEtaleProfiniteComparison f Q ≫
    limMap (e X).inv ≫ limit.π (adicLisseRingSystem X I) (op n) = _
  rw [limMap_π]
  rw [← Category.assoc (proEtaleProfiniteComparison f Q)]
  rw [(proEtale_profinite_coefficient_inverse_image Q).2.2.1 X T f (op n)]
  have hinv : (e X).inv.app (op n) = 𝟙 _ := by
    simp [e]
    rfl
  simp only [hinv, Category.comp_id]
  change F.map (limMap (e T).hom) ≫
    F.map (limit.π (proEtaleCoefficientTower T Q) (op n)) ≫
      proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (A ⧸ I ^ (n + 1))) = _
  rw [← Category.assoc, ← F.map_comp, limMap_π]
  have hhom : (e T).hom.app (op n) = 𝟙 _ := rfl
  rw [hhom, Category.comp_id]

end AlgebraicGeometry.Scheme
