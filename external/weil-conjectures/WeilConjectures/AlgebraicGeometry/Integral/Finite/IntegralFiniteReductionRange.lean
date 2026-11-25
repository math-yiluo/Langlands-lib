/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.ModuleObjects.KFlatScalarTower.InternalKFlatScalarTowerRealizationSupplement
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Common bounds and top epimorphisms for integral reductions
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint
attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.finiteModulesDerived
  AdicCompletion.modulesDerived AdicCompletion.modulesProducts AdicCompletion.complexProducts

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

private theorem tensorComparison :
    ∃ e : ∀ n, DerivedNakayama.reductionFunctor l E X (n + 1) ≅
        AdicCompletion.derivedReduction l E X n ⋙ AdicCompletion.restrict l E X n,
      ∀ n K, (DerivedNakayama.reductionMap l E X
        (AdicCompletion.quotientStep l E n)).app K ≫ (e n).hom.app K =
          (e (n + 1)).hom.app K ≫ AdicCompletion.integralStep l E X K n := by
  obtain ⟨e, hs, _⟩ := Mod.KFlatScalarTower.derived_realization
    (AdicCompletion.ring l E X) (AdicCompletion.finiteRing l E X)
    (AdicCompletion.quotient l E X) (AdicCompletion.transition l E X)
    (AdicCompletion.quotient_transition l E X) (AdicCompletion.finiteModule l E X)
    (AdicCompletion.finiteUnit l E X)
    (fun n ↦ (DerivedNakayama.pullback l E X).map (AdicCompletion.quotientStep l E n))
    (fun n ↦ (Functor.mapModComapIso (upperStarFromPoint X)
      (DerivedNakayama.reductionRing l E (n + 1))).app
        (Mod.regular (DerivedNakayama.quotientRing l E (n + 1))))
    (by
      intro n
      change (𝟙 _ ≫ (upperStarFromPoint X).map
        (DerivedNakayama.reductionRing l E (n + 1))) ≫ 𝟙 _ = _
      simp only [Category.id_comp, Category.comp_id])
    (by
      intro n
      change (upperStarFromPoint X).map (AdicCompletion.transitionRing l E n) ≫ 𝟙 _ =
        𝟙 _ ≫ (upperStarFromPoint X).map (AdicCompletion.transitionRing l E n)
      simp only [Category.id_comp, Category.comp_id])
  exact ⟨e, hs⟩

/-- Every canonical finite reduction has the residue cohomological interval, and its top
cohomology transition is epic. -/
theorem integral_finite_reduction_range
    (K : DerivedCategory (AdicCompletion.Modules l E X)) (a b : ℤ)
    (hbound : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((AdicCompletion.derivedReduction l E X 0).obj K))) :
    (∀ n, DerivedCategory.homologyConcentratedIn a b
      (AdicCompletion.integralLevel l E X K n)) ∧
    (∀ n, Epi ((DerivedCategory.homologyFunctor (AdicCompletion.Modules l E X) b).map
      (AdicCompletion.integralStep l E X K n))) := by
  classical
  obtain ⟨e, he⟩ := tensorComparison l E X
  obtain ⟨d, _, r, hr, i, q, _, hq, htri⟩ :=
    DerivedNakayama.derived_nakayama_resolution l E
  let F := DerivedNakayama.pullback l E X
  let H := DerivedCategory.homologyFunctor (AdicCompletion.Modules l E X)
  have hr' (n : ℕ) : r (n + 1) = AdicCompletion.quotientUnit l E n := by
    apply Mod.hom_ext
    exact hr (n + 1)
  have hq' (n : ℕ) : F.map (q 1 (n + 1)) =
      F.map (AdicCompletion.quotientStep l E n) := by
    obtain ⟨hz, hshort⟩ := (htri X (n + 2) (by omega)).1
    have : Epi (F.map (r (n + 2))) := hshort.epi_g
    apply (cancel_epi (F.map (r (n + 2)))).mp
    rw [← F.map_comp, ← F.map_comp]
    calc
      F.map (r (n + 2) ≫ q 1 (n + 1)) = F.map (r (n + 1)) :=
        congrArg F.map (hq 1 (n + 1))
      _ = F.map (r (n + 2) ≫ AdicCompletion.quotientStep l E n) := by
        rw [hr' n, hr' (n + 1)]
        rfl
  have hres (j : ℤ) (hj : j < a ∨ b < j) :
      IsZero ((H j).obj ((DerivedNakayama.reductionFunctor l E X 1).obj K)) := by
    let G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.finiteRing l E X 0) ⥤ AdicCompletion.Modules l E X :=
      Mod.comap (AdicCompletion.quotient l E X 0)
    have hz := ((G.map_isZero (hbound j hj)).of_iso
      ((G.mapDerivedCategoryHomologyFunctorIso j).symm.app
        ((AdicCompletion.derivedReduction l E X 0).obj K)))
    exact hz.of_iso ((H j).mapIso ((e 0).app K))
  have hlevels (n : ℕ) (j : ℤ) (hj : j < a ∨ b < j) :
      IsZero ((H j).obj ((DerivedNakayama.reductionFunctor l E X (n + 1)).obj K)) := by
    induction n with
    | zero => exact hres j hj
    | succ n ih =>
      obtain ⟨δ, hT⟩ := (htri X (n + 1) (by omega)).2.2 1 (by omega) (by omega) K
      exact (DerivedCategory.HomologySequence.exact₂ _ hT j).isZero_of_both_isZero
        (hres j hj) ih
  constructor
  · intro n
    have hz (j : ℤ) (hj : j < a ∨ b < j) :=
      (hlevels n j hj).of_iso ((H j).mapIso ((e n).app K).symm)
    exact ⟨(DerivedCategory.isGE_iff _ a).mpr (fun j hj ↦ hz j (Or.inl hj)),
      (DerivedCategory.isLE_iff _ b).mpr (fun j hj ↦ hz j (Or.inr hj))⟩
  · intro n
    obtain ⟨δ, hT⟩ := (htri X (n + 1) (by omega)).2.2 1 (by omega) (by omega) K
    have hepi : Epi ((H b).map
        ((DerivedNakayama.reductionMap l E X (q 1 (n + 1))).app K)) :=
      (DerivedCategory.HomologySequence.exact₃ _ hT b (b + 1) rfl).epi_f
        ((hres (b + 1) (Or.inr (by omega))).eq_zero_of_tgt _)
    have hmap : (DerivedNakayama.reductionMap l E X (q 1 (n + 1))).app K =
        (DerivedNakayama.reductionMap l E X (AdicCompletion.quotientStep l E n)).app K := by
      unfold DerivedNakayama.reductionMap
      rw [hq']
    rw [hmap] at hepi
    have hcomp := congrArg ((H b).map) (he n K)
    simp only [Functor.map_comp] at hcomp
    have : Epi ((H b).map ((e (n + 1)).hom.app K) ≫
        (H b).map (AdicCompletion.integralStep l E X K n)) := by
      rw [← hcomp]
      infer_instance
    exact epi_of_epi ((H b).map ((e (n + 1)).hom.app K)) _

end AlgebraicGeometry.ProEtale
