import Langlands.GroupScheme.PseudoCompleteDomination
import Langlands.CommutativeAlgebra.DVRAlgebraicBaseChange
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Descent of the DVR lifting property along algebraic field extensions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open Langlands.CommutativeAlgebra.DVRAlgebraicBaseChange

namespace Langlands.GroupScheme.PseudoComplete

/-- Let `L/k` be an algebraic extension. If the base change of `X` to `L` has the DVR lifting
property over `L`, then `X` has the DVR lifting property over `k`. -/
theorem hasDVRLifting_of_baseChange (k L : Type u) [Field k] [Field L] [Algebra k L]
    [Algebra.IsAlgebraic k L] (X : Over (Spec (CommRingCat.of k)))
    (h : HasDVRLifting (k := L)
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj X)) :
    HasDVRLifting X := by
  intro R _ _ _ _ hred x
  have : Algebra.IsGeometricallyReduced k (ResidueField R) := hred
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, hm, htm⟩ := exists_isPrime_tmul_mem k L R hϖ
  have : IsDomain (Localization.AtPrime m) := isDomain_localization k L R m hϖ htm
  have : IsDiscreteValuationRing (Localization.AtPrime m) :=
    isDiscreteValuationRing_localization k L R m hϖ htm
  have hred' := isGeometricallyReduced_residueField k L R m hϖ htm
  let f : R →+* Localization.AtPrime m := toLocalization k L R m
  have hf : Function.Injective f := toLocalization_injective k L R m hϖ
  have : IsLocalHom f := by
    have := isLocalHom_toLocalization k L R m hϖ htm
    exact isLocalHom_toRingHom _
  let b := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let a : Spec (CommRingCat.of (FractionRing (Localization.AtPrime m))) ⟶ X.left :=
    Spec.map (CommRingCat.ofHom (fractionRingMap f hf)) ≫ x.left
  have hw : x.left ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (FractionRing R))) := Over.w x
  have cond : a ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap L (FractionRing (Localization.AtPrime m)))) ≫ b := by
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hw).trans
      ((Spec.map_comp _ _).symm.trans ?_))
    rw [← Spec.map_comp]
    congr 1
    ext c
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply]
    rw [IsScalarTower.algebraMap_apply k R (FractionRing R), fractionRingMap_algebraMap,
      IsScalarTower.algebraMap_apply L (Localization.AtPrime m)]
    congr 1
    rw [← IsScalarTower.algebraMap_apply k L (Localization.AtPrime m)]
    exact (toLocalization k L R m).commutes c
  let xL : algebraSpec L (FractionRing (Localization.AtPrime m)) ⟶
      (Over.pullback b).obj X :=
    Over.homMk (pullback.lift a _ cond) (pullback.lift_snd _ _ _)
  obtain ⟨yL, hyL⟩ := h (Localization.AtPrime m) hred' xL
  have h2 : Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.AtPrime m) (FractionRing (Localization.AtPrime m)))) ≫ yL.left =
      pullback.lift a _ cond := congr(($hyL).left)
  have hxy : Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.AtPrime m) (FractionRing (Localization.AtPrime m)))) ≫
        (yL.left ≫ pullback.fst X.hom b) =
      Spec.map (CommRingCat.ofHom (fractionRingMap f hf)) ≫ x.left :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ pullback.fst X.hom b) h2).trans (pullback.lift_fst _ _ _))
  obtain ⟨z, hz⟩ := exists_comp_eq_of_dominates f hf x.left _ hxy
  exact exists_extension_of_comp_eq X R x z hz

end Langlands.GroupScheme.PseudoComplete
