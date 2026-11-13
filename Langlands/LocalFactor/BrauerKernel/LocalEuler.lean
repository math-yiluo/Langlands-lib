import Langlands.Global.Factors.RelativeWeilLocalEulerBridge

/-! # Tate L-factors of a local relation among induced characters -/

noncomputable section

set_option autoImplicit false

universe u w

namespace Langlands.Weil.Local.InertiaEuler

open Correspondence VirtualRepresentation VirtualRepresentation.ExactGrothendieckGroup

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance brauerEulerTopology (K : PadicField.{u} p) : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

/-- The formal L-factors of a vanishing combination of induced character differences
multiply to `1`. -/
theorem prod_inducedLFactor_eq_one_of_relation {J : Type*} [Fintype J]
    (E : J → PadicField.{u} p) (g : ∀ j, F.Carrier →ₐ[Padic p] (E j).Carrier)
    (α β : ∀ j, localWeilGroup (E j) →ₜ* ℂˣ) (n : J → ℤ)
    (h : ∑ j, n j • ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F (E j) (g j))
        (extensionWeilMap_isOpenEmbedding F (E j) (g j))
        (characterClass.{u, w} (α j) - characterClass.{u, w} (β j)) = 0) :
    ∏ j, (inducedLFactor F (E j) (g j) (α j) / inducedLFactor F (E j) (g j) (β j)) ^ n j = 1 := by
  have hL := congrArg (fun x => Additive.toMul (lFactorHom.{u, max u w} F x)) h
  simp only [map_zero, map_sum, map_zsmul, map_sub,
    lFactorHom_continuousInduceAlong_characterClass, toMul_zero, toMul_sum, toMul_zsmul,
    toMul_sub, toMul_ofMul] at hL
  have hc := congrArg (fun x : (RatFunc ℂ)ˣ => (x : RatFunc ℂ)) hL
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_div_eq_div_val,
    coe_lFactorUnit_induceAlong_characterLine, Units.val_one] at hc
  exact hc

/-- **Tate L-factors of a local relation.** Suppose that, in the continuous exact virtual
group of `W_F`, `Σ_j n_j Ind_{E_j/F}([η_j ∘ e_j] - [η'_j ∘ e_j]) = 0`, with geometric
reciprocity candidates `e_j` of the extensions `E_j`. Then at every `s` where the Tate
L-factors involved are nonzero, `Π_j (L(s, η_j) / L(s, η'_j))^{n_j} = 1`. -/
theorem prod_lFactor_eq_one_of_relation {J : Type*} [Fintype J]
    (E : J → PadicField.{u} p) (g : ∀ j, F.Carrier →ₐ[Padic p] (E j).Carrier)
    {e : ∀ j, LocalFactor.RankOne.ReciprocityCandidate (E j)}
    (he : ∀ j, IsGeometricReciprocity (E j) (e j))
    (η η' : ∀ j, QuasiCharacter (E j)) (n : J → ℤ)
    (h : ∑ j, n j • ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F (E j) (g j))
        (extensionWeilMap_isOpenEmbedding F (E j) (g j))
        (characterClass.{u, w} (LocalFactor.RankOne.weilCharacter (E j) (e j) (η j)) -
          characterClass.{u, w} (LocalFactor.RankOne.weilCharacter (E j) (e j) (η' j))) = 0)
    (s : ℂ)
    (hs : ∀ j, LocalFactor.PadicAbelian.lFactor (E j).canonicalTopologicalData (η j) s ≠ 0)
    (hs' : ∀ j, LocalFactor.PadicAbelian.lFactor (E j).canonicalTopologicalData (η' j) s ≠ 0) :
    ∏ j, (LocalFactor.PadicAbelian.lFactor (E j).canonicalTopologicalData (η j) s /
      LocalFactor.PadicAbelian.lFactor (E j).canonicalTopologicalData (η' j) s) ^ n j = 1 := by
  have hrel := prod_inducedLFactor_eq_one_of_relation.{u, w} F E g _ _ n h
  set x := RankinSelberg.spectralPoint F.canonicalTopologicalData.residueCardinality s
  have hr : ∀ j, IsRegularUnitAt x
      (inducedLFactor F (E j) (g j) (LocalFactor.RankOne.weilCharacter (E j) (e j) (η j))) :=
    fun j => isRegularUnitAt_inducedLFactor_weilCharacter (E j) (g j) (he j) (η j) (hs j)
  have hr' : ∀ j, IsRegularUnitAt x
      (inducedLFactor F (E j) (g j) (LocalFactor.RankOne.weilCharacter (E j) (e j) (η' j))) :=
    fun j => isRegularUnitAt_inducedLFactor_weilCharacter (E j) (g j) (he j) (η' j) (hs' j)
  have hq : ∀ j ∈ (Finset.univ : Finset J), IsRegularUnitAt x
      ((inducedLFactor F (E j) (g j) (LocalFactor.RankOne.weilCharacter (E j) (e j) (η j)) /
        inducedLFactor F (E j) (g j) (LocalFactor.RankOne.weilCharacter (E j) (e j) (η' j))) ^
          n j) :=
    fun j _ => ((hr j).div (hr' j)).zpow (n j)
  have hev := congrArg (RatFunc.eval (RingHom.id ℂ) x) hrel
  rw [IsRegularUnitAt.eval_prod Finset.univ hq, IsRegularUnitAt.eval_one] at hev
  refine Eq.trans (Finset.prod_congr rfl fun j _ => ?_) hev
  rw [((hr j).div (hr' j)).eval_zpow, (hr j).eval_div (hr' j),
    eval_inducedLFactor_weilCharacter (E j) (g j) (he j) (η j) (hs j),
    eval_inducedLFactor_weilCharacter (E j) (g j) (he j) (η' j) (hs' j)]

end Langlands.Weil.Local.InertiaEuler
