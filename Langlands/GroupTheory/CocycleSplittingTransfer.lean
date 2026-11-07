import Langlands.GroupTheory.CocycleExtensionTransfer
import Langlands.GroupTheory.CocycleSplittingAbelianization
import Langlands.GroupTheory.CocycleSplittingInvariants

noncomputable section

universe u

namespace Langlands.NormalizedTwoCocycle.SplittingModule

set_option backward.isDefEq.respectTransparency false

attribute [-instance] ULift.module

variable {G A : Type u} [Group G] [Fintype G] [CommGroup A]
  [MulDistribMulAction G A] (c : NormalizedTwoCocycle G A)

local instance transferCoefficientModule : Module Scalars.{u} (Additive A) := ULift.module

local instance transferActionModule :
    Module Scalars.{u} (Rep.ofMulDistribMulAction G A) := ULift.module

/-- The splitting-module norm evaluated on the actual cocycle extension. -/
def normOnExtension :
    c.Extension →* Multiplicative (coefficientRepresentation G A).ρ.invariants where
  toFun x := Multiplicative.ofAdd (splittingNorm c (extensionCoinvariant c x))
  map_one' := by
    change splittingNorm c (extensionCoinvariant c 1) = 0
    rw [extensionCoinvariant_one, map_zero]
  map_mul' x y := by
    change splittingNorm c (extensionCoinvariant c (x * y)) =
      splittingNorm c (extensionCoinvariant c x) +
        splittingNorm c (extensionCoinvariant c y)
    rw [extensionCoinvariant_mul, map_add]

/-- The actual splitting norm is Mathlib's actual transfer, in additive form. -/
lemma splittingNorm_extensionCoinvariant_val (x : c.Extension) :
    (show Additive A from (splittingNorm c (extensionCoinvariant c x)).val) =
      Additive.ofMul
        (MonoidHom.transfer (ExtensionTransfer.coefficientSubgroupEquiv c).toMonoidHom x) := by
  rw [ExtensionTransfer.transfer_eq_prod]
  change ((splitting c).ρ.norm
    ((Additive.ofMul x.left, augmentationCocycle x.right) :
      Carrier (G := G) (A := A))).1 = _
  change (LinearMap.fst Scalars.{u} (Additive A) (Ideal G))
    ((∑ g : G, (splitting c).ρ g)
      ((Additive.ofMul x.left, augmentationCocycle x.right) :
        Carrier (G := G) (A := A))) = _
  rw [LinearMap.sum_apply, map_sum, ofMul_prod]
  apply Finset.sum_congr rfl
  intro g _
  change coefficientAction g (Additive.ofMul x.left) +
    twist c g (augmentationCocycle x.right).val =
    Additive.ofMul ((g • x.left) * c (g, x.right))
  rw [twist_augmentationCocycle]
  rfl

/-- The same comparison with the coefficient group written multiplicatively. -/
lemma splittingNorm_extensionCoinvariant_toMul (x : c.Extension) :
    (show Additive A from (splittingNorm c (extensionCoinvariant c x)).val).toMul =
      MonoidHom.transfer (ExtensionTransfer.coefficientSubgroupEquiv c).toMonoidHom x :=
  congrArg Additive.toMul (splittingNorm_extensionCoinvariant_val c x)

end Langlands.NormalizedTwoCocycle.SplittingModule
