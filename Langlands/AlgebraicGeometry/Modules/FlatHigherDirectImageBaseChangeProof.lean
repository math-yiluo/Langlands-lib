import Langlands.AlgebraicGeometry.Modules.FlatHigherDirectImageBaseChangeStatement
import Langlands.AlgebraicGeometry.Modules.FlatBaseChange.Gluing

/-!
# Proof: flat base change for higher direct images

For a cartesian square `g' ≫ f = f' ≫ g` with `f` quasi-compact and separated and `g` flat, and a
quasi-coherent `M`, the base change transformation of higher direct images
`higherDirectImageBaseChangeNatTrans g f f' g' w n` is an isomorphism at `M`
(`FlatBaseChange.isIso_higherDirectImageBaseChange`); `asIso` of this component is the required
isomorphism `g^* Rⁿ f_* M ≅ Rⁿ f'_* g'^* M`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- **Flat base change for higher direct images** (Stacks Project, tag 02KH, existence part, for
quasi-compact separated `f`). -/
theorem flatHigherDirectImageBaseChange : FlatHigherDirectImageBaseChangeStatement.{u} := by
  intro X Y X' Y' f g f' g' h _ _ _ M _ n
  have : Flat g' := MorphismProperty.of_isPullback h.flip inferInstance
  have : PreservesFiniteLimits (Scheme.Modules.pullback g) := flatPullbackExact Y' Y g inferInstance
  have : PreservesFiniteLimits (Scheme.Modules.pullback g') :=
    flatPullbackExact X' X g' inferInstance
  have := FlatBaseChange.isIso_higherDirectImageBaseChange f g f' g' h M n
  exact ⟨asIso ((DerivedSections.higherDirectImageBaseChangeNatTrans g f f' g' h.w n).app M)⟩

end Langlands.AlgebraicGeometry.Modules
