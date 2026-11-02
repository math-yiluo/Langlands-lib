import Langlands.AlgebraicGeometry.Picard.LineBundleHigherProjectionFormulaStatement
import Langlands.AlgebraicGeometry.Picard.LineBundleProjectionFormulaProof

/-! # Proof of the projection formula for higher direct images and an actual line bundle -/

noncomputable section

universe u v u' v'

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- The higher projection isomorphism `L ⊗ Rⁿ f_* M ≅ Rⁿ f_* (f^* L ⊗ M)` for an actual line
bundle `L`, obtained by deriving the degree-zero projection isomorphism along the exact
autoequivalences `L ⊗ -` and `f^* L ⊗ -`. -/
def lineBundleHigherProjectionIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : LineBundle Y) (M : X.Modules) (n : ℕ) :
    Langlands.Scheme.Modules.tensorObj L.obj ((higherDirectImage f n).obj M) ≅
      (higherDirectImage f n).obj
        (Langlands.Scheme.Modules.tensorObj ((Scheme.Modules.pullback f).obj L.obj) M) := by
  let h := locallyFreeRankOneTensorInvertible Y L.obj L.property
  let N := h.choose
  let e : L.obj ⊗ N ≅ 𝟙_ Y.Modules := h.choose_spec.some
  let F := Scheme.Modules.pullback f
  let eX : F.obj L.obj ⊗ F.obj N ≅ 𝟙_ X.Modules :=
    Functor.Monoidal.μIso F L.obj N ≪≫ F.mapIso e ≪≫ (Functor.Monoidal.εIso F).symm
  let EY := tensorLeftEquivalenceOfInverse L.obj N e
  let EX := tensorLeftEquivalenceOfInverse (F.obj L.obj) (F.obj N) eX
  have : (tensorLeft L.obj).IsEquivalence := EY.isEquivalence_inverse
  have : (tensorLeft (F.obj L.obj)).IsEquivalence := EX.isEquivalence_inverse
  have : (tensorLeft L.obj).Additive := Functor.additive_of_preserves_binary_products _
  have : (tensorLeft (F.obj L.obj)).Additive := Functor.additive_of_preserves_binary_products _
  let c := tensorLeftRightAdjointCommIso F (Scheme.Modules.pushforward f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) L.obj N e
  let d := Langlands.Cohomology.DerivedComparison.rightDerivedCompIso
    (Scheme.Modules.pushforward f) (tensorLeft L.obj) (tensorLeft (F.obj L.obj))
    (Scheme.Modules.pushforward f) c n
  exact (localizedTensorIso Y L.obj ((higherDirectImage f n).obj M)).symm ≪≫ d.app M ≪≫
    (higherDirectImage f n).mapIso (localizedTensorIso X (F.obj L.obj) M)

/-- The projection formula for higher direct images holds for every scheme morphism, actual
line bundle, module sheaf and degree. -/
theorem lineBundleHigherProjectionFormula : LineBundleHigherProjectionFormulaStatement.{u} := by
  intro X Y f L M n
  exact ⟨lineBundleHigherProjectionIso f L M n⟩

end Langlands.AlgebraicGeometry.Picard
