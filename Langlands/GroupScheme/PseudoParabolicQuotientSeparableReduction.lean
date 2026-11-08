import Langlands.GroupScheme.PseudoParabolicQuotientDynamicCase
import Langlands.GroupScheme.PseudoCompleteAlgebraicBaseChange
import Langlands.GroupScheme.Dynamic.QuotientFiberBaseChange
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Reductive.PseudoReductiveSeparableExtensionStatement
import Mathlib.FieldTheory.IsSepClosed

/-! # Reduction of the dynamic case of CGP Proposition C.1.6 to separably closed fields

Assuming that pseudo-reductivity is preserved by separable algebraic field extensions, the DVR
lifting property for quotients by dynamic parabolic subgroups over an arbitrary field follows
from the same property over separably closed fields, by base change to a separable closure.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Base change along a morphism of base schemes preserves the hypotheses on the quotient map in
`DynamicParabolicQuotientDVRLifting`: smoothness, surjectivity, quasi-compactness and the
right-coset fibre criterion for the base-changed dynamic parabolic. -/
theorem dynamicParabolicQuotient_baseChange {S S' : Scheme.{u}} (b : S' ⟶ S)
    {G : GroupScheme S} (χ : (Gm S).toGrp ⟶ G) {Q : Over S} (q : G.X ⟶ Q)
    (hsm : Smooth q.left) (hsurj : Surjective q.left) (hqc : QuasiCompact q.left)
    (hfib : ∀ (T : Over S) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (Dynamic.parabolic χ).carrier T) :
    Smooth ((Over.pullback b).map q).left ∧ Surjective ((Over.pullback b).map q).left ∧
      QuasiCompact ((Over.pullback b).map q).left ∧
      ∀ (T : Over S') (g h : T ⟶ ((GroupScheme.baseChange b).obj G).X),
        g ≫ (Over.pullback b).map q = h ≫ (Over.pullback b).map q ↔
          g⁻¹ * h ∈ (Dynamic.parabolic (Dynamic.baseChangeCocharacter b χ)).carrier T :=
  ⟨MorphismProperty.overPullbackMap (P := @Smooth) b q hsm,
    MorphismProperty.overPullbackMap (P := @Surjective) b q hsurj,
    MorphismProperty.overPullbackMap (P := @QuasiCompact) b q hqc,
    dynamicParabolicQuotient_fiber_baseChange b χ q hfib⟩

/-- If pseudo-reductivity is preserved by separable algebraic field extensions (`hsep`), then the
DVR lifting property for quotients by dynamic parabolic subgroups over separably closed fields
implies it over every field. -/
theorem dynamicParabolicQuotientDVRLifting_of_isSepClosed
    (hsep : PseudoReductiveSeparableExtensionStatement.{u})
    (hsc : ∀ (k : Type u) [Field k] [IsSepClosed k], DynamicParabolicQuotientDVRLifting k)
    (k : Type u) [Field k] : DynamicParabolicQuotientDVRLifting k := by
  intro G χ Q q hG hsm hsurj hqc hfib
  let b := Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k)))
  obtain ⟨hsm', hsurj', hqc', hfib'⟩ := dynamicParabolicQuotient_baseChange b χ q hsm hsurj hqc hfib
  exact PseudoComplete.hasDVRLifting_of_baseChange k (SeparableClosure k) Q
    (hsc (SeparableClosure k) ((GroupScheme.baseChange b).obj G)
      (Dynamic.baseChangeCocharacter b χ) ((Over.pullback b).obj Q) ((Over.pullback b).map q)
      (hsep k (SeparableClosure k) G hG) hsm' hsurj' hqc' hfib')

end Langlands.GroupScheme
