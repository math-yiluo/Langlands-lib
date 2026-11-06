import Langlands.GroupScheme.Lie.SemisimpleElement
import Langlands.GroupScheme.Lie.ElementCentralizer
import Langlands.GroupScheme.Torus.Maximal

/-! # Statements: tori centralizing Lie elements that commute with their tangent vectors -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Semisimple Lie elements commuting with the Lie algebra of a maximal torus.** Over an
algebraically closed field `k`, let `j₀ : T₀ ⟶ G` be a maximal torus of a smooth connected
affine group `G`. If a geometrically semisimple Lie element `Y` of `G` has every tangent vector
of `T₀` in its Lie centralizer, then `T₀` centralizes `Y` over every test scheme. -/
def SemisimpleMaximalTorusLieCentralizerStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T₀ : CommGroupScheme (Spec (CommRingCat.of k))) (j₀ : T₀.toGrp ⟶ G),
    IsMaximalTorus j₀ → ∀ Y : lieKernel G k, Lie.IsSemisimpleElement G Y →
      (∀ t : lieKernel T₀.toGrp k,
        Additive.ofMul (Lie.targetMap j₀ k t) ∈ Lie.elementCentralizerLie G Y) →
      SubgroupFunctor.range j₀ ≤ Lie.elementCentralizer G Y

/-- **Tori and Lie centralizers in characteristic zero.** Over a field `k` of characteristic
zero, let `j : T ⟶ G` be a homomorphism from a torus to a smooth affine group. If every tangent
vector of `T` maps into the Lie centralizer of a Lie element `Y` of `G`, then `T` centralizes
`Y` over every test scheme. -/
def CharZeroTorusLieCentralizerStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
    IsTorus T.toGrp → ∀ Y : lieKernel G k,
      (∀ t : lieKernel T.toGrp k,
        Additive.ofMul (Lie.targetMap j k t) ∈ Lie.elementCentralizerLie G Y) →
      SubgroupFunctor.range j ≤ Lie.elementCentralizer G Y

end Langlands.GroupScheme
