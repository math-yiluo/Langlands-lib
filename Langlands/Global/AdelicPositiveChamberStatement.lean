import Langlands.Global.AdelicEisensteinConvergenceStatement

/-! # The positive chamber of a parabolic is nonempty

There is a parameter `λ ∈ X^*(P) ⊗ ℂ` whose real part, restricted to the split component `A`,
pairs positively under the presentation's form `B` with every root of `A` in the unipotent
radical: the positive Weyl chamber of `𝔞_P^*`, in which Bernstein–Lapid (§2.2) take `Re λ`
sufficiently regular, is nonempty. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- The positive chamber of a parabolic is nonempty. Let `G` be a connected reductive group
over a number field and `p : P → G` a parabolic with rational Levi `l : M → P`, presented
through the split component `a : A → M` by `r`. Then some `λ ∈ X^*(P) ⊗ ℂ` is `0`-regular:
`0 < B(Re λ|_A, α)` for every root `α` of `A` in the unipotent radical of `P`, where `B` is the
Weyl-induced positive form of the presentation. -/
def PositiveChamberNonemptyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    IsConnectedReductive G →
    ∃ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT 0 lam

end Langlands.Global
