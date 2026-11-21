import Langlands.Automorphic.GroupSchemeInfiniteTranslation

/-! # The adjoint action of `G(F_∞)` fixes the center of the enveloping algebra

For a connected reductive group `G` over a number field `F`, every point `g` of the infinite
adelic group `G(F_∞)` acts trivially, through the adjoint automorphism
`adelicEnvelopingConjugation`, on the center of the complex enveloping algebra. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme

/-- `Ad(G(F_∞))` fixes the center `𝔷` of the complex enveloping algebra pointwise, for a
connected reductive group `G` over a number field `F`: for every smooth structure `hsmooth`,
every `g ∈ G(F_∞)` and every central element `z` of `AdelicEnvelopingAlgebra F G hsmooth`,
the adjoint automorphism `adelicEnvelopingConjugation F G hsmooth g` fixes `z`. -/
def AdelicEnvelopingCenterConjugationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom),
    IsConnectedReductive G →
    ∀ (g : InfiniteAdelicGroupPoints F G) (z : AdelicEnvelopingAlgebra F G hsmooth),
      z ∈ AdelicEnvelopingCenter F G hsmooth →
        adelicEnvelopingConjugation F G hsmooth g z = z

end Langlands.Automorphic.GroupSchemeFunctions
