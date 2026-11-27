import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.AdelicLogSection
import Langlands.Global.RelativeRootChamber

/-! # The half modulus of a standard parabolic on its positive split component

For a standard parabolic `P_J = M_J U_J` with split component `A_J`, the modulus
`δ_{P_J}(a) = |det(Ad(a) | Lie P_J)|` at a positive real point `a` of `A_J` is the product
`∏_{β ∈ Φ⁺} |β(a)|^{m_β}` over the positive relative roots, with `m_β` the dimension of the
`β`-weight space of the maximal split torus on the Lie algebra of `G`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- **The half modulus of a standard parabolic on its positive split component.** Let `𝓕` be a
standard parabolic family of `G`, `J` a standard index and `s` a positive real point of the
split component `A_J`, with image `a` in `P_J(𝔸)`. Then
`|a^{ρ_J}|² = δ_{P_J}(a) = ∏_{β ∈ Φ⁺} |β(s)|^{m_β}`, where `Φ⁺ = positiveRelativeRoots`,
`β(s)` is the value at `s` of the restriction of `β` along `A_J → T`, `|·|` is the idele norm
and `m_β = finrank F (weightSpace 𝓕.i β)`. -/
def HalfModulusRootProductStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (𝓕 : StandardParabolicFamily F G) (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (s : PositiveRealTorus.intrinsicSubgroup F (𝓕.A J)),
    ‖𝓕.halfModulus J
        (PositiveRealTorus.positivePointMap F (𝓕.P J) (𝓕.A J) (𝓕.a J ≫ 𝓕.l J) s)‖ ^ 2 =
      ∏ᶠ (β : characterLattice 𝓕.T) (_ : β ∈ positiveRelativeRoots 𝓕.i 𝓕.ν),
        ((PositiveRealTorus.normCharacter F (𝓕.A J) (𝓕.f J ≫ β) s : ℝ≥0) : ℝ) ^
          Module.finrank F (weightSpace 𝓕.i β)

end Langlands.Global
