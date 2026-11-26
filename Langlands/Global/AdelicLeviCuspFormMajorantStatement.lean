import Langlands.Global.AdelicLeviConstantTermPairing
import Langlands.Global.AdelicIwasawaStatement

/-! # Weighted majorants of cusp forms on standard Levi subgroups

The integrability hypothesis `HasLeviPairingMajorant` of the continuous Levi pairings
`StandardParabolicFamily.constantTermLeviPairingCLM`, asserted for every cusp form on every
standard Levi subgroup, every adelic point and every growth exponent, when the maximal compact
subgroup is in good position (Mœglin–Waldspurger I.2.18). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Weighted majorants of cusp forms on standard Levi subgroups (Mœglin–Waldspurger I.2.18,
rapid decay of cusp forms). Let `𝓕` be a standard parabolic family of a connected reductive
group `G` over a number field and `K` a maximal compact subgroup of `G(𝔸)` with
`P₀(𝔸)K = G(𝔸)` for the minimal standard parabolic `P₀` and with `K ∩ M_J(𝔸)` maximal compact
in every standard Levi `M_J(𝔸)`. For every closed matrix embedding `rho`, every cusp form `ψ`
on `M_J(F) \ M_J(𝔸)`, every `g ∈ G(𝔸)` and every real `R`, the function
`m ↦ ‖ι(m) g‖^R |ψ(m)|` on `M_J(F) \ M_J(𝔸)^1`, evaluated at suitable representatives, has an
integrable majorant (`HasLeviPairingMajorant`). -/
def LeviCuspFormPairingMajorantStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (𝓕 : StandardParabolicFamily F G) (K : Subgroup (AdelicGroupPoints F G)),
    IsMaximalCompactSubgroup F G K →
    IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K →
    (∀ J : StandardIndex F G 𝓕.i 𝓕.ν, IsMaximalCompactSubgroup F (𝓕.M J)
      (K.comap (AdelicGroupPoints.map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).toMonoidHom)) →
    ∀ {N : ℕ} (rho : MatrixRepresentation G (Fin N)), IsClosedSubgroup rho →
    ∀ (J : StandardIndex F G 𝓕.i 𝓕.ν) (ψ : AdelicGroupPoints F (𝓕.M J) → ℂ),
      𝓕.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J ψ →
      ∀ (g : AdelicGroupPoints F G) (R : ℝ), 𝓕.HasLeviPairingMajorant J ψ g rho R

end Langlands.Global
