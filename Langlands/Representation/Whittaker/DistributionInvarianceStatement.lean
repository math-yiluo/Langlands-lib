import Langlands.Representation.Whittaker.Distribution

/-!
# Shalika invariance of Whittaker bi-equivariant distributions

The nonarchimedean distribution assertion of Shalika (1974), Theorem 1.6,
specialized to canonical p-adic fields and the standard all-ones character.
This module defines an unproved proposition.
-/

namespace Langlands.Whittaker

universe uF

/-- Every standard Whittaker bi-equivariant distribution on a positive-rank
p-adic general linear group is fixed by Weyl-conjugated transpose. -/
def ShalikaDistributionInvarianceStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalNormedField
    ∀ (n : ℕ) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
      (D : HarmonicAnalysis.Distribution (GeneralLinear (n + 1) F.Carrier)),
      IsBiEquivariantDistribution ψ n D →
      IsWeylTransposeInvariant n F.Carrier D

end Langlands.Whittaker
