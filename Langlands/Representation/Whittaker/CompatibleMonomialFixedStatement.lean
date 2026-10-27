import Langlands.Group.GL.UpperBruhatCells
import Langlands.Representation.Whittaker.Distribution

/-!
# Compatible monomial representatives are fixed by Weyl-conjugated transpose

The monomial specialization of Shalika (1974), property (1.5), to canonical p-adic
fields and the standard all-ones character. This module defines an unproved
proposition.
-/

namespace Langlands.Whittaker

universe uF

/-- If the monomial matrix `s = permutation w * diagonalUnits d` carries the standard
character to itself on the common upper-unipotent domain, then `s` is fixed by the
Weyl-conjugated transpose. -/
def CompatibleMonomialFixedStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalNormedField
    ∀ (n : ℕ) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
      (w : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → F.Carrierˣ),
      let s := GeneralLinear.permutation (n + 1) F.Carrier w *
        GeneralLinear.Iwasawa.diagonalUnits d
      (∀ u v : GeneralLinear.upperUnipotent (n + 1) F.Carrier,
        s * u.val * s⁻¹ = v.val →
          standardCharacter ψ n u = standardCharacter ψ n v) →
      weylTransposeHomeomorph n F.Carrier s = s

end Langlands.Whittaker
