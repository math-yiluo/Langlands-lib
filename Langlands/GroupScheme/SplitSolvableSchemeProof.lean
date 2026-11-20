import Langlands.GroupScheme.SplitSolvableCanonicalExtension
import Langlands.GroupScheme.SplitSolvableSchemeFromCanonical

/-! # Proof of Milne 16.56: a split solvable group is affine space times a split torus -/

universe u

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 16.56 (first sentence): the underlying scheme of a split solvable group
`G` over a field is `𝔸^r × G_m^m`, where `U ≅ 𝔸^r` and `D ≅ G_m^m` are the parts of its canonical
extension. -/
theorem splitSolvableSchemeProductStatement : SplitSolvableSchemeProductStatement.{u} :=
  SplitSolvableScheme.splitSolvableSchemeProduct_of_split fun _ _ _ _ _ i q hG hi hU hq hD =>
    SplitSolvableCanonical.canonicalExtension_split hG i q hi hU hq hD

end Langlands.GroupScheme
