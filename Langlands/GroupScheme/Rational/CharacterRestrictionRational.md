# Rational scalar extension of integral character restriction

Author: Worker 1321.

This internal adapter applies `RationalSpan.rationalizationEquiv` to the actual
group-scheme Hom-lattice map `characterRestrict`. Given injectivity of that
integral map and finite index of its image, it proves bijectivity of the existing
map `rationalCharacterRestrictRat`. For a morphism from a commutative group scheme
`A`, it constructs `rationalCharacterRestrictRatEquiv` with precisely that forward
map and concludes `rationalCharacterRank G = splitTorusRank A`.

The target rational characters of `A.toGrp` and the character lattice of `A` are
definitionally the same abelian group in the existing Library. Thus no
identification of integral lattices is asserted or chosen as an extra input.
The rational linear equivalence is derived from the integral restriction facts.

The final three helper theorems consume the existing
`CharacterRestrictionStatement.{u}` and obtain rational bijectivity and the rank
identity for every actual split component of a connected reductive group over
any field in universe `u`. They are conditional adapters: this module does not
prove `CharacterRestrictionStatement`, which is the separate geometric
restriction task, and does not prove `RelativeRankIdentityStatement`.
`rationalCharacterRestrictRat_consequences_of_characterRestriction` packages
the two conclusions as a conjunction.

The provenance is internal. The implementation unfolds the already published
scalar-extension definition and invokes the general finite-index rationalization
proof in `Langlands.LinearAlgebra.RationalFiniteIndex`. The rank equality follows
from the resulting rational linear equivalence. Finite dimensionality is neither
assumed nor concluded here; the natural-number finrank equality is valid even
without it and must be supplemented by the finiteness results in the full
relative-rank theorem.
