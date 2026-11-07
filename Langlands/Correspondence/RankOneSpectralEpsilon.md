# Full rank-one arithmetic pair epsilon in the abelian spectral convention

Worker 1555 derives these internal rewrites from the existing full arithmetic
rank-one epsilon formula on the original base field and the normalized
character-twist comparison in `Abelian.NormalizedTwist`.

`conditionalPairEpsilonValue_eq_abelianSpectral` identifies the full
arithmetic pair epsilon value with the actual fixed-Haar abelian spectral
epsilon expression for the product of the two original quasicharacters.
The spectral parameter is unchanged. Its input measure is the actual
bottom-field regular additive Haar measure transported back to the original
field. The proof rewrites the previously established formula on the base
field, then uses the equality between twisting the character by the
normalized absolute-value power and evaluating the spectral epsilon at
that parameter.

The input pairs are every continuous actual bottom-field restriction of
the specified rank-one irreducible Weil quotient classes. The supplied
compatible reciprocity data, validated common-closure local-constant system,
original nontrivial unitary additive character, every compatible bottom-field
character, arbitrary actual Haar measure and geometric Frobenius remain
explicit. The equality includes the full invariant-quotient determinant
correction already handled by the preceding formula.

`isArithmeticPairEpsilonFactor_rankOne_spectral_iff` applies the same identity
under the exact arithmetic certificate's quantifiers. Its right side retains
existence of an original-field self-dual regular additive Haar measure,
existence of a bottom-field geometric Frobenius, and the epsilon-monomial
identity for every such original-field self-dual measure and every complex
parameter. The epsilon monomial uses the original base residue cardinality,
the given coefficient in complex units and the given integer exponent.

The prime and base field are arbitrary. The field universe, parameter-carrier
universe and supplied-system universe are independent. This is an equality
with the constructed abelian spectral expression; no JPSS functional equation,
analytic epsilon comparison, reciprocity or system existence, measure
existence, Gauss nonvanishing, monomial constants or closed supercuspidal
correspondence is proved.
