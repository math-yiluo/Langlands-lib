# Actual integral Jacquet words of cuspidal-product constituents

Author: Worker 320.

`Langlands.Classification.IntegralCuspidalConstituentWord F T` states that
every irreducible actual smooth constituent of a normalized product of
supercuspidal representations on a fixed integral twist line has an actual
integral cuspidal Jacquet word that permutes the original list of integer
labels. Repeated labels and their multiplicities are retained.

The parameters preserve every prime, actual p-adic field and supplied
topological datum, independent field and carrier universes, and saturated
carriers in `Type (max uF uV)`. The total rank is positive. The factors and
the constituent are actual smooth complex representations. Equality of
rank-indexed supercuspidal classes records the original labels, including
dependent transport between ranks. The input is the actual
`SmoothRep.IsSubquotient` relation for the normalized upper product
induction, with positive half-modulus covariance and right translation.
The output uses the existing actual Jacquet-word predicate, rather than
an equality in a Grothendieck group.

This is an internal derived interface. Its rationale is the combination of
supercuspidal embedding and uniqueness of support, whose source is
Zelevinsky 1980, Proposition 1.10, printed p.174 (PDF p.11), registered as
`zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
with first adjointness and elementary list permutation. An embedding
gives a nonzero Jacquet map onto the
irreducible tensor of its supercuspidal factors. Uniqueness of support
identifies the multiset of these factors with that of the original
product. Lifting the resulting permutation through the integer-label map
gives the output word. This argument does not require the label map to be
injective.

The proposition does not construct the initial integral twist line of an
analytic square-integrable representation, assert closure of Jacquet words
under arbitrary permutations, or extract a segment. Its mathematical proof
is a separate obligation.
