# Exact-K0 constituent exchange calculation

Author: Worker 1344.

`signedAlternatingOperator` is the integer-linear map `(-1)^|J| D_G` on the
actual exact K0 group. Its supporting elementary lemmas prove the additive calculation used in Aubert 1995,
Corollary 1.10(b), printed p.2183. It does not yet prove the exact rational-point
target. The actual rank-one sequence, proper Jacquet vanishing, full-subset
identity term and induced Weyl class comparison remain to be supplied by their
applicable proofs. No arbitrary subgroup-family identity is asserted.

The implemented argument first applies exact short-sequence additivity in either
orientation of `HasTwoConstituents`. A categorical zero object has zero class,
as follows directly from its zero self-sequence. The actual Jacquet generator
formula and that zero-class lemma remove every proper subset other than the
chosen maximal subset. An actual Jacquet isomorphism identifies its induced
term. The full subset is retained explicitly. Maximality gives cardinalities
differing by one, so multiplication by `(-1)^|J|` changes the full-term sign to
minus one and the proper-term sign to plus one. The short exact sequence then
replaces the induced class by the sum of the two constituent classes.

The direct mathematical dependencies are `HasTwoConstituents`,
`IsMaximalStandard`, `alternatingOperator`, `alternatingTerm`,
`jacquetK0_ofRepresentation`, `inductionK0_ofRepresentation`,
`FiniteLengthGrothendieckGroup.ofRepresentation_shortExact` and
`FiniteLengthGrothendieckGroup.ofObject_eq_of_iso`. The quotient is the actual
finite-length exact K0 group, with nonsplit short exact sequences included.
No Langlands classification, character independence, geometric lemma,
adjointness or cuspidal-support theorem is used by this additive calculation.
These may be necessary to discharge the remaining representation inputs.

The final helper `constituentExchange_of_jacquet_pattern` derives both actual
class exchanges from `RankOneJacquetPattern`, `HasTwoConstituents`, the explicit
full-term equality on each constituent, and `inducedClassWeylConjugacy`. For the
minus constituent it applies the latter predicate to the inverse normalizer lift
and uses the published continuous-equivalence pullback finite-length theorem.
The arguments are conditional inputs to this internal calculation, not published
proofs of those representation-theoretic predicates. Its direct dependencies
add `pullbackFunctor_preservesFiniteLength` and `conjugationEquiv`; there is no
transitive application of a classification, geometric-lemma, character,
adjointness or support theorem in the implementation.

The source locator is registered `aubert-1995-duality`, printed p.2183,
Corollary 1.10(b) and its proof (read directly). The source is motivation for
this derived additive construction. It is not used to assume its missing
representation-theoretic inputs; Proposition 3.2 and the irreducibility
argument affected by the erratum are unused.
