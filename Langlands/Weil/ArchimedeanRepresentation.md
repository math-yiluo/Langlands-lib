# Concrete archimedean Weil representations

Author: Worker 2. Namespace: `Langlands.Weil.Archimedean`. This pair uses the
published actual archimedean Weil groups and the published
`Langlands.FiniteRepresentation` carrier. It supplies concrete representations;
independent review is required for acceptance.

For a continuous complex quasi-character, `complexCharacter` is the existing
scalar character representation on the actual complex line, with its continuity
proved in the canonical complex module topology on endomorphisms.
`realCharacter` pulls a continuous character of real units back along the
constructed real abelian coordinate. Both have rank one. The formulas at complex
elements and at `j` are explicit. Identification of the abelian coordinate with
reciprocity is not assumed.

For a continuous character `chi` of the complex Weil subgroup, `inducedFunctions`
is the actual submodule of functions on the real Weil group satisfying
`f(z w) = chi(z) f(w)`. `inductionRightAction` is right translation on that
space, with preservation and representation laws proved. Evaluation at `1,j`
gives the linear equivalence `inductionCoordinates` with `Complex × Complex`.
Its inverse sends `(a,b)` to the function with value `chi(z)*a` at `z` and
`chi(z)*b` at `z j`. Thus all these functions are continuous. Since the subgroup
has two cosets, no support condition restricts this induction space.

`twoDimensionalAction` transports this actual action through the coordinate
equivalence. `inductionEquiv` records the intertwining equivalence. On the
complex subgroup the matrices are diagonal with entries `chi(z),chi(conj z)`;
on `j` the matrix is `[[0,1],[chi(-1),0]]`. In particular its square is the
scalar `chi(-1)`, in agreement with the nonsplit real Weil group. This is a
concrete induced realization, without a classification or irreducibility
assumption. `twoDimensionalAction_j_twice` also verifies the scalar square
directly. `conjugateCharacter` is pullback by complex conjugation, and
`twoDimensionalAction_restrict` identifies restriction with the existing
`Representation.prod` of the two scalar character actions.

`twoDimensionalAction_isContinuous` proves continuity into the canonical complex
module topology on the four-dimensional endomorphism space. On each clopen
parity fiber the action is a fixed complex-linear function of the two continuous
coefficient functions `chi(z)` and `chi(conj z)`. The coefficient-to-endomorphism
linear maps are continuous for the module topology. The two fibers are then
combined using their clopenness. `realInducedCharacter` packages this action in
the existing `FiniteRepresentation.ContinuousObjects RealWeil` and
`realInducedCharacter_rank` proves its rank is exactly two.

The one-dimensional continuity proof similarly uses the linear map from a
complex scalar to its scalar endomorphism. These are construction proofs, not
assumed continuity fields. The representation laws on induced functions follow
from associativity and are transported by the actual coordinate equivalence.
The inverse-coordinate laws use the unique two-coset description of the concrete
real Weil group. No proof of an external theorem is used in place of those laws.

The constructed objects have the actual carriers `Complex` or
`Complex × Complex`, with no basis-existence or representation-existence
assumption. They are realizations, not isomorphism classes. Their genuine classes
are obtained using the published `FiniteRepresentation.classOf` and its proved
intertwining-equivalence relation; this file creates no competing quotient.
The auxiliary two-coset function model is specific to the real/complex groups.
No generic-induction comparison theorem is asserted by this file.

The source is J. Tate, *Number theoretic background*, Corvallis Part II (1979):
section 1.4.3, printed p.6 (one-based PDF15), gives the groups and conventions;
section 2, printed pp.9-10 (PDF18-19), specifies finite-dimensional continuous
complex representations, quasi-characters, restriction and induction;
section 2.2.2, printed p.10 (PDF19), gives the archimedean induction setting.
The explicit two-coset realization and its elementary construction proofs are
derived implementation details. No classification theorem from section 2.2.2
is asserted in this file.

The retained original is
`C:/Central-Library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`,
literature ID `tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The cited passages were read directly. All coefficients and constructed carriers
here are in `Type`; the reused finite-representation interface permits independent
group and carrier universes. The complex topology is the usual one. As in the
published continuity predicate, continuity is tested on endomorphisms with their
finite-dimensional module topology. No topology on the full function space,
smoothness condition, Haar normalization or spectral parameter is added.

All continuous quasi-characters are permitted, including nonunitary ones.
The two-dimensional construction also permits conjugation-invariant characters;
it does not declare them irreducible. The criterion for irreducibility when a
character differs from its conjugate, the classification of all irreducible
archimedean representations, identification of the abelian coordinate with
reciprocity, arithmetic L/epsilon expressions, and dual/tensor comparison
formulas are separate theorem or construction obligations.

The only project imports are the published `Langlands.Weil.Archimedean`,
`Langlands.Weil.Representation.Predicates` (and its `Basic` dependency), and
`Langlands.Representation.Twist.Definitions`. The scalar constructor is reused
from the latter; no draft implementation from another worker is copied.
Pinned environment: Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
