# Strict normalized Jacquet exponents on actual rational points

This pair states the sufficiency direction of the general square-integrability
criterion needed in Casselman's rank-one irreducibility argument. It supplies
no proof of the criterion or of self-association.

The source is W. Casselman, *Introduction to the theory of admissible
representations of p-adic reductive groups*, draft of 1 May 1995, Theorem 4.4.6,
printed/PDF p.45, with its exponent convention on pp.44–45. The registered source
is `casselman-1995-admissible-representations`, SHA-256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
The introduction on p.2 allows any nonarchimedean locally compact field.
Theorem 6.5.1, pp.64–65, and Proposition 7.1.3 and Theorem 7.1.4, pp.67–68,
describe the intended later use for cuspidally induced representations.

`simpleRootPointValue` evaluates the character underlying the literal
`SimpleRoot i ν` label on a point of the actual maximal split torus. It uses the
existing `rationalCharacterEval` and the existing identification of the
character lattice with rational characters of a commutative group scheme.
`IsNoncentralNegativeTorusPoint` requires every simple-root value to have
valuation at most one and at least one to have valuation strictly below one.
These comparisons use the canonical `ValuativeRel.valuation k`. They express
the closed negative chamber with its central valuation directions removed;
they do not choose a norm or change the field topology. The existential
strictness condition is false when there are no simple roots.

`HasStrictNormalizedJacquetExponents` concerns the published actual standard
parabolic, Levi and unipotent point subgroups. For every finite subset `J` of
the literal simple-root labels it forms the actual normalized Jacquet object
`jacquetFunctor (h J) (hU J)`. Its exponents are the existing
`IsCentralExponent`: characters of the full group center of that Levi with
open kernel and nonzero uniform generalized central-character subrepresentation.
Each exponent is tested on every central Levi point equal in `G(k)` to the
image of a torus point satisfying the displayed negative-chamber condition.
The bound is the literal complex norm inequality `‖χ(z)‖ < 1`.
It is a condition on the normalized quotient representation, so the inverse
half-modulus twist is already included. In Casselman's unnormalized convention
the corresponding bound contains the inverse half-modulus.

`RationalStrictJacquetSquareIntegrabilityStatement` quantifies over any
connected reductive group scheme over any nonarchimedean local field, its
actual maximal split torus, and a generic cocharacter. Rational points carry
the canonical `pointTopology`. The displayed local compactness,
nonarchimedean-group and Hausdorff hypotheses are retained.
`StandardCocharacterStatement` supplies the actual semidirect decompositions;
closedness of each actual radical remains explicit. For any admissible
smooth complex object with a genuine smooth unitary central character and
the strict exponent condition, the statement concludes
`IsSquareIntegrableModCenter` for every supplied Borel Haar measure on the
quotient by the full actual group center. This is square-integrability of
every coefficient of a smooth-dual functional and a representation vector,
as specified by the existing predicate.

The source states an equivalence. This target requests only its sufficiency
direction and assumes a unitary central character as explicit data. Its
testing set uses actual central Levi points in the chosen maximal split
torus rather than introducing a separately represented split-center scheme.
The geometric comparison with the source's split component, the generalized
central-character decomposition, the asymptotic coefficient comparison and
the integration argument all remain obligations of a proof. No root
realization theorem, Cartan estimate or analytic assertion is supplied by
these definitions.

The field and representation universes `u` and `v` are independent, with
representation carriers in `max (u + 1) v`. No characteristic-zero, split,
quasisplit, nonempty-root, irreducibility or finite-length restriction is
imposed. This supplementary analytic target does not change
`RationalRankOneSelfAssociationStatement` or supply any of its missing
representation-theoretic inputs.
