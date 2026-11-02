# Actual group-scheme ambient functions and the general-linear comparison

For a group scheme `G` over an arbitrary number field `F`,
`GroupSchemeFunctions.RationalInvariantFunctions F G` is the actual complex
vector space of functions on its actual full adelic point group with
`f (rational q * x) = f x` for every actual rational point `q`.
The definition reuses Mathlib's coinduction of the trivial representation,
as does the existing matrix ambient space. `rationalRightAction` is its
positive right-translation representation: `R(g)f(x) = f(x * g)`.

`quotientLinearEquiv` upgrades the previously constructed quotient-function
equivalence to a complex linear equivalence with functions on the actual
rational homogeneous quotient. Its right-translation identity proves that
quotient pullback preserves the same positive action.

For affine `G`, continuity cuts out `continuousSubrepresentation` and
`ContinuousRationalFunctions`, with their inherited complex vector space and
right representation. Continuity is preserved by precomposition with actual
right multiplication in the actual topological adelic point group.
`continuousQuotientLinearEquiv` identifies continuous complex functions on the
actual rational quotient with this continuous subspace. Continuity descends
and ascends by the quotient topology's universal property. No topology on
these function spaces beyond the already specified topology on their domains
is asserted by this linear equivalence.

For the published general linear group scheme on `Fin n`, for every natural
`n`, `generalLinearEquiv` is a complex linear equivalence onto the existing
`Langlands.Automorphic.RationalInvariantFunctions F n`.
It sends `f` to `f` composed with the inverse of the actual adelic
multiplicative homeomorphism. Its inverse composes with the forward
homeomorphism. The rational compatibility of that homeomorphism and the
actual rational point equivalence prove both rational invariance conditions.
The inverse laws follow from the point homeomorphism's inverse laws.
The comparison intertwines the existing matrix right action, by
multiplicativity of the point comparison. `continuousGeneralLinearEquiv`
restricts it to the existing `ContinuousRationalFunctions F n`, since both
point comparisons are continuous, and also intertwines the continuous right
representations.

The provenance is internal and derived: these are function descent and
comparison constructions using the actual point, quotient and matrix
ambient APIs. They do not introduce substitute matrix functions. The
underlying arithmetic quotient and positive right-action conventions are
Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
Section 2.6, printed pages 67–69, and Section 9.1, printed pages 239–242.
The implemented comparison concerns the full rational quotient.
The split-centre quotient and its comparison, measures, finite volume,
finite-level compatibility, smoothness, differential growth, compact and
central finiteness, constant terms, cuspidality and Hilbert realizations
remain separate obligations. These ambient functions are not claimed to
satisfy the automorphic analytic conditions.
