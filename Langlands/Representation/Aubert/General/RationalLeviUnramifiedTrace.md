# Normalized induced traces for the actual rational Levi norm family

This internal derived adapter specializes `UnramifiedInducedTrace` to the full
family `leviRationalNormCharacters` and combines it with
`RationalLeviCharacterDensity`. It introduces no original-literature assertion.

The base field is an arbitrary nonarchimedean local field `F`. The ambient affine
group scheme `G` has the canonical `RationalPointFamily.pointTopology` on its
rational points. The index `I` consists of literal simple relative roots. The
coefficient group is exactly the subgroup `levi i ν I`, with its inherited
topology. Its norms range over every rational algebraic character of the same
representative `Standard.leviScheme i ν (rootSet i ν I)` through the actual
point homeomorphism. No finite subfamily replaces these norms.

The ambient rational-point group is assumed locally compact, nonarchimedean and
Hausdorff, with its Borel measurable structure and a left-invariant measure `μ`
finite on compact sets. An actual decomposition `h : IsSemidirectDecomposition
P (levi i ν I) U` has closed radical `U` and continuous canonical Levi
projection. The actual quotient `Induction.LeftQuotient P` is compact. `P` and
`U` are actual subgroups of this same rational-point group; this allows both
standard parabolics and other parabolics sharing its literal Levi to instantiate
the interface. The coefficient object `A` is an admissible `SmoothRep ℂ` of
that Levi. The field and coefficient-carrier universes are independent.

`rationalLeviUnramifiedInductionDistribution` is the genuine distribution
character of the actual normalized induction of `A` twisted by an actual
unramified character. It specializes the existing construction, which derives
both twisted coefficient admissibility and actual induced admissibility from
`A.IsAdmissible` and the retained compact quotient. Neither connected
reductivity of the Levi nor closedness of `P` is required for this definition.

With `P` closed, `rationalLeviUnramifiedInductionDistribution_eval` computes its
value on each Schwartz–Bruhat test function with the single finitely supported
coefficient function `normalizedInductionTwistCoefficients`. That function is
chosen before every norm family and character. Each summand is its coefficient
at `p : P` multiplied by the complex value of the character at `h.projection p`.
The proof supplies `continuous_leviRationalNormCharacters` for every rational
character, discharging all norm-continuity premises of the generic evaluation
law. The scalar continuity theorem similarly specializes the generic result to
the actual inherited compact-open character topology. No topology on the space
of distributions is asserted.

The coordinate evaluation and continuity theorems additionally retain
`hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I))`.
The evaluation law reconstructs each character value as its actual
valuation-image Laurent monomial at the inverse image of `h.projection p` under
`leviRationalPointHomeomorph`. It uses the same integer basis and valuation
projection as `leviRationalUnramifiedCharacterCoordinates_symm_apply`; integer
powers, including negative powers, are retained. The finite coefficient
function remains the same one. Coordinate continuity composes the scalar
continuity theorem with the inverse coordinate homeomorphism. Rank zero is
included.

Finally, `rationalLeviUnramifiedInductionDistribution_eq_of_principalOpen`
allows a second actual decomposition `Q = (levi i ν I) N`, with closed `N`, a
continuous canonical projection, closed `Q` and compact actual quotient. Its
admissible coefficient object `B` has a second independent carrier universe.
Given a nonzero polynomial in the actual finite coordinates and equality of
these two genuine distribution families on its principal open locus, their
distributions agree for every actual unramified character. The proof applies
`dense_leviUnramifiedPrincipalOpen` and the generic closed-equality-locus
extension theorem, again discharging all norm-continuity premises with the
full rational norm family.

Connected reductivity of the actual Levi representative, the nonzero polynomial
and the induced-distribution comparison on its locus remain explicit inputs.
The adapter supplies no generic irreducibility or representation-family
polynomial witness, no proof of that comparison, and no finite-length
admissibility or exact-K0 conclusion. Actual parabolic quotient compactness and
projection continuity also remain inputs. The whole
`RationalInducedK0WeylConjugacyStatement` remains open.
