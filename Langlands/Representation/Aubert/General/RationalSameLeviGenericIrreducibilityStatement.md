# Generic irreducibility of two inductions sharing a standard Levi

Author: Worker 121.

This module states
`Langlands.Aubert.General.RationalPointFamily.RationalSameLeviGenericInductionIrreducibilityStatement`.
It provides no proof.

## Exact content

The hypotheses are copied from the unchanged published
`RationalSameLeviGenericInductionIsoStatement.{u,v}`:

- a nonarchimedean local field of any characteristic, a connected reductive
  group, an actual maximal split torus and a generic cocharacter;
- the canonical `pointTopology` on the rational point group, with its
  local compactness, nonarchimedean-group property and Hausdorffness displayed;
- `StandardCocharacterStatement` and closedness of every literal standard
  unipotent subgroup;
- subsets `I,J`, an actual point `g` satisfying
  `x ∈ L_J ↔ g⁻¹ * x * g ∈ L_I`, and connected reductivity of the displayed
  standard Levi scheme;
- an irreducible admissible smooth complex representation `σ` of the literal
  Levi subgroup `L_J`.

The field universe `u` and representation-carrier universe `v` are independent.
There are no splitness, quasisplitness, positive-rank or characteristic-zero
restrictions. No additional topological or representation-theoretic premise
is inserted.

Write `Aχ` for the actual `normalizedInductionFunctor` from `P_J`, applied to
`σ.twist χ`, and `Bχ` for `conjugateInductionFunctor` from `g P_I g⁻¹`, applied
to the same literal twist. The second decomposition has the literal Levi
`L_J`, rather than a separately chosen isomorphic Levi. Both objects and all
normalizations are exactly those in the published isomorphism target.

The polynomial has variables `Fin (rationalImageRank L_J)` and coefficients
in `ℂ`. Its locus is the published `leviUnramifiedPrincipalOpen` in the
coordinates `leviRationalUnramifiedCharacterCoordinates`, for the full rational
norm family. A nonzero polynomial defines a dense nonempty locus by
`dense_leviUnramifiedPrincipalOpen`; rank zero is included.

The conclusion is that one nonzero polynomial `p` exists such that both `Aχ`
and `Bχ` are irreducible for every `χ` in its principal open locus. The
conjunction is pointwise, on the same locus. Irreducibility of the inducing
representation and its admissibility are hypotheses; irreducibility,
admissibility and finite length of the induced objects are not premises.

## Provenance and outstanding proof

This is an internal prerequisite extracted from the classical generic
irreducibility theorem, specialized to the two actual parabolics occurring
in the published generic-isomorphism target. It is not a quotation of a
single source theorem, and is not an external structural input.

The registered original `konno-2003-langlands-classification`, T. Konno,
*A note on the Langlands classification and irreducibility of induced
representations of p-adic groups*, Kyushu J. Math. 57 (2003), 383–409,
uses a nonarchimedean local field of any characteristic in §2, printed p.384.
Theorem 4.2, pp.402–405, treats an arbitrary irreducible admissible inducing
representation. It gives irreducibility for sufficiently small parameters
whose real parts avoid the relative-root walls. That theorem alone does
not state the polynomial principal open asserted here. Passing from an
irreducible parameter to a Zariski principal open needs algebraic openness,
as in Renard VI.8.4 Proposition, and the actual parameter comparison.
Applying that argument to both parabolics and multiplying their nonzero
polynomials gives the common locus. If the relative-root set is empty,
the wall-avoidance condition is vacuous.

Waldspurger, registered original `waldspurger-2003-plancherel`, IV.3,
printed p.285, also records nonempty Zariski openness of the induced
irreducibility locus for irreducible inducing data, referring to Sauvageot
for existence of an irreducible parameter. His arbitrary-characteristic
convention is on p.237. This paragraph identifies the classical argument,
not a published Lean proof of the present declaration.

The Lean statement imports the published target, reuses its actual
constructions, and adds no assumption supplying generic irreducibility.
The existing supercuspidal-only `GenericInducedIrreducibilityStatement` and
square-integrable-only `ConditionalParabolicGenericIrreducibilityStatement`
do not establish it. A proof must supply or reuse all representation-theoretic
inputs at their actual hypotheses, as well as the identification of the
conjugate parabolic and its unramified coordinates. Nothing here proves
the generic isomorphism target or equality of induced composition factors.
