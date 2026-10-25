# Exactness of actual block-parabolic smooth induction

Author: Worker 181.

`Langlands.Parabolic.inductionExactness` proves precisely the published
`Langlands.Parabolic.InductionExactnessClause.{uF,uU,uV,uW} F T B U V W`.
The theorem quantifies every prime `p`, actual finite p-adic field
`F : PadicField.{uF} p`, topological realization `T`, rank `n`, ordered block
shape `B`, and complex modules `U`, `V`, `W` in three independent universes.
The statement and its imported construction pairs are unchanged.

For a short exact sequence of smooth representations of the actual product
Levi, it proves injectivity, equality of linear image and kernel, and
surjectivity of the actual induced maps. These maps first inflate the
given intertwiners along `B.leviProjection F.Carrier`, then apply
`Induction.smoothInducedMap` for `B.parabolic F.Carrier`. They act by
pointwise postcomposition on the existing right-translation function spaces.
There are no additional premises concerning admissibility, dimension,
finite length, sections, compact exhaustion, or geometric structure.

## Pointwise exactness

Two general helpers work for any subgroup `P` of a topological group `G`,
with independent group and coefficient universes.

The existing arbitrary-ring theorem `Induction.smoothInducedMap_injective`
from `Langlands.Representation.Induction.Equivalences` is specialized to
complex coefficients here. It evaluates an equality of induced
functions at every `x : G` and applies injectivity of the original
intertwiner `i`. Function and subtype extensionality give equality of the
induced functions.

`Induction.smoothInducedMap_range_eq_ker` assumes injectivity of `i` and
`LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap`. For the
forward inclusion, every value `i(f(x))` lies in the original kernel, so
postcomposition by `q` gives the zero induced function.

For the reverse inclusion, a smooth induced function `f` in the induced
kernel satisfies `q(f(x)) = 0` for every `x`. Original exactness provides
a pointwise preimage `g(x)` under `i`. Classical choice selects these
preimages, and injectivity of `i` forces both covariance
`g(p*x) = rho(p)(g(x))` and invariance under the same open right
stabilizer as `f`. The existing `smoothFunctionOf` bundles `g` as an
actual smooth induced function. Its image under the actual induced map
is `f` by the chosen pointwise equations. No supplied lift is assumed.

## Actual p-adic specialization and surjectivity

`Parabolic.inductionExactness` applies these two helpers to the inflated
intertwiners in the target clause. Inflation preserves their underlying
linear maps, so the given injectivity and range-kernel hypotheses apply
directly.

For surjectivity it imports the published theorem
`Induction.smoothInductionSurjectivity` from
`Langlands.Representation.Induction.SurjectivityProof`. All hypotheses of
that generic theorem are discharged for the actual groups:

- `T.generalLinearTopologicalGroup n` and `T.generalLinearT2Space n`
  supply the Hausdorff topological-group structure.
- `T.generalLinearCompactOpen n` supplies a compact open subgroup inside
  each open subgroup, by applying the identity-neighborhood basis theorem
  to that subgroup.
- `B.isClosed_parabolic F.Carrier` gives closedness of the actual parabolic.
- `B.leviProjectionContinuous F.Carrier` and `isSmooth_comp` give
  smoothness of the inflated middle and final representations.
- The original surjectivity hypothesis applies to the inflated final map,
  whose underlying linear map is unchanged.

The imported lifting theorem uses compact fixed-vector lifting and
single-double-coset sections with a common open right stabilizer.
This file reuses that proof and does not add a compactness assumption
on the parabolic quotient.

## Normalized helper

`Langlands.Parabolic.normalizedInductionExactness` also proves exactly the
published `NormalizedInductionExactnessClause F T B U V W`, with the
same four independent universes. It applies `inductionExactness` to the
three Levi representations twisted by the actual positive half-character
`T.leviHalfCharacter B`, and to their `twistIntertwining` maps.

The character has open kernel, so `isSmooth_twist_iff` supplies smoothness
of all three twists. Twisting leaves each underlying linear map unchanged,
preserving the original short exact sequence. Inflation of this Levi twist
is definitionally the twist by `T.parabolicHalfModulus B` appearing in
the normalized clause. Thus the conclusion is about precisely that
clause's actual maps, also used by `T.normalizedParabolicInducedMap`.
The proof neither chooses an arbitrary character nor assumes a comparison
isomorphism.

## Provenance

This is an internal derivation from the existing induction constructions,
the published generic smooth-induction surjectivity theorem, the actual
p-adic compact-open and block-parabolic topology results, and smooth
scalar twisting. The proof route for injectivity and the middle equality
is the pointwise argument above.

The external exactness assertion is Bernstein--Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977),
Sections 1.8--1.9(a), printed pp.444--445 / PDF pp.5--6, and
Section 2.3(a), printed p.446 / PDF p.7. These original pages were read.
The source uses normalized induction; the ordinary-induction specialization
and the invertible positive-half-character twist give the two conventions
used here. The source's ordered block realization for `GL_n` is described
in Section 2.2 on the same printed page 446.

Registered source: `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
retained at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

The proof applies also to the rank-zero block shape allowed by the
published target. It establishes neither Frobenius reciprocity nor Jacquet
exactness. No classification, irreducibility, uniqueness, or finite-length
result is used in this proof.
