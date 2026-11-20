# The fixed-level compact Sobolev estimate on the actual determinant band

`Langlands.Automorphic.operatorCompactSobolev` proves
`Langlands.Automorphic.OperatorCompactSobolevStatement.{u}` with its
original universe parameter and hypotheses. The source is Shalika,
*The multiplicity one theorem for GL(n)* (1974), Lemma 5.6 and the
pointwise estimate in Lemma 5.7, printed pp. 187–188, registered as
`shalika-1974-multiplicity-one`. The implemented route is a direct
determinant-band argument. It never uses the source's
`Z(𝔸) GL_n(F) \ GL_n(𝔸)` norm, so no comparison between the two
norms is assumed or needed. Every norm on the right of the estimate
is the statement's `L²` norm, `OperatorDeterminantSlice.toL2`, for the
quotient Haar measure restricted to the band `1 < |det| < 2`.

## Local estimate at a band point

`OperatorDeterminantSlice.exists_local_sobolev_of_mem_band`
(module `OperatorBandLocalSobolev`) gives, for each adelic point whose
image lies in the band, an open neighborhood, a finite set of genuine
enveloping operators and a nonnegative constant. These bound the
original realized function on that neighborhood for every vector
fixed by the open subgroup `J`. Its proof combines four steps.

1. The rational quotient map has an open injective neighborhood at
   each point, and the band is open. Inside it choose a compact
   product patch: a closed ball in the ambient archimedean matrix chart
   times a coset `b K` of a compact open subgroup `K ≤ J`
   (`exists_closedBall_productPatch`, module `OperatorBandProductPatch`).
2. A `K`-fixed vector is constant in the finite direction of the patch.
   Comparing additive and multiplicative Haar measure on the unit chart,
   and the product Haar measure with the adelic Haar measure, bounds the
   additive chart integral by the group Haar integral on the patch.
   Cauchy–Schwarz and the injective-patch quotient bound
   (`eLpNorm_bandPatch_le`, module `OperatorBandLocalMeasure`) then bound
   it by the actual band `L²` norm (`exists_lintegral_coordinateSlice_le`).
3. On the compact ball, coordinate derivatives up to order
   `dim + 1` are bounded by a finite sum of slices of genuine enveloping
   derivatives `S.envelopingAction d v` (`exists_coordinateSlice_jet_bound`,
   module `OperatorBandCoordinateDerivatives`). The enveloping action
   commutes with the finite representation, so these derivatives are
   still `K`-fixed and step 2 applies to each of them.
4. The averaged Taylor estimate of `Langlands.Analysis.LocalSobolevPointwise`,
   applied on translated balls of half the radius
   (`Langlands.Analysis.exists_enorm_le_mul_of_lintegral_derivatives_le`),
   gives one pointwise bound on the open half-radius ball. Finite-level
   invariance extends it to the whole open product neighborhood.

## Globalization over the compact set

`exists_unitary_shift` moves an arbitrary adelic point into the band.
Left multiplication by a central scalar idele with determinant norm
`(3/2) |det g|⁻¹` puts `g` at determinant norm `3/2`. By the central
character law and `‖χ‖ = 1`, this continuous shift preserves the absolute
value of every realized function. The private lemma
`exists_norm_bound_of_local` pulls the local neighborhoods back by these
shifts, takes a finite subcover of the compact set `Q`, and uses the union
of the finitely many operator sets and the sum of the constants. The
resulting `D` and `C ≥ 0` depend only on `F`, `r`, `S`, `χ`, `J`, `Q` and
the supplied `hL2`. They are chosen before the `J`-fixed vector and the
point.

The hypothesis that `J` is compact is not used: the argument only needs
`J` open, since it chooses compact open subgroups `K ≤ J` locally.
The supporting modules are `Langlands.Analysis.UnitGroupLocalHaarComparison`,
`Langlands.Analysis.UnitGroupFrameDerivatives`,
`Langlands.Analysis.CompactBallSobolev`,
`Langlands.Global.LeftCosetLocalMeasure`,
`Langlands.Automorphic.OperatorBandLocalMeasure`,
`Langlands.Automorphic.OperatorBandProductPatch`,
`Langlands.Automorphic.OperatorBandCoordinateDerivatives` and
`Langlands.Automorphic.OperatorBandLocalSobolev`.
