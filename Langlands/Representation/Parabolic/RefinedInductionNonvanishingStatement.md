# Evaluation and nonvanishing for actual refined induction

`Langlands.Parabolic.NormalizedRefinedInductionNonvanishingStatement` is a closed
proposition definition. It states two properties of the existing
`T.normalizedRefinedInduced B S σ`; it does not prove either property.

The parameters are a prime `p`, a `PadicField.{uF} p`, compatible topological data
`T`, a natural number `n`, a block shape `B`, a block refinement `S`, and a complex
representation `σ` of the actual subgroup `refinedLevi F.Carrier B S` on a
carrier `V : Type uV`. The statement installs `T.topology` and the existing
topological-group structure `T.leviTopologicalGroup B`. It assumes only that
`σ` is smooth. The field and carrier universes are independent.

The local name `σP` is the existing inflated action twisted by
`T.refinedParabolicHalfModulus B S`. The local name `I` is exactly
`Rep.of (T.normalizedRefinedInduced B S σ)`, with carrier universe `max uF uV`.
That carrier is
`Induction.SmoothFunctions (refinedParabolic F.Carrier B S) σP`.
The conclusions are:

- The actual map `f ↦ Induction.eval (refinedParabolic F.Carrier B S) σP f 1`
  from `I` to `V` is surjective.
- If `V` is nontrivial, then this same actual induced carrier is nontrivial.

The definition retains the induction's right-translation action, its positive
half-modulus covariance, and the uniform open right stabilizer required of each
smooth induced function. It does not restrict the whole induced space to compact
support. There are no irreducibility, admissibility, cuspidality, finite-length,
or chosen-section hypotheses. All natural ranks, including zero, and all
refinements are quantified; the surjectivity clause also covers a zero carrier.

This is an internal specialization target for the public
`Induction.compactLocalSection` and `Induction.compactLocalSection_apply` in
`Langlands.Representation.Induction.CompactLocalSection`. A later proof can use a
compact local section at identity with quotient neighborhood `Set.univ` and
include its underlying function into the existing smooth induced space.
The present file neither repeats that construction nor assumes evaluation
preimages. Nonvanishing will support a later irreducible-quotient argument after
an independently established finite-length theorem; neither that theorem nor a
quotient is claimed here.
