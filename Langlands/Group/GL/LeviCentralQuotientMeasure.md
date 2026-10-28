# Haar measure on the full central quotient of a standard block Levi

This module proves that every Haar measure on the actual central quotient
`B.Levi F / Subgroup.center (B.Levi F)` of a standard block Levi
`∏ i, GL_(n_i)(F)` is right invariant and invariant under inversion. These are
the two measure laws used when matrix-coefficient pairings on this quotient are
changed by right translation and by `g ↦ g⁻¹`. The existing
`Langlands.Group.GL.CentralQuotientMeasure` treats one general linear group; this
module is its block-Levi analogue.

## Inversion invariance from right invariance

`Langlands.isInvInvariant_of_isMulRightInvariant` works on any locally compact
topological group `G` with Borel measurable structure. It takes a Haar measure
`μ` that is regular and right invariant, and concludes `μ.IsInvInvariant`.

The proof uses Mathlib's regular Haar uniqueness. The inverse measure `μ.inv` is
left invariant because `μ` is right invariant, so `μ.inv = c • μ` with
`c = haarScalarFactor μ.inv μ`. Applying inversion twice gives `μ = c² • μ`.
Evaluating on a positive compact set, whose measure is positive and finite,
gives `c² = 1`, hence `c = 1` in `ℝ≥0∞`, and `μ.inv = μ`.

## Positive characters of the Levi central quotient

`GeneralLinear.BlockShape.leviCentralQuotient_positiveCharacter_eq_one` works
over every field `F` and block shape `B`. It proves that every monoid
homomorphism `χ` from the full central quotient of `B.Levi F` to `ℝ≥0` takes the
value one everywhere. No topology or continuity is assumed.

The proof pulls `χ` back to `B.Levi F` along the quotient map. By
`MonoidHom.pi_ext` it suffices to treat each block factor separately. The
restriction `ψ` of the pullback to the `i`-th factor is a character of
`GL_(n_i)(F)`. A scalar matrix placed in the `i`-th block and the identity
elsewhere commutes with every element of the Levi, so it lies in the full
center and `ψ` is trivial on scalars. The public theorem
`Langlands.RankinSelberg.GeneralLinearUnimodularity.character_eq_one` then shows
that `ψ` is identically one. Hence the pullback, and therefore `χ`, is trivial.

## Right invariance of regular Haar measures

`GeneralLinear.BlockShape.haar_leviCentralQuotient_isMulRightInvariant` assumes
a topological-group topology on `B.Levi F`, local compactness of the full central
quotient, and a Borel measurable structure there. It proves that every regular
Haar measure on the quotient is right invariant.

Right translation by `q` is a homeomorphism, so the translated measure is again
regular and, by regular Haar uniqueness, equals its Haar scalar factor times
`μ`. This factor is Mathlib's modular character at `q`, an `ℝ≥0`-valued
character of the quotient. The previous theorem shows it equals one.

## Actual p-adic specialization

`PadicField.TopologicalData.leviCentralQuotientHaar_unimodular` takes a prime
`p`, a `PadicField p` with compatible `TopologicalData T`, a rank `n` and a block
shape `B`. With `T.topology` installed, it quantifies over every measurable
structure on the actual full central quotient with `BorelSpace` and every Haar
measure `μ` on it, and concludes

`μ.IsMulRightInvariant ∧ μ.IsInvInvariant`.

There is no regularity, local-compactness or countability premise. The proof
obtains the topological-group structure from `T.leviTopologicalGroup B` and the
Hausdorff, locally compact and second-countable quotient properties from
`glBlockCentralQuotientTopology`. Haar regularity is then inferred by instance
search, so both generic theorems apply.

## Provenance and scope

This is an internal derived result. The character argument is the block-wise
form of the argument in `Langlands.Group.GL.CentralQuotientMeasure` and reuses
Worker 116's `character_eq_one` unchanged. The measure-theoretic steps use
Mathlib at pinned commit `5ed2965256430c3649e86755f9576b54eca72435`:
`MeasureTheory/Group/ModularCharacter.lean` and
`MeasureTheory/Measure/Haar/{Basic,Unique}.lean`. This module proves only the
special case of unimodularity stated above, not a general reductive-group
result.

No integrability, coefficient bound or representation-theoretic statement is
asserted here.
