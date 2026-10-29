# Conditional detection of actual fine induction quotients

Authors: Worker 845, Worker 526 and Worker 435. Worker 526 wrote the
unreviewed compiled proof prototype `FineOppositeJacquetQuotientDetectionProof`
in the shared draft of task `ebf9d80c-dcd4-45c5-91f8-428ad29b1363`, revision 2.
This proposition transcribes that prototype's theorem type. Worker 435 designed
the change-of-group and flattened Hom transports that the prototype adapts.
Worker 845 wrote this statement pair. Worker 979 later updated this Markdown
after the second-adjointness proof was published. The Lean file is unchanged.

`Langlands.FineOppositeJacquetQuotientDetectionStatement.{uF,uV,uW,uZ}` is a
closed proposition definition (`def ... : Prop`). This module states the
assertion and contains no proof. It does not prove or assume either
second-adjointness clause outside its own two explicit premises.

## Explicit premises

The proposition is an implication. Its first two hypotheses are:

1. `Parabolic.StandardSecondAdjointnessClause.{uF, uV, uZ}`. For each
   positive rank and block shape this gives a family of linear equivalences
   from intertwiners `i_P σ → π` to intertwiners `σ → r_opP π`, for admissible
   `σ` on a product Levi with carrier in `uV` and admissible `π` on `GL_n` with
   carrier in `uZ`.
2. `Parabolic.RefinedSecondAdjointnessClause.{uF, uV, uW}`. This gives the
   same kind of family inside a product Levi: `σ` is on the refined subgroup
   with carrier in `uV`, and `π` is on `B.Levi F.Carrier` with carrier in `uW`.

Both clauses are defined in `Parabolic.SecondAdjointnessStatement`, which this
statement imports for them. They are proved separately in the Library.
`Langlands.Parabolic.normalizedSecondAdjointness`, in
`Parabolic.SecondAdjointnessProof`, proves
`Parabolic.NormalizedSecondAdjointnessStatement.{uF, uV, uW}` with no hypotheses.
That proposition is the conjunction of the standard and refined clauses at
those three universes. Its first projection at `{uF, uV, uZ}` is the first
premise, and its second projection at `{uF, uV, uW}` is the second premise.
Since `uW` and `uZ` are independent here, the theorem is used twice with
different universes:
`(Parabolic.normalizedSecondAdjointness.{uF, uV, uZ}).1` and
`(Parabolic.normalizedSecondAdjointness.{uF, uV, uW}).2`.

The proposition itself is still an implication. It does not import
`Parabolic.SecondAdjointnessProof`, and the conclusion below is asserted only
under the two premises. A consumer that needs the conclusion without premises
may import `Parabolic.SecondAdjointnessProof` itself and supply the two
premises by these two instantiations. The naturality parts of the clauses
are present in the premises. The published proof of this implication,
`Langlands.fineOppositeJacquetQuotientDetection`, does not use them.

## Quantified data and hypotheses

After the premises, the proposition quantifies over every prime `p` (as
`[Fact p.Prime]`), every p-adic field `F : PadicField.{uF} p` and every
compatible topological datum `T : F.TopologicalData`. The installed topology is
exactly `T.topology`; the topologies of `GL_n(F)`, of the product Levi
subgroups and of the refined subgroup are the induced ones of the existing
constructions. It then quantifies over every natural `n` with `0 < n`, every
ordered block shape `B : BlockShape n` and every refinement
`S : BlockRefinement B`. The positivity of `n` is the positivity required by
both adjointness clauses.

The fine input is an actual bundled complex representation
`ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)` of the flattened product Levi.
The only hypotheses on it are:

* `Representation.IsIrreducible ω.ρ`, Mathlib's simple-order predicate on its
  subrepresentations, which includes a nonzero carrier;
* `CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ`, which is admissibility
  (including smoothness) together with vanishing of the actual unipotent
  coinvariants for every proper standard block refinement.

The real vectors `v : Fin (B.flatten S).length → ℝ` and `t : Fin B.length → ℝ`
are arbitrary. No unitarity, positivity, strict ordering, genericity or
regularity condition is imposed on `ω`, `v` or `t`.

## The actual fine source and the two inductions

Put `τ := RelativeJacquetMultiplicity.fineTwist T B S ω v t`. This is the
existing representation of `Geometric.refinedLevi F.Carrier B S` on the carrier
of `ω`. Its action multiplies `ω` by the positive real character

```text
∏ k |det(m_k)|_F^(-v(k) + t(((B.flattenBlockEquiv S).symm k).1))
```

of the flattened product Levi (the Library's `T.leviRealPowerTwist`, with the
residue-normalized absolute value of each block determinant), and is
then pulled back along the inverse of the constructed equivalence
`Geometric.flattenedLeviEquiv F.Carrier B S`. The fine exponents enter with a
negative sign and the restricted coarse exponents with a positive sign.

* The inner induction is `RelativeJacquetMultiplicity.innerInduced T B S τ`,
  the representation `T.normalizedRefinedInduced B S τ.ρ` of
  `B.Levi F.Carrier`. It is the actual smooth induction from the refined
  parabolic of the product Levi, with right translation and covariance by the
  positive half of the upper refined modulus. Its carrier lies in `max uF uV`.
* The ambient fine induction is
  `RelativeRecovery.fineAmbientInduced T B S ω v t`, namely
  `CuspidalJacquetMultiplicity.induced T (B.flatten S)` applied to the same
  real twist of `ω`, before any pullback. This is the actual normalized upper
  parabolic induction `T.normalizedParabolicInduced (B.flatten S)` to
  `GL_n(F)`, with positive-half covariance. Its carrier lies in `max uF uV`.

## The two opposite Jacquet targets

* `T.normalizedRefinedOppositeJacquet B S π.ρ` is the actual coinvariant
  quotient of the carrier of `π` by the product of the inner lower radicals.
  The refined subgroup acts through its radical normalizer, twisted by the
  inverse half of `T.refinedOppositeLeviModulus B S`, which is the inverse of
  the full upper refined modulus. The normalizing scalar is therefore the
  positive half `T.refinedLeviHalfModulus B S`.
* `T.normalizedComposedOppositeJacquet B S J.ρ` is the actual coinvariant
  quotient of the carrier of `J` itself by
  `Parabolic.composedOppositeUnipotent F.Carrier B S`. This group contains the
  outer lower block radical and the embedded inner lower radicals. The refined
  subgroup acts through its embedding in `GL_n(F)`, twisted by the inverse half
  of `T.composedOppositeLeviModulus B S`. The normalizing scalar is the
  positive half `T.composedLeviHalfModulus B S`.

These are the quotient carriers of `π` and `J`, in universes `uW` and `uZ`. The
second target is the opposite Jacquet module of `J`, not of an induced
representation such as `RelativeJacquetMultiplicity.ambientJacquet`.

## The conclusion

The conclusion is the conjunction of two universal equivalences.

1. For every `π : Rep.{uW} ℂ (B.Levi F.Carrier)` with `IsAdmissible π.ρ` and
   `Representation.IsIrreducible π.ρ`, the following are equivalent:
   * there is `f : τ.ρ.IntertwiningMap (T.normalizedRefinedOppositeJacquet B S π.ρ)`
     with `f ≠ 0`;
   * there is
     `q : (RelativeJacquetMultiplicity.innerInduced T B S τ).ρ.IntertwiningMap π.ρ`
     with `Function.Surjective q`.
2. For every `J : Rep.{uZ} ℂ (GeneralLinear n F.Carrier)` with
   `IsAdmissible J.ρ` and `Representation.IsIrreducible J.ρ`, the following
   are equivalent:
   * there is `f : τ.ρ.IntertwiningMap (T.normalizedComposedOppositeJacquet B S J.ρ)`
     with `f ≠ 0`;
   * there is
     `q : (RelativeRecovery.fineAmbientInduced T B S ω v t).ρ.IntertwiningMap J.ρ`
     with `Function.Surjective q`.

`Representation.IntertwiningMap` is Mathlib's space of all complex-linear maps
commuting with the two actions; no continuity is required.
`Langlands.IsAdmissible` means smoothness together with finite dimensionality
of the fixed vectors of every open subgroup. The carriers may be infinite
dimensional. Nonvanishing is an actual existential `f ≠ 0`, not a rank or
dimension convention. A surjection is an actual intertwiner whose underlying
function is surjective. No quotient map or Hom equivalence is chosen in the
statement.

The universes `uF`, `uV`, `uW` and `uZ` of the field, the fine source, the
coarse target and the ambient target are independent. The level parameters of
the declaration appear in this order.

## Scope

The targets `π` and `J` are assumed only admissible and irreducible. They need
not be tempered, unitary, supported on any particular cuspidal datum, or
quotients of any further induced representation. The statement assumes no
unitarity, positivity, strictness, support condition, middle representation,
finite length, positivity of a finrank, finite dimensionality, Jacquet
semisimplicity, chosen quotient map or chosen Hom equivalence.

The statement does not supply arbitrary-tempered quotient reflection, occurrence
continuation, or an equality of positive Hom dimensions. It does not identify
Jordan–Hölder multiplicities with these Hom spaces. The parent J-specific Hom
comparison `Langlands.GLRelativeCosocleHomComparisonStatement` is not proved by
it. Supplying the two premises with
`Parabolic.normalizedSecondAdjointness` does not change this. The conclusion
is still the same pair of equivalences, with none of these further results.

## Internal provenance

This is an internal algebraic specialization of existing published Library
interfaces, not a transcription of a theorem printed in the original
literature. The two-clause shape, the explicit adjointness premises and these
Hom spaces are formalization choices. They are not attributed to Silberger's
1978 article or to any other printed theorem. The original-source provenance of
the two assumed clauses (Casselman 2019, Chapter III) is recorded with
`Parabolic.SecondAdjointnessStatement`. That citation is not a proof. In the
Library the clauses are proved by the separate theorem
`Langlands.Parabolic.normalizedSecondAdjointness` described above, which this
statement does not import.

The rationale is the following route through published results. The
separately published theorem `Langlands.fineOppositeJacquetQuotientDetection`,
in `Classification.FineOppositeJacquetQuotientDetectionProof`, implements it
and keeps the two premises as hypotheses.

* `Langlands.fineTwistIrreducibleAdmissible`, in
  `Classification.FineTwistRegularityProof`, proves that `τ` is irreducible and
  admissible, and that the flattened real twist of `ω` is cuspidal, hence
  admissible. These are the inducing admissibility hypotheses of the two
  clauses, for every real `v` and `t`.
* In clause 1, the refined adjointness equivalence for `τ` and `π` identifies
  the intertwiners out of the inner induction with the intertwiners into the
  refined opposite Jacquet module.
* In clause 2, the standard adjointness clause on `B.flatten S` identifies the
  intertwiners out of the ambient fine induction with intertwiners from the
  flattened twist into
  `CuspidalJacquetMultiplicity.oppositeJacquet T (B.flatten S) J`. The published
  theorem `Langlands.Parabolic.flattenedOppositeJacquetComparison`, in
  `Parabolic.FlattenedOppositeJacquetComparisonProof`, compares that quotient
  with the composed quotient pulled back along `flattenedLeviEquiv`.
  Postcomposition with the inverse comparison, followed by change of group along
  `flattenedLeviEquiv`, identifies the Hom space with the composed
  opposite-Jacquet Hom space from `τ`.
* A linear equivalence preserves and reflects nonzero elements. Mathlib's
  `Representation.IsIrreducible.surjective_or_eq_zero` makes a nonzero
  intertwiner onto an irreducible target surjective. Conversely, an irreducible
  target has a nonzero carrier, so a surjective intertwiner onto it is nonzero.

The statement imports only the modules defining its notions:
`Classification.RelativeRecoveryStatement`, for `fineAmbientInduced` and,
through its imports, `fineTwist`, `innerInduced` and the two normalized
opposite Jacquet representations; and `Parabolic.SecondAdjointnessStatement`,
for the two premises. It imports none of the proof modules named in this file,
including `Parabolic.SecondAdjointnessProof` and
`Classification.FineOppositeJacquetQuotientDetectionProof`.
