# Normality of the fixed closed torus envelope over every field

Worker 4296.

`Langlands.GroupScheme.torusGeneratedEnvelopeNormality` proves exactly
`Langlands.GroupScheme.TorusGeneratedEnvelopeNormalityStatement.{u}`, for an
arbitrary universe `u`. Fix any field `k : Type u`, any group scheme `G` over
`Spec k` that is smooth and affine over the field with connected underlying space,
and any actual representative `D : TorusGeneratedEnvelope G` of the unchanged
`closedTorusEnvelope G`. Then `SubgroupFunctor.range D.inclusion` satisfies the
existing `SubgroupFunctor.IsNormal`. That is, on every scheme over `Spec k`,
reduced or not, conjugation by every point of `G` preserves the points of the
range. The final theorem has no premises beyond the target's. In particular it
assumes no splitness, reductivity, perfectness or characteristic restriction, and
no theorem-valued hypothesis. The axiom report lists only `propext`,
`Classical.choice` and `Quot.sound`.

## Implemented proof

The proof splits on `finite_or_infinite k`. In both cases it applies the published
`TorusGeneratedEnvelope.isNormal_of_algebraicClosure_envelope_eq` (module
`Rational.TorusGeneratedEnvelopeNormalityReduction`) to the supplied `D`. That
theorem needs only smoothness and affineness of `G`, together with the equality

`(closedTorusEnvelope G).baseChange (toAlgebraicClosure k) =
closedTorusEnvelope ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G)`

of subgroup functors. Over the algebraic closure the base-changed `D` represents the
envelope of `G_k̄`. That envelope is normal there, because the actual closed
normalizer contains every rational point and `G_k̄` is reduced. Normality then
descends to `k` along the fpqc morphism `Spec k̄ ⟶ Spec k`. The remaining work is to
supply the envelope equality in each case: the published infinite-field theorem
and the finite-field helper below.

### Infinite fields

The imported theorem
[`torusGeneratedEnvelopeAlgebraicClosureInfinite`](TorusGeneratedEnvelopeAlgebraicClosureInfiniteProof.md) proves
`TorusGeneratedEnvelopeAlgebraicClosureInfiniteStatement.{u}` as
`torusGeneratedEnvelopeAlgebraicClosureInfinite_of maximalTorusBaseChange
maximalTorusConjugacy rationalMaximalTorusConjugateDensity`. The reduction is in
module `Rational.TorusGeneratedEnvelopeAlgebraicClosureInfiniteReduction`. Its
three inputs are published unconditional proofs:

- `maximalTorusBaseChange`: maximality of tori under field extension
  (`Torus.MaximalBaseChangeProof`);
- `maximalTorusConjugacy`: conjugacy of maximal tori over an algebraically closed
  field (`Absolute.MaximalTorusConjugacyProof`);
- `rationalMaximalTorusConjugateDensity`: over an infinite field, density in `G_k̄`
  of the conjugators carrying the base change of a maximal `k`-torus onto base
  changes of closed `k`-tori (`Rational.RationalMaximalTorusDensityProof`).

### Finite fields

The finite case uses two private helpers and a published reduction.

1. `finiteFieldCentralCocharacterEnvelopeNormality` proves
   `FiniteFieldCentralCocharacterEnvelopeNormalityStatement.{u}`. Assume every
   cocharacter of `G` over the finite field is central. Then
   `finiteFieldCentralCocharacterSolvable_of parabolicDynamic finiteFieldQuasiSplit`
   shows that `G` is solvable (`IsSolvableGroupScheme G`). The reduction is in module
   `Rational.FiniteFieldCentralCocharacterSolvableReduction`. Its inputs are the
   published proofs `parabolicDynamic` (Milne 25.1, `Absolute.ParabolicDynamicProof`)
   and `finiteFieldQuasiSplit` (quasi-splitness of connected reductive groups over
   finite fields, `Rational.FiniteFieldQuasiSplit`). The published
   `finiteFieldSolvableEnvelopeNormality`
   (`Rational.FiniteFieldSolvableEnvelopeNormalityProof`) then gives normality of
   `closedTorusEnvelope G` for that solvable `G`.
2. `finiteFieldMaximalTorusTransporter_of`
   (`Rational.FiniteFieldMaximalTorusTransporterReduction`) turns the first helper
   into `FiniteFieldMaximalTorusTransporterStatement.{u}`. That reduction inducts on
   the Lie dimension through dynamic centralizers of noncentral cocharacters.
3. `torusGeneratedEnvelopeAlgebraicClosureFinite` proves
   `TorusGeneratedEnvelopeAlgebraicClosureFiniteStatement.{u}` as
   `torusGeneratedEnvelopeAlgebraicClosureFinite_of maximalTorusBaseChange
   maximalTorusConjugacy` applied to the transporter statement of step 2 (module
   `Rational.TorusGeneratedEnvelopeAlgebraicClosureFiniteReduction`).

### Conclusion

In the finite case the final theorem applies
`D.isNormal_of_algebraicClosure_envelope_eq` to
`torusGeneratedEnvelopeAlgebraicClosureFinite k G`. In the infinite case it applies
the same theorem to `torusGeneratedEnvelopeAlgebraicClosureInfinite k G`.

The two finite-field helpers remain `private`, so the module's only new public
declaration is the target theorem. The infinite-field step imports its public
proof instead of repeating the former private composite. The private helpers
prove published targets with their own proof tasks.

## Provenance

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), Proposition A.2.11, printed pp.477–480 (one-based PDF pp.503–506),
registered as `conrad-gabber-prasad-2015-pseudo-reductive`. The meaning of the
target, and its identification of the source subgroup `G_t` with the fixed
envelope, are recorded in
[`TorusGeneratedEnvelopeNormalityStatement`](TorusGeneratedEnvelopeNormalityStatement.md).
The proof follows the source's deduction of normality from compatibility with field
extension. It splits into the infinite-field and finite-field cases as the source
does. Each case is closed by published Library reductions whose structural inputs
are all published proofs.

The Lean proof itself is an internal composition of these imported declarations. It
adds no new mathematical assertion. Worker 15's public note
`notes/group-schemes/smooth-split-torus-conjugacy-route.md` records the same
infinite-field composite.
