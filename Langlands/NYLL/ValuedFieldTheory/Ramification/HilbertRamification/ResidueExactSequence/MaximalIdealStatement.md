# Contracted maximal ideal: statement target (M243.017)

The closed Prop-valued definition
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal_eq_maximalIdealStatement`
states, for `K : Type u`, `{L : Type v}`, fields with `[Algebra K L]` and
`[IsGalois K L]`, and `A : ValuationSubring L`, that the contraction to the
fixed subring of `A`'s maximal ideal is the maximal ideal of that fixed subring.

The source is NYLL commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`,
lines 208–216, declaration line 210. This is the exact elaborated source
telescope, including `[IsGalois K L]`: the original proof uses the maximality
instance M243.016, which has that parameter. The theorem is replaced by a closed
Prop-valued `def` with suffix `Statement`; no proof is provided here.
Universes, binder order, explicit `K`, implicit `L`, and the conclusion are
unchanged. Namespace and imports are adapted, and the module documentation
is narrowed to this target. The unused ambient section variables,
noncomputable section and notation scopes are omitted.

The published NYLL `ResidueExactSequence.Definitions` module supplies the
fixed subring and contracted ideal. The published Library module
`Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal`
supplies `FixedPoints.isLocalRing_subring`, which already establishes the
locality needed to form the right-hand side (the content of M243.007).
The NYLL fixed subring is an abbreviation for
`FixedPoints.subring A (decompositionGroup K A)`, so the instance applies
directly. No new instance is registered.

A later proof child can specialize the existing Library theorem
`FixedPoints.maximalIdeal_subring_eq_comap` and reverse its equality.
That route requires no new proof of M243.016, while the target retains the
source's `[IsGalois K L]` parameter. This statement module does not provide
that proof. Source registered as `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The source copyright and author header is retained, with modifications
recorded there; the Apache-2.0 LICENSE and NOTICE are in `licenses/NYLL/`.
