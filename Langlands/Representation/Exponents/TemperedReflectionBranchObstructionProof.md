# The selected tempered-reflection obstruction from independent Hom comparison

Author: Worker 2314.

`Langlands.glTemperedReflectionBranchObstruction` proves exactly the published
`Langlands.GLTemperedReflectionBranchObstructionStatement`, imported from
`Langlands.Representation.Exponents.TemperedReflectionBranchObstructionStatement`.
The five universe parameters are `uF`, `uV`, `uM`, `uW`, and `uZ`, independently.
The target and its imported Lean/Markdown pairs are unchanged.

The implemented proof establishes that the statement's sole extra hypothesis,
absence of the specified fine-to-coarse surjection, contradicts its other
hypotheses. It then eliminates this contradiction into the exact existential
conclusion. Thus the theorem proves the selected-branch implication, including
all three clauses for one permutation and its actual conjugacy witness. It does
not implement Silberger's continuation construction or choose a permutation
before deriving the contradiction.

## Implemented proof

Keep the target's complete nested datum, its actual shape equality
`h : (B.flatten Q).flatten R = B.flatten S`, the literal transported objects
`ωB = h ▸ ω` and `vB = h ▸ v₀`, and both surjections onto the specified `J`.
The private `branchTransportFineData` lemma uses equality elimination to prove
irreducibility and Levi cuspidality of this exact `ωB`.

1. The proved `IsLeviTempered.isAdmissible` extracts admissibility of the
   arbitrary coarse input `π` from analytic temperedness. The proved
   `relativeCosocleAdmissibility`, applied to the actual outer surjection,
   gives admissibility of the original target `J`.
2. Apply the proved `fineOppositeJacquetQuotientDetection` with the standard
   and refined clauses of the proved `Parabolic.normalizedSecondAdjointness`.
   Its ambient clause turns the given fine ambient surjection onto `J` into
   an actual nonzero element of

   ```lean
   Hout := (fineTwist T B S ωB vB t).ρ.IntertwiningMap
     (T.normalizedComposedOppositeJacquet B S J.ρ)
   ```

3. Apply the published `relativeCosocleHomComparison` to the entire original
   fine/middle/coarse telescope and the actual outer surjection onto `J`.
   It gives finite dimensionality of `Hout` and

   ```lean
   Hin := (fineTwist T B S ωB vB 0).ρ.IntertwiningMap
     (T.normalizedRefinedOppositeJacquet B S π.ρ)
   ```

   and equality of their complex finranks. The nonzero element of `Hout`
   makes its finrank positive, hence `Hin` also has positive finrank.
4. A nonzero element of `Hin` exists. The same detection theorem, now its
   inner clause at coarse parameter zero, gives a surjective intertwiner
   from precisely

   ```lean
   (innerInduced T B S (fineTwist T B S ωB vB 0)).ρ
   ```

   to `π.ρ`. This contradicts the supplied negation of that existential.
   False elimination closes the original selected-branch conclusion.

Every Hom is between the actual representations displayed above. Detection
uses actual normalized second adjointness and the flattened opposite-Jacquet
comparison, and the Hom comparison uses actual opposite-refinement transitivity
and actual character-twist equivalences. The argument makes no identification
of representations from coordinate equalities. It does not need a separate
zero-specialization identity for a transported complex family: it reaches a
contradiction before constructing any family candidate. In particular it makes
no almost-everywhere-to-zero inference and assumes no continuation certificate.

## Why the Hom comparison is independent of reflection

The proof uses the closed theorem `relativeCosocleHomComparison` from
[`RelativeCosocleHomComparisonProof`](../Classification/RelativeCosocleHomComparisonProof.md).
Its implemented proof has a route independent of quotient reflection:

- `Exponents.wholeInductionLeadingRealBlock` is proved there using the actual
  geometric lemma, `relativeGeometricLeadingCharacterExclusion`, and
  `RelativeCosocleHomIsolationReduction.temperedInductionFiniteGeneration`.
  The latter derives finite generation from normalized-induction finite-length
  preservation and irreducibility, without a fine-support premise.
- `comparisonOfIsolationAndFiniteGeneration` applies the whole-induction
  retraction to the specified actual quotient. Generalized central blocks,
  second adjointness, their actual quotient maps, and fine-Hom factorization
  give the upper finrank inequality. The independently proved
  `fineRelativeHomLowerBound` supplies finiteness and the reverse inequality.

These are the actual bodies of the imported proof and reduction modules; the
Hom comparison does not take reflection as a premise or invoke a proof of it.
The present theorem imports no quotient-reflection proof, Langlands uniqueness
proof, or classification theorem. The full reflection statement is not used
as a premise or intermediate theorem. The proof establishes the contradiction
locally by the two detection clauses and finite-dimensional linear algebra.
It does not add later tempered-induction, cone-extraction or numerical-rigidity
proof units to this task.

## Scope and provenance

All original hypotheses remain: arbitrary actual prime and p-adic field,
compatible topological data, positive rank, the nested refinements and literal
shape transport, irreducible unitary cuspidal fine data, positive internal-root
parameter, irreducible full-center square-integrable middle data and its
surjection, arbitrary irreducible analytically tempered coarse data, every
strictly decreasing real coarse determinant parameter, and both actual
surjections onto the same arbitrary irreducible `J`. No support or constituent
premise is imposed on `π`. All real central shifts and the one-block case are
retained. Induced carrier universes remain those of the published constructions.

The target's source-derived boundary is Silberger, *The Langlands quotient
theorem for p-adic groups*, Math. Ann. **236** (1978), 95–104: supporting data
on p.99, parameter and inverse-conjugation conventions on pp.96–97, and
Proposition 5.8 on p.102. Registered source:
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
Worker 2314 read these passages and the p.101 comparison, and inspected the
p.96 and p.102 formula images. The published scope and continuation notes were
also read. The unrestricted printed Lemma 5.3 and Corollary 5.4 are not used.

This proof is an internal logical assembly of independently published Library
proofs. Its route differs from the original continuation argument. The paired
[statement explanation](TemperedReflectionBranchObstructionStatement.md)
continues to document the source's all-parameter p.102 occurrence and its zero
specialization; this theorem does not claim a universal continuation theorem.

The development Lake build completed with zero errors and zero warnings.
Declaration inspection reports exactly the five independent universe
parameters and only `propext`, `Classical.choice`, and `Quot.sound` as axioms.
Independent semantic review and submission validation remain separate checks.
