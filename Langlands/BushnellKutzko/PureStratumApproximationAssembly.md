# The pure-stratum approximation theorem from five named premises

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`, proof of (2.4.1)(i), printed pp. 66–71 (PDF pp. 78–83).

This module does **not** prove the Library target `PureStratumSimpleApproximationStatement` outright. It proves that the target follows from five named premises, none of which the Library proves. Each premise is a closed proposition over every nonarchimedean local field `F` and finite-dimensional `F`-space `V`. For any field `E` acting on `V` it uses the Library's tame corestrictions, derived strata (`Stratum.IsDerivedStratum`) and fundamental, split and nonsplit predicates.

## Premises

- `TopNonsplitPremise` ((2.3.11)) and `NonsplitRefinementPremise` ((2.3.4)) are defined in `PureStratumApproximationSeed`.
- `SplitObstructionPremise` is (2.3.12), printed p. 61. If `S.IsDerivedStratum E b s D` and `D` is split, then `F[S.b + b]` is not a field.
- `ChainImprovementPremise` is (2.4.5), printed pp. 67–69, in a conjugation-free form. Let `S` be simple with derived stratum `D` of `β − S.b`. Suppose some element of `D.coset` differs from a scalar of `E` by a nilpotent element. Then some simple `T` has `β ∈ T.coset`, `T.r · e(S) < S.r · e(T)`, and the same ramification index and residue degree as `S`.
  - Taking the scalar `0` covers a non-fundamental `D`; a nonzero scalar covers the scalar-fundamental case. A nilpotent difference from a scalar of too small valuation is impossible inside `D`'s coset, so the hypothesis is exactly BK's "non-fundamental or scalar fundamental".
  - The source conjugates `β` to `β″`. Conjugating the chain and `γ″` back instead gives the same conclusions about `β`.
  - The source's clause (ii), that `L'` is an `𝔄″`-lattice, served its compactness argument. It is replaced here by `PureStratumApproximationBoundedApproximation`. Clause (v) is not needed.
- `DegreeIncreasePremise` is the final step of the proof, printed pp. 70–71. Let `S`, `β` and `D` be as above, with `D` fundamental, not split, and not scalar fundamental in the same sense. Then there are strata `T` and `U` with:
  - a common chain (`U.chain = T.chain`), a common level (`U.n = T.n`) and `U.r = T.r − 1`;
  - `T` and `U` both simple, with `β` in both cosets;
  - `k₀(U.b) = −T.r`;
  - `[F[S.b]:F] < [F[U.b]:F]`;
  - the ramification index and residue degree of `F[T.b]` dividing those of `F[U.b]`.

  The premise does not require `T.b = S.b`. In the source, this step applies (2.3.4) over `E`, lifts the resulting order to `A`, applies (2.2.8) to get a refinement `γ` of the old generator `γ_m`, and uses (2.2.1) to get a conjugate `β'` of `β_m` congruent to `γ` (printed p. 70). On printed p. 71 it then conjugates all objects, including the order, `γ` and the old generator `γ_m`, by one `g ∈ G` so that `β'` becomes `β`. So in the premise `T.b` is the conjugated old generator `g γ_m g⁻¹`. Conjugation preserves the degree and invariants of the generated field. Hence `[F[T.b]:F] = [F[S.b]:F] < [F[U.b]:F]`, and by (2.2.8) the invariants of `F[U.b]` are those of `F[T.b]` times those of `F[T.b, α]` over `F[T.b]`. Only the strict comparison with `S.b` and the two divisibilities with divisor `T.b` are recorded. A form keeping `T.b = S.b` exactly is false in general: there is a counterexample over `F = 𝔽₁₁((π))` in which no such pair `T`, `U` exists with the original generator.

  "Fundamental and not split" is the source's meaning of nonsplit ((2.3.3), printed p. 58). The Library's `Stratum.IsNonsplit` additionally records the factorization, which is why the weaker hypothesis is used here.

## Implemented proof

`maximalCriticalAssembly` proves `MaximalCriticalApproximationStatement`, the critical full-degree case, from the five premises. Let `S = [𝓛,n,r,β]` be such a stratum.

1. `candidateSeed` gives a candidate: a simple stratum with `β` in its coset and generated field of smaller degree. `optimalCandidate` then gives a candidate `T₀` of maximal degree and minimal normalized depth.
2. The derived stratum `D` of `β − T₀.b` is constructed from the Library's `subfieldChain`, a tame corestriction from T1 `tameCorestriction`, and the image property of `s` on filtrations. `valuation_subfieldChain` and `mem_subfieldChain_endFiltration_iff` identify the derived chain's filtration with the original one.
3. If `D` is non-fundamental or scalar fundamental, (2.4.5) gives a candidate of the same degree (`e·f` is the degree) and smaller normalized depth. This contradicts the choice of `T₀`.
4. Otherwise `D` is fundamental (take the scalar `0`). It is not split, since `F[β]` is a field and (2.3.12) applies. The final step gives `T` and `U`. If `[F[U.b]:F] < dim V`, `U` is a candidate of larger degree, a contradiction.
5. So `F[U.b]` has full degree. `maximalSimpleReflection` makes `[U.chain, U.n, U.r, β]` simple, and T5 `stratumEquivalence` gives `k₀(β) = k₀(U.b) = −T.r` on that chain, with equal invariants. Both chains are normalized by `F[β]ˣ`, and `V` is a line over `F[β]`, so `lineChainTranslation` makes `U.chain` a translate of `𝓛`. Translation invariance of `k₀` gives `T.r = r`. Equal periods and `pureCosetSlope` give `T.n = n`.
6. `chainTranslation` moves `T` to `𝓛`, giving the simple witness `[𝓛,n,r,T.b]` equivalent to `S`. Its element is the generator `T.b` returned by the final step, not `T₀.b`. Its invariants divide those of `F[U.b]` by the premise, and T5 identifies these with those of `F[β]`.

`pureStratumApproximationFromPremises` proves `PureStratumApproximationFromPremisesStatement`: the five premises imply the exact Library target. It composes the assembly with `pureStratumApproximationMaximalReduction` and `pureStratumApproximationCriticalReduction`. No aggregate T7 and no (2.4.1)(iii) assumption is used. The assembly proof uses finite heartbeat limits for elaboration with generated-field instances.
