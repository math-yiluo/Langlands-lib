# Approximation of pure strata: proof

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`, (2.4.1)(i), (ii)(c), (iii) and (2.4.2), printed pp. 65–66 (PDF pp. 77–78).

## Statement

`Langlands.BushnellKutzko.stratumApproximation : StratumApproximationStatement` proves the proposition of the module `StratumApproximationStatement`, unchanged and with no further hypotheses. Over a nonarchimedean local field `F` and a finite-dimensional `F`-vector space `V`, with `F` and `V` in independent universes:

1. every pure stratum `S` has an equivalent simple stratum with the same chain and integers; every such simple stratum `T` has `elementRamificationIndex F T.b ∣ elementRamificationIndex F S.b` and `elementResidueDegree F T.b ∣ elementResidueDegree F S.b`; and a pure stratum `T` with the same chain and integers, equivalent to `S`, is simple exactly when `elementDegree F T.b` is at most `elementDegree F U.b` for every pure stratum `U` with the same chain and integers equivalent to `S` ((2.4.1)(i));
2. for equivalent simple strata `S`, `T` with the same chain and integers and any tame corestriction `s` relative to `F[S.b]/F`, `s(S.b − T.b)` is congruent modulo `𝔓^{1−r}` to an element of `F[S.b]` ((2.4.1)(ii)(c));
3. if `S` is pure with `k₀(S.b, 𝔄) = −S.r` and `T` is an equivalent simple stratum with the same chain and integers, then `T.HasSimpleDerivedStratum (S.b − T.b)`: for every tame corestriction relative to `F[T.b]/F`, the derived stratum of the perturbation `S.b − T.b` is equivalent to a simple stratum over the extension field `F[T.b]` with its integral-closure integer ring ((2.4.1)(iii));
4. every pure stratum has a defining sequence ((2.4.2)).

## Proof

The module `StratumApproximationReduction` proves `stratumApproximationReduction : StratumApproximationReductionStatement`, which derives `StratumApproximationStatement` from six propositions. The theorem applies it to their proofs in the Library:

| Premise | Source | Proof (module) |
| --- | --- | --- |
| `MinimalCriticalExponentStatement` | BK93 (1.4.15) | `minimalCriticalExponent` (`MinimalCriticalExponentProof`) |
| `StratumEquivalenceStatement` | BK93 (1.5.2), (2.1.4) | `stratumEquivalence` (`StratumEquivalenceProof`) |
| `RefinementStatement` | BK93 (2.2.8) | `refinement` (`RefinementProof`) |
| `PureStratumSimpleApproximationStatement` | BK93 (2.4.1)(i), existence with divisibility for the witness | `pureStratumSimpleApproximation` (`PureStratumSimpleApproximationProof`) |
| `SimpleStratumCorestrictionCongruenceStatement` | BK93 (2.4.1)(ii)(c) | `simpleStratumCorestrictionCongruence` (`SimpleStratumCorestrictionCongruenceProof`) |
| `CriticalDerivedStratumStatement` | BK93 (2.4.1)(iii) | `criticalDerivedStratum` (`CriticalDerivedStratumProof`) |

The reduction instantiates `MinimalCriticalExponentStatement` and `RefinementStatement` with the universe of the extension field equal to that of `V`, since the fields there are generated inside `End_F(V)`; the theorem supplies `minimalCriticalExponent` and `refinement` at those universes.

Inside the reduction, (2.4.1)(ii)(c) and (iii) are the premises themselves. Existence in (2.4.1)(i) is the witness of `PureStratumSimpleApproximationStatement`. Divisibility for an arbitrary simple approximation comes from the divisibility of that witness, because equivalent simple strata have the same ramification index and residue degree (`StratumEquivalenceStatement`). A simple stratum has minimal degree because its ramification index and residue degree divide those of every equivalent pure stratum, and `e f = [F[b]:F]` for a generated field. For the converse, let `T = [𝔄,n,r,β]` be pure and not simple, and take a simple approximation `[𝔄,n,−k₀(β,𝔄),γ]` at its critical level. The critical derived stratum and the refinement theorem show that `[F[β]:F]` is the degree of a field properly containing `F[γ]`, so the equivalent pure stratum `[𝔄,n,r,γ]` has strictly smaller degree. Defining sequences are built by strong induction on `n − r`, with (1.4.15) bounding the critical exponent below by `−n`.

The theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
