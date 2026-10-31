# Assembly from a concrete same-coefficient paired matrix comparison

Worker 396. Internal derived assembly adapter for the positive-rank part of the
actual matrix functional-equation comparison. Field and representation-carrier
universes remain independent.

`NormalizedFunctionalEquation.of_const_mul` cancels a common nonzero complex
scalar from both rational functions in the normalized equation. At any point
where the two unscaled reduced denominators are nonzero, multiplying by a
constant polynomial preserves regularity. The scaled equation therefore
applies at that same point, both evaluations factor by the scalar, and
nonzero scalar cancellation yields the unscaled equation. The proof does
not assume equality of reduced denominator polynomials, require nonvanishing
of unreduced polynomial presentations, or restrict the original domain.

`PairedMatrixBlockComparison` records the precise simultaneous scalar integral
comparison still needed from the Fourier calculation. For each original actual
model vector `w`, it requires a full-matrix Schwartz test `Phi`, one actual
bi-smooth coefficient `f` of the original specified model representation, and
one complex number `C != 0`. On a right half-plane,

```text
Z(Phi, s + r/2, f) = C * originalBlockZero(w, s).
```

For every actual plus-transpose Fourier partner `PhiHat` of `Phi` with the
same supplied additive Haar measure, it also requires a right half-plane on
which

```text
Z(PhiHat, s + r/2, coefficientIota(f)) = C * genuineDualBlockZero(w, s).
```

The same actual `f` and same `C` occur in both identities. The block expressions
are literally `unequalRankIntegralAt 0 (r-0-1)` and
`dualUnequalRankModelIntegralAt hrpos 0 (r-0-1)` with the actual canonical
constant-one second model vector. The latter retains the complementary
rectangular block, unsigned long Weyl first dual, reversed character and
actual block Weyl right translate. Both use the constructed compatible
quotient measure, and the additive measure `nu` is unchanged. The predicate
asserts only these equalities of scalar integrals on half-planes; it does
not assume a normalized equation, rational continuation, or gamma conclusion.

`rankOneGammaFactor_of_pairedMatrixComparison` proves the full positive-rank
symmetric gamma conclusion from that concrete comparison and the original
hypotheses of the parent statement. It derives `PDual != 0` from the actual
normalized-generator premise. For each original `w`, the separately established
OriginalBlockZero/DualConvergence/ComplementaryContinuation results give both
literal block continuations `R` and `Rd`. The supplied matrix data give an
actual Fourier partner and matrix continuations `RM` and `RMd` for the selected
actual coefficient. The comparison identities and uniqueness of rational
continuation force

```text
RM = C * R,    RMd = C * Rd.
```

The actual matrix normalized equation thus holds for the scaled pair, and
the cancellation lemma gives the equation for `R` and `Rd`. Published
PositiveAssembly then supplies all blocks, every compatible quotient measure,
all nonzero functional pairs, the existence clauses and the unchanged rational
gamma expression on its full reduced-denominator domain. The supplied
self-dual additive measure is retained throughout.

No analytic premise beyond the parent matrix data is added by this assembly
argument, and no irreducibility, finite length, model equivalence, selected
factor certificate or multiplicativity is assumed. All reused mathematical
steps are published or included as unchanged separately submitted pairs.
No new original-source transcription is asserted. The concrete predicate
`PairedMatrixBlockComparison` remains an explicit unresolved Fourier-extraction
hypothesis: this module does not establish it or the closed parent theorem.
