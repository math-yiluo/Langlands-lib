# Dévissage by powers of an invariant ideal

Worker 148. This is internal algebra derived from the existing coaction,
stable-submodule, quotient, invariant-ideal, and short exact sequence
constructions. It does not rely on a geometric descent theorem. The rings
have arbitrary universe `u`, and the coefficient modules have independent
universe `v`.

`FiniteAnnihilatorVanishing t I` is the following condition: for every finite
`B`-module `M` in `Type v` and every `GroupoidCoaction t M`, containment
`I ≤ Module.annihilator B M` implies `OneCohomologyVanishes` for that
coaction. Thus the condition concerns the existing flat-test cocycles and
retains vanishing for modules killed by `I` as an assumption.

`finiteAnnihilatorVanishing_pow` assumes that `B` is Noetherian,
`RingEtaleEquivalenceRelation t`, `IsInvariantIdeal t I`, and
`FiniteAnnihilatorVanishing t I`. It proves the same condition for `I^n`,
for every natural number `n`, by induction.

For `n = 0`, the annihilator contains `1`, so every element of the module is
zero. Tensor induction shows that every tensor is zero, and every cocycle
has the zero primitive.

For the successor step, let `N = I • M`. Invariance of `I` and flatness of
`C` over `B` give stability of `N`. Use the actual restricted and quotient
coactions, with their equivariant inclusion and quotient maps, in
`0 → N → M → M/N → 0`. If `I^(n+1)` annihilates `M`, then `I^n`
annihilates `N`: for a generator `b • m` with `b ∈ I` and `a ∈ I^n`,
`a • (b • m) = (a*b) • m = 0`. Induction on the ideal-generated submodule
extends this equality to every element of `N`. The quotient is annihilated
by `I` because `b • m` lies in `N` for `b ∈ I`. Noetherianity and finiteness
of `M` make `N` finite, and the quotient is finite as a quotient of `M`.
The induction hypothesis gives vanishing for `N`, and the assumed condition
gives vanishing for `M/N`. The existing
`oneCohomologyVanishes_of_shortExact` theorem then gives vanishing for `M`.

`oneCohomologyVanishes_of_le_radical_annihilator` applies the power reduction
when `I ≤ (Module.annihilator B M).radical`. Over a Noetherian ring `I` is
finitely generated. Mathlib's
`Ideal.exists_pow_le_of_le_radical_of_fg` gives a natural number `n` for
which `I^n` lies in the annihilator, so the preceding theorem applies.

Both results are conditional reductions. They establish neither the initial
vanishing condition for modules killed by `I` nor the host geometric
acyclicity theorem.
