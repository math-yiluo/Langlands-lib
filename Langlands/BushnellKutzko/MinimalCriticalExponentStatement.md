# The critical exponent and minimality (T3)

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, Proposition (1.4.15),
printed p. 41 (PDF p. 53), with the setting of §1.4, printed p. 35.

`MinimalCriticalExponentStatement` is an unproved proposition definition.
For every nonarchimedean local field `F`, finite-dimensional `F`-vector
space `V`, hereditary order represented by `𝓛`, and field `E = F[β] ≠ F`
acting on `V` with `Eˣ` normalizing the order, it states:

- the existing `criticalExponent 𝓛 b` is a finite integer `k₀`;
- `𝓛.valuation b ≤ k₀`;
- equality holds if and only if `IsMinimalOver F E β`.

Here `b` is the image of `β : E` under the published field-action
embedding. The generator hypothesis and the condition that `β` is not
in the image of `F` express exactly `E = F[β] ≠ F`. All three type
universes are independent.

The integer witness allows comparison between the already published
`WithTop ℤ` order valuation and the `WithBot ℤ` critical exponent
without imposing an extra finiteness hypothesis. Minimality uses
the constructed integral-closure valuation and residue ring in
`MinimalElement`, exactly the conditions of (1.4.14). No conclusion
of T2 or T3 is a premise.
