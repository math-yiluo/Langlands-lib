# Reduction of critical-level approximation to a maximal generated field

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`, reduction to a maximal generated subfield in the opening proof of (2.4.1)(i), printed p. 66 (PDF p. 78). The theorem below formalizes that reduction in the Library's indexed-chain model.

`MaximalCriticalApproximationStatement` restricts the witness form of pure-stratum approximation to inputs with `k₀(β) = −r` whose generated field has degree equal to `dim_F V`. It otherwise has the same assertions: a simple equivalent on the same chain and at the same integers, with the two divisibilities for that witness. `PureStratumApproximationMaximalReductionStatement` says that this restricted proposition implies `CriticalPureStratumSimpleApproximationStatement`. It does not prove the full-degree case.

## Implemented proof

For a pure critical input with element `β`, take `E = F[β]` and the regular multiplication endomorphism `b` on the field line `E`. Its generated algebra is the image of `E` under the regular representation, so its degree is `dim_F E` and it normalizes the line chain of uniformizer powers. Choose a relative splitting basis of the original chain, with uniformizer shift `d > 0`; the diagonal `Δb` is `β`. The valuation and critical-exponent dilation lemmas give `n = d*(-m)` and `r = d*(-k)`, where `m` and `k` are respectively the line valuation and line critical exponent of `b`. Finiteness of both follows from purity and criticality of the input. Thus the pure line stratum at integers `-m,-k` is at its critical level, with full generated-field degree.

Apply the supplied full-degree assertion on the line. Transport the simple line witness `γ` back by `Δ`, giving a pure stratum on the input's chain and at its integers: normalizing units and valuation transport, and multiplication by positive `d` preserves the strict critical bound (also when the line exponent is bottom). Congruence lifts because line depth `k` corresponds on the diagonal to ambient depth `d*k = −r`. The ramification index and residue degree of each line element coincide with those of its diagonal by field-isomorphism invariance. Transport the two divisibilities of the line witness separately.

No (2.4.1)(iii) premise or conclusion is used. The Lean proof has finite heartbeat limits for elaboration with the generated field's instances.
