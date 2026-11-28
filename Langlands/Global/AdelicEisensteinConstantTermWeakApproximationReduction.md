# The constant term on cones from the remainder of the weak constant term

Module `Langlands.Global.AdelicEisensteinConstantTermWeakApproximationReduction`, namespace
`Langlands.Global`. It proves

```
theorem eisensteinConstantTermWeakApproximation_of_remainder
    (h : EisensteinWeakConstantTermRemainderStatement) :
    EisensteinConstantTermWeakApproximationStatement
```

This is a reduction: it does not prove `EisensteinConstantTermWeakApproximationStatement`
(module `Langlands.Global.AdelicEisensteinConstantTermWeakApproximationStatement`) without the
premise `EisensteinWeakConstantTermRemainderStatement` (module
`Langlands.Global.AdelicEisensteinWeakConstantTermRemainderStatement`), which is not proved in
this module.

## Proof

Fix the data of the target, including `δ > 0`, the threshold `t` and the compact `Ω`.

1. Put `t' = min(t, 1)` (as an element of `ℝ≥0ˣ`), so that `t' ≤ t` and `t' ≤ 1`. The weak
   chamber of threshold `t` is contained in that of threshold `t'`.
2. Apply the premise to the same data with the threshold `t'`. It gives `ε > 0`, `m`, `B` and
   triples `(c_q, L_q, Φ_q)` with items 1–6 for the chamber of threshold `t'`, and for each
   `x ∈ C` the properties 7a–7c of the remainder
   `r_x = E(i e(x))_Q − ∑_q c_q(x) Φ_q(x, ·)`: a unitary central character, the bound
   `‖r_x(b ω)‖ ≤ B δ(b)^{1/2} σ(b ω)^m` on the chamber of threshold `t'`, and
   `HasConeShiftEquations F G T i ν T₀ j J δ ε m r_x`.
3. Choose `α₀ ∈ Δ \ J` (the target assumes one exists). `ConeShiftDecay.exists_coneBound`
   (module `Langlands.Global.AdelicConeShiftEquationDecay`), applied with `J`, `α₀`, `δ`, `ε`,
   `m`, `B`, `t' ≤ t`, `t' ≤ 1` and `Ω`, gives `B'`, independent of `x`.
4. The target's witnesses are `ε δ / 4`, `m`, `max(B, B')` and the same triples. Items 1–5 are
   those of the premise. Item 6 for `b` in the chamber of threshold `t` is item 6 of the premise
   for the larger chamber of threshold `t'`, with `B ≤ max(B, B')`. Item 7' is the conclusion of
   `exists_coneBound` for `f = r_x`, with `B' ≤ max(B, B')`.

The proof uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Source

P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered as
`delorme-2023-spectral-theorem-langlands` (published PDF): the bound for `φ_Q − φ^w_Q` in the
proof of Lemma 5.1 (pp.18–19), the passage to the cone in Lemma 5.2 (p.19), carried out for
Eisenstein series as in the proof of Lemma 5.3 (pp.19–20). The premise collects the inputs of
that bound: the weak constant term (4.3) (p.16), the exponents (4.4) (p.17) with their strictly
negative real parts on the cone, and the polynomial bound (5.1) (p.19).
