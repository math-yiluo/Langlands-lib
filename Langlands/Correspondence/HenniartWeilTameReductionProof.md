# The truncated tame reduction of the Weil-side count

`Langlands.Henniart.weilTameReduction.{uK, uW}` proves
`Langlands.Henniart.WeilTameReductionStatement.{uK, uW}`. For
\(n=p^r m\) with \(p\nmid m\), the theorem obtains the conductor count
\(C_K(n,j)=(q_K-1)q_K^j\) for \(j<n e_K\) from the truncated
pure \(p\)-power counts over the tame totally ramified extensions in the
statement. [Statement and notation](HenniartWeilElementaryLayer.md)

The Lean term applies `weilTameAveragingFromOrbitFormulas` to
`tameWeilFrobeniusParametrization`, `weilTameOrbitFormula` and
`weilTameFieldFixedPoint`. The first theorem parametrizes the embedded fields
by inertia cosets. The two formulas express the base count in terms of
Frobenius-stable inertia orbits and each field count in terms of fixed wild
classes. The averaging theorem relates these counts at the same \(j\) and
gives \(\sum_L C_L(p^r,j)=m\,C_K(p^r m,j)\) in `ℕ∞`, with \(L\) running
over the \(m\) embedded tame totally ramified fields of degree \(m\).
[Fixed-cutoff averaging proof](HenniartWeilTameAveragingFromOrbitFormulasProof.md)

The term passes this identity to `weilTameReductionFromAveraging`. For
each \(L\) in the sum, \(e_L=m e_K\) and \(q_L=q_K\) by total
ramification. The bound \(j<p^r m e_K\) therefore gives \(j<p^r e_L\).
The pure-rank hypothesis makes every summand equal to \((q_K-1)q_K^j\).
Cancelling the finite positive multiplier \(m\) in `ℕ∞` gives the result.
[Reduction from the average](HenniartWeilTameReductionFromAveragingProof.md)

The fixed-cutoff comparison comes from Koch (1984), §8, Satz 4 and its
proof, printed pp. 112–113 (`koch-1984-numerical-langlands-remarks`).
The truncation is the form of Proposition `prop:tame` used in the proof of
Proposition `prop:LDcount`(c) of the numerical LLC route note
(`operator-numerical-llc-route-2026-11-16`).
