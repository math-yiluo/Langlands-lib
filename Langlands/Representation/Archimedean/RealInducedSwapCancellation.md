# Finite-support cancellation for recurrent two-block crossings

This internal module derives consequences of the recurrent four-crossing
construction and ambient adjacent-rotation uncertainty. It uses no new
literature assertion. `FiniteModes L μ` means that `μ j = 0` whenever
`L ≤ |j|`, so the possible nonzero modes have absolute index strictly below `L`.

`induced_low_modes` strengthens each actual
induction window from the absolute weight to that weight plus one: the boundary
mode has the wrong parity, using the actual position characters evaluated at
`-1` and the published Fourier parity theorem. `eq_zero_of_induced_finite`
applies the proved ambient
uncertainty theorem to such a high-mode window and finite support on an adjacent
axis, then principal-series uniqueness on the compact subgroup gives zero in
the actual standard module. This argument works in any rank, with both adjacent
axes inside an explicitly supplied three-coordinate block.

In rank four, the first two recurrent crossings transport the first window to
the middle axis by `RealInducedSwapRecurrent.first_window_once`.
A finite `AC` factor with cutoff at most the first weight therefore annihilates
their composite. The alternative `BC,BD` path has the analogous property for the
second window, using `second_window_once`. The multiplier Fourier identity
supplies the finite support. Disjoint commutation gives the corresponding zero
full maps.
A finite last `AD` factor also annihilates the full map when its cutoff is at
most either target induction weight. Equality at the cutoff is included.

These are conditional vanishing theorems for supplied recurrent sequences. This
module constructs no parameter limit and does not prove the full unlinked swap.
