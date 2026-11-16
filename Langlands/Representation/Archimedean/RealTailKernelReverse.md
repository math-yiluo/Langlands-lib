# Reverse preservation of an ascending induction tail kernel

This is a derived supporting result about the actual compact-finite standard modules and Frobenius operators in the Library. Its inputs are the proved integral landing theorem, the mirror and high-mode transposition theorems, the character-induced pushforward construction, and compact induction-in-stages slices. No external literature theorem is asserted.

Let `c` be a real character, `d` a complex character datum with positive absolute weight `L`, and `sb` an arbitrary internal parity. Use the published ascending characters `b = chiB d sb` and `a = chiA d sb`, with exponents `d.exponent - L/2` and `d.exponent + L/2`, and write `dP` for the positive-weight induction datum. The three character lists are

- `X = [c,b,a]`, with tail `D1 : X → [c,induced dP]` at position one;
- `Y = [b,c,a]`;
- `Z = [b,a,c]`, with tail `T0 : Z → [induced dP,c]` at position zero.

The local `kernel_step` proves that swaps `Q1 : X → Y` and `Q2 : Y → Z` carry `ker D1` into `ker T0`. Both swaps are actual `blockFrobMap` operators supplied by valid Frobenius data. Their symmetry signs are `sigma0 b c` and `sigma0 a c`, respectively, and their recurrence parameters are `c.exponent - b.exponent + 1` and `c.exponent - a.exponent + 1`. The multiplier data, symmetry and recurrence requirements remain explicit; the theorem does not assert an invertible or surjective exchange.

The implemented proof first uses the tail coefficient formula to show that every mode of `z ∈ ker D1` of absolute value at least `L` vanishes along rotation one. Modes on the wrong parity class vanish by sign equivariance; the reducibility parity excludes the boundary of the tail support. It applies `Q1` and `Q2`, then projects onto the high modes along rotation zero using `dataG0`.

The raw reflection `reflect F x = F (mirrorUnit * x)` exchanges the two rotations with the same angle. It preserves continuity and right compact finiteness, the latter by containment of orbit spans in a linear-map image. The high projection after reflection has the sign equivariance of `[cPR,induced d]`, twisted by `sgnDet^sb`, where `cPR` has parity `(c.parity + sb) mod 2`. `reflected_sign` proves this directly by conjugating sign diagonals and comparing their three sign powers. The parity and symmetry lemmas put the two reflected multipliers in precisely the classes required by `RealSwapFLanding.highModes_eq_zero`. The landing premise is discharged by `characterFirst_of_inducedFirst RealSwapLandingIntegral.inducedFirst`. Reflecting the resulting high-mode vanishing back, and using the induced target's low-mode cutoff, proves the tail map is zero by Fourier uniqueness.

`kernel_step_inStages` proves the same kernel containment with arbitrary surrounding lists `pre` and `post` in rank `n`, assuming `realRank pre + 3 + realRank post = n`. All four ambient Frobenius data are inputs, at positions `realRank pre` and `realRank pre + 1` as appropriate. The compact-slice commutation theorem from `RealTailKernelInStages` identifies every sliced ambient composition with the local one. Slices of the zero source tail vanish, so the local result and detection of zero by all compact slices prove the ambient conclusion.

`RealTailKernelReverseStatement` is the universal proposition for this ambient result; `realTailKernelReverse` proves it. Positive absolute weight is required. The construction supplies no zero-weight argument, nonvanishing or range identification, heavier replacement image, or full two-induction-block filtration.
