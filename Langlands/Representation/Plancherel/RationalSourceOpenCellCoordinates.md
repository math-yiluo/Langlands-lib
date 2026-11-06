# Actual source open-cell coordinates

Author: Worker 200.

This derived adapter follows Waldspurger (2003), I.1, second formula (2),
printed p.240 / PDF p.6. It uses the canonical rational-point topology and
Borel measurable space for an actual connected reductive group scheme over
an arbitrary-universe nonarchimedean local field, in any characteristic.
The existing affine and locally finite type hypotheses are explicit;
connected reductivity implies them.

The compact open subgroup K fixes the original ambient, parabolic, Levi
and radical Haar measures by mass one on their compact intersections.
The theorem retains compact-limit stability: the actual dynamic limit
of every p in P intersect K belongs to K. This is the precise premise of
the published normalized semidirect measure comparison; no special-compact
realization is asserted.

`leviModulus` is the existing closed-subgroup radical conjugation modulus
restricted to the actual dynamic Levi. `inverseLeviModulus` is its inverse
as a nonnegative extended-real density. Its measurability follows from
the published open-kernel theorem.

`lintegral_parabolicHaar_of_limit_stable` decomposes the actual parabolic
Haar integral into the canonical Levi-then-radical coordinates. The global
Levi-first theorem derives the actual open embedding, conullness and
opposite-radical right invariance, applies the restricted global formula,
removes inversion by the proved radical inversion invariance and uses this
normalized semidirect comparison.

`lintegral_eq_source_order_of_limit_stable` changes to the source order
U, M, opposite U, with inverse Levi modulus. The proof uses the existing
conjugation change of variables and nonnegative Tonelli interchange.
Every measurable nonnegative extended-real function is allowed.

No whole-group ambient right invariance, Levi right invariance, Iwasawa
factorization or analytic convergence premise is used in this coordinate
formula. Identifying the original gamma with the source Iwasawa-modulus
integral retains the separate existing factorization, compact-limit
stability and Levi right-invariance premises. Same-Levi independence,
a Bochner formula and the Plancherel conclusions remain separate.
