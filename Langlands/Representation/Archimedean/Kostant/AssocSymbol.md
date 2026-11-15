# Symbol data for an associative algebra with a finite basis

`A` is a unital associative `K`-algebra with a basis `b` indexed by `B`, regarded as a Lie
algebra under the commutator. Put `S = K[X_c]` (`SymRing`) and `R = S[x_c]` (`CoordRing`).

* `der a` is the `S`-derivation of `R` given by right multiplication:
  `x_c ↦ ∑_d (b_d a)_c x_d`.
* `der_lie` shows that `a ↦ der a` turns commutators into commutators. Both sides are
  derivations, so it suffices to compare them on the variables, which uses
  `∑_d (b_f a)_d (b_d a')_c = (b_f a a')_c`.
* `rho` is the resulting Lie algebra map into `End_K(R)`.

`ideal` is the ideal of the point `x = 1` and `eval1` is evaluation at that point. With
`lin = ∑_c X_c (x_c - 1_c)` this gives `symbolData`. Its linear symbol is
`ξ(a) = ∑_c a_c X_c` (`symbolData_ξ`), so `ξ(b_c) = X_c` (`symbolData_ξ_basis`).
