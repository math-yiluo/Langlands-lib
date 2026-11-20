# Inducing data for the real generic unitary dual

The predicates encode the block lists underlying the basis in Badulescu–Renard, *Unitary dual of GL(n) at archimedean places and global Jacquet–Langlands correspondence* (2010), Theorem 8.2, p. 1131 (PDF p. 18, `badulescu-renard-2010-unitary-dual`). Definition 7.1, pp. 1129–1130 (PDF pp. 16–17), writes the basis elements as `u(δ, 1) = δ` and `π(δ, 1; α) = ν_δ^α δ × ν_δ^(−α) δ` for unitary square-integrable-modulo-center `δ` and `0 < α < 1/2`. Proposition 9.4, p. 1133 (PDF p. 20), identifies `ν_δ` with `|det|` over `ℝ`.

`IsRealUnitaryDiscreteBlock` selects the Library's rank-one character blocks with real exponent zero and its rank-two induced blocks with positive weight and real exponent zero. These describe the two cases `D₁` and `D₂` in §9.2, pp. 1132–1133 (PDF pp. 19–20). The rank-two parameter `η(x,y)` has weight `x − y > 0` and exponent `(x + y)/2`. The real part of the exponent is zero for a unitary block because its positive scalar central character has modulus one.

`IsRealGenericUnitaryInducingFactor` describes a singleton unitary block or the ordered pair of determinant twists of one unitary block, using the Library's existing `realBlockTwist`. The predicate `IsRealGenericUnitaryInducingData` concatenates these lists in the order of the factors of a product. An empty product has the empty list. These are predicates on inducing data. The theorem in this module addresses only the exponents of lists satisfying the predicates.

`IsRealGenericUnitaryInducingData.exponent_bound` finds a factor containing a given block. The exponent of a singleton factor is zero. In a pair, `realBlockExponent_twist` gives `α` and `−α` and hence absolute value `α < 1/2`.
