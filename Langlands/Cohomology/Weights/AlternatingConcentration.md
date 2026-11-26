# The alternating characteristic function concentrated in one degree

Polynomial algebra for Kottwitz's identity when the cohomology lies in one degree.
All results are proved; namespace `Langlands.Cohomology.Weights`, over any field `L`.

- `alternatingPolynomial_eq_of_eq_one`: if `H i = 1` for every degree `i ≠ k` in
  `Fin (2d + 1)`, then the published
  `alternatingPolynomial d H = ∏ᵢ H i^{(-1)^i}` (in the field of rational functions)
  equals `H k^{(-1)^k}`. The product collapses to its factor at `k`
  (`Finset.prod_eq_single`).
- `eq_pow_natAbs_of_zpow_eq`: if `H` and `P` are monic, `P` has positive degree, `e` is
  `1` or `-1`, and `H^e = P^a` in the field of rational functions, then
  `H = P^{|a|}`. Writing the identity as `H = P^b` with `|b| = |a|`: for `b ≥ 0` it is an
  identity of polynomials (the map to rational functions is injective); for `b < 0` it
  gives `H · P^{|b|} = 1`, whose degree `deg H + |b| deg P` is positive, a
  contradiction. So the sign of `a` is forced and no purity is used.
- `eq_pow_natAbs_of_alternating`: the two together. If `H i = 1` outside degree `k`,
  `H k` is monic, `P` is monic of positive degree and
  `alternatingPolynomial d H = P^a`, then `H k = P^{|a|}`.
- `natDegree_pos_iff_of_alternating`: under the same hypotheses `H k` has positive
  degree exactly when `a ≠ 0`.

## Source

R. E. Kottwitz, *On the λ-adic representations associated to some simple Shimura
varieties*, Invent. Math. 108 (1992), (5.6) and (6.1), printed pp. 663–664, and the
remark on regular highest weight, printed p. 658. Kottwitz excludes cancellation in
(6.1) by purity; when all but one factor of (6.1) is `1` the conclusion follows from the
algebra above alone. Registered `kottwitz-1992-lambda-adic-simple-shimura`, SHA256
`749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
