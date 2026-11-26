# Moderate growth of nested standard constant terms

A continuous function on the quotient by \(U_P(\mathbb A)M_P(F)\) is fixed by \(P(F)\), hence by \(Q(F)\) for \(Q\le P\). The normalized average along \(U_Q(F)\backslash U_Q(\mathbb A)\) is continuous and invariant under the rational parabolic and the adelic radical by `inducingConstantTermCovariance`. These invariances give the left invariance under \(U_Q(\mathbb A)M_Q(F)\).

The proof of `hasHeightGrowth_constantTerm` uses the compact quotient to bound the height of a representative of every class by one constant \(B\). The representatives differ by rational radical points that fix the input function. If the input bound is \(CH(g)^r\), the integrand is bounded by \(CB^rH(g)^r\) by submultiplicativity, and the quotient measure is a probability. `adelicParabolicConstantTermGrowth` uses `hasModerateGrowthFunction_iff_hasHeightGrowth` to pass between this height and the adelic source norm in the moderate-growth predicate.

This is a derived growth and invariance step in the induction of Mœglin–Waldspurger I.3.4, pp. 45–46, and the parabolic quotient formulation of Bernstein–Lapid (8.1), p. 221.

- `moeglin-waldspurger-1995-cuspidal-components`, `ce20e97e0e7b5008124763a26598dd024c66c926069ca07e92aa24afe91999f1`, 05.3_pp_40_48_Cuspidal_components.pdf, I.3.4, pp. 45–46, induction on semisimple rank.

- `bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`, `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`, Bernstein-Lapid--On the meromorphic continuation of Eisenstein series--2024.pdf, (8.1), p. 221.
