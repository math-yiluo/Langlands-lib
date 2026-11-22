# Archimedean differentiation of the unipotent constant term

`AdelicUnipotentConstantTermDifferentiationStatement` concerns a smooth connected affine unipotent group \(U\) embedded as a closed subgroup of a smooth affine group \(G\) over a number field \(F\), with \(G\) locally of finite type. Fix an open subgroup \(L\) of \(G(\mathbb A_f)\). Let \(f\) be continuous on \(G(\mathbb A)\), smooth on each archimedean slice, left invariant under \(U(F)\), and right invariant under \(L\).

For every archimedean tangent direction \(X\) at the identity, the derivative of \(t \mapsto f(xt)\) at \(t=1\) is continuous, smooth on each archimedean slice, and has the same two invariances as \(f\). The constant term on the actual quotient \(U(F)\backslash U(\mathbb A)\), with normalized probability Haar measure, is smooth on each archimedean slice. Its derivative in direction \(X\) is the constant term of the derivative of \(f\). In particular, if the constant term vanishes identically, it still vanishes after any finite iteration of these derivatives.

The proof writes the normalized quotient integral as an integral over a relatively compact Borel fundamental domain and views the resulting finite measure on the domain's compact closure. At a fixed finite coordinate, the integration parameter maps continuously into \(G(F_\infty)\times(G(\mathbb A_f)/L)\). The open subgroup makes the finite quotient discrete. The smooth compact manifold integral formula then gives both smoothness and differentiation under the integral.

This implements the differentiation under the unipotent average used in Mœglin–Waldspurger, §I.2.10, pp. 30–33. It also supplies the differentiation step for the smooth constant terms in Bernstein–Lapid, §7.1, pp. 210–211.
