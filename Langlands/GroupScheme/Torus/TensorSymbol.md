# Tensor symbol cocycle of a split torus

Let \(F\) be a field and \(T\) a split commutative group scheme over
\(\operatorname{Spec}F\), with actual cocharacter lattice
\(Y=\operatorname{Hom}(\mathbb G_m,T)\). The inputs are an integral
bilinear form \(D\) on \(Y\) and a bimultiplicative pairing \(h\) from
\(F^\times\times F^\times\) to a commutative group \(A\). Lean represents
\(h\) by `Fˣ →* Fˣ →* A`.

`TorusSymbol.cocharacterPoint` evaluates a cocharacter on a field unit
by postcomposition with the cocharacter. At the identity test scheme
over \(\operatorname{Spec}F\), `unitsTensorPointEquiv` combines
`Gm.affinePointsEquiv` with `TorusPointsTensor.tensorPointEquiv`. It sends
the pure tensor of \(a\) and \(y\) to the point \(y(a)\) in the group
`rationalPoints T.toGrp`, with the multiplicative groups written additively.
The scalar ring is `ULift ℤ`, acting through its integer coordinate.

`symbol` uses the inverse of this equivalence in both point variables.
`TensorProduct.tensorTensorTensorComm` regroups
the two unit factors and the two lattice factors. The additive form of
\(h\) and the scalar lift of \(D\) give linear maps on those two tensor
products by the tensor universal property. `TensorProduct.map` applies
both maps, and `TensorProduct.rid` contracts the lifted integer with the
additive coefficient. On pure tensors this contraction becomes an
integer power in \(A\), giving `symbol_cocharacterPoint`.

$$
c_D\bigl(y(a),z(b)\bigr)=h(a,b)^{D(y,z)} .
$$

Tensor additivity in each variable proves `symbol_mul_left` and
`symbol_mul_right`. Tensoring with zero proves `symbol_one_left` and
`symbol_one_right`. The two multiplication laws and commutativity in
\(A\) give the cocycle identity of `normalizedCocycle` for the trivial
action of \(T(F)\).

`Extension` specializes `Langlands.NormalizedTwoCocycle.Extension` to
this cocycle. In product coordinates its multiplication is
\((\alpha,x)(\beta,z)=(\alpha\beta c_D(x,z),xz)\). The inclusion
\(i(\alpha)=(\alpha,1)\), projection \(p(\alpha,x)=x\), and section
\(s(x)=(1,x)\) are `inclusion`, `projection`, and `sectionMap`.
The general extension laws give injectivity, surjectivity, equality of
the inclusion range and projection kernel, and \(p(s(x))=x\).
The trivial action makes the included coefficients central.
The section satisfies \(s(x)s(z)=i(c_D(x,z))s(xz)\).

Assume in addition that \(h(b,a)=h(a,b)^{-1}\).
`commutator_cocharacterPoint` applies
`NormalizedTwoCocycle.Extension.commutator_eq_inl_div` to arbitrary
lifts \(e,f\) of \(y(a),z(b)\). The two pure-tensor evaluations
identify the quotient of opposite cocycle values. Inversion of \(h\)
in the swapped order and the addition law for integer powers then give

$$
efe^{-1}f^{-1}=i\bigl(h(a,b)^{D(y,z)+D(z,y)}\bigr).
$$

The module abstracts the symbol in Brylinski and Deligne,
*Central extensions of reductive groups by \(K_2\)*, (3.9.3),
printed p. 31 (PDF p. 27). Its commutator is the ratio from Proposition
3.13 and Corollary 3.14, printed p. 33 (PDF p. 29). Gan and Gao,
*The Langlands–Weissman program for Brylinski–Deligne extensions*,
§2.6, printed pp. 200–201 (PDF pp. 218–219), give the corresponding
torus product, and §3.3, printed p. 205 (PDF p. 223), gives the
Hilbert-symbol commutator. The tensor construction uses the
bimultiplicativity common to those pairings. The commutator calculation
uses their inversion under exchange in the form of the explicit
hypothesis on \(h\).
