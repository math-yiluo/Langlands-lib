# Integral quadratic forms and bisectors of split cocharacter lattices

## Sources

- Jean-Luc Brylinski and Pierre Deligne, *Central extensions of reductive groups by K2*,
  `brylinski-deligne-2001-central-extensions`,
  SHA-256 `24ea359c677a6c767a5eeeffad7d39f7019d875d3f18c5280f5086414e182ba5`.
  Section 0.N.3 (printed p. 11, PDF p. 7) specifies the polarization. The proof of
  Proposition 3.11 (printed pp. 31–32, PDF pp. 27–28) uses a bilinear form with diagonal
  \(Q\) and computes its symmetrization. Section 6.1 (printed pp. 49–50, PDF pp. 45–46)
  supplies Weyl invariance of the quadratic datum of a split reductive group.
- Wee Teck Gan and Fan Gao, *The Langlands–Weissman program for Brylinski–Deligne extensions*,
  `gan-gao-2018-langlands-weissman-program`,
  SHA-256 `fabbe056bdec2a5d57a22a0d3ad275640d0343c3f71092a7df427f7ebaebe892`.
  Theorem 2.4 in §2.5 (printed p. 199, PDF p. 217) specifies the integral Weyl-invariant
  quadratic datum. Section 2.6 (printed p. 200, PDF p. 218) defines the bisector by its
  diagonal and records its existence and symmetrization law.

## Quadratic datum

For `p : SplitPinning G` over a field \(k\), the lattice \(Y\) is
`cocharacterLattice p.torus`, the group of morphisms from \(\mathbb G_m\) to the pinned
torus. `WeylInvariantQuadraticForm p` contains a Mathlib `QuadraticForm ℤ Y` and the
predicate `IsWeylInvariant p` for the representation
`p.rootDatum.weylGroupCorootRep` of the opposite Weyl group on \(Y\).
The coreflection criterion `isWeylInvariant_iff_coreflection` evaluates this
representation at the individual Weyl generators. The converse uses the identity
and product cases of `RootPairing.weylGroup.induction`. In a product, the cocharacter
representation applies the factors in the order given by the opposite group.
The induction includes the empty root system.

`polarization Q` is Mathlib's `Q.polarBilin`. Its value at \(x,y\) is
\(B_Q(x,y)=Q(x+y)-Q(x)-Q(y)\). The module proves its symmetry, the diagonal
\(B_Q(y,y)=2Q(y)\), and its invariance under the simultaneous Weyl action on both
arguments. The invariance follows by using additivity of the action in the formula
for \(B_Q\).

## Ordered-basis construction

`Bisector Q` consists of a `LinearMap.BilinForm ℤ Y` with \(D(y,y)=Q(y)\) for every
\(y\). The diagonal condition alone gives \(B_Q=D+D^{\mathsf T}\) by
`LinearMap.BilinMap.polarBilin_toQuadraticMap`.

To implement the existence in Gan–Gao §2.6, `Bisector.ofBasis Q e` uses `Matrix.toBilin`
in the given finite linearly ordered integral basis \(e\). Its diagonal entries are
\(Q(e_i)\), its entries for \(i<j\) are \(B_Q(e_i,e_j)\), and its entries for \(j<i\)
are zero. The basis evaluations follow from the inverse relationship between
`Matrix.toBilin` and `LinearMap.BilinForm.toMatrix`.

The proof checks \(D+D^{\mathsf T}=B_Q\) on every pair of basis vectors. On the
diagonal both sides are \(2Q(e_i)\). For distinct indices the upper entry supplies
the polarization, using its symmetry when the indices occur in reverse order.
Equality of the matrices gives equality of bilinear forms. Evaluation at \((y,y)\)
then gives \(2D(y,y)=2Q(y)\). Cancellation in \(\mathbb Z\) proves the bisector
identity for arbitrary \(y\), including when the form is zero or degenerate.

`cocharacterBasisOfSplitting` pulls back the standard integral coordinate basis
through `splitTorus.cocharacterLatticeEquiv` and `cocharacterLattice.congr` for a
supplied isomorphism of the pinned torus with a split torus. Every pinning admits
such an isomorphism. Reindexing the coordinate basis by `Fin n` gives
`exists_orderedCocharacterBasis`. `WeylInvariantQuadraticForm.bisectorOfSplitting`
uses the supplied splitting and the linear order on its factors, and
`WeylInvariantQuadraticForm.nonempty_bisector` gives existence for each pinning.
