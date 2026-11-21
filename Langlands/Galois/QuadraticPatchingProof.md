# Quadratic patching of continuous semisimple Galois representations

`Langlands.GaloisRepresentation.quadraticPatching` proves
`Langlands.GaloisRepresentation.QuadraticPatchingStatement` with independent
base field, coefficient field, and carrier universes. The construction and
comparison follow the degree-two case of Sørensen, *A Patching Lemma*, §1,
Definition 1 and Lemma 1, author manuscript pp. 1–5, and Harris–Taylor,
*The Geometry and Cohomology of Some Simple Shimura Varieties*, Theorem VII.1.9,
pp. 230–231. The finite-dimensional span argument below implements the
disjointness and intertwiner-detection steps. [Sørensen's author manuscript](https://mathweb.ucsd.edu/~csorense/patch.pdf)

## Common algebraic closure and finite-dimensional spans

For each finite Galois intermediate field \(E\), write \(H_E\) for its fixing
subgroup in the absolute Galois group of \(F\). The proof chooses an
\(E\)-algebra isomorphism from `AlgebraicClosure E` to `AlgebraicClosure F`.
`toFixing` identifies the absolute Galois group of \(E\) with \(H_E\). It is
continuous by restriction along the inverse closure embedding, and its inverse
is continuous by compactness of the absolute Galois group and Hausdorffness of
the fixing subgroup. The restriction comparisons for field inclusions and
automorphisms identify compositum compatibility on \(H_E \cap H_N\) and
Galois invariance under conjugation. `specifiedPullbackEquiv` uses the
published `pullbackAlongClosureEquiv` to carry actual linear intertwiners
between these descriptions and the Library's chosen pullbacks.

For an action \(r\) of \(H_E\) in a finite-dimensional endomorphism algebra,
`exists_stable_span` chooses a finite Galois \(M\) containing \(E\) for which
the dimension of the span of \(r(H_M)\) is minimum. Every finite Galois field
containing \(M\) gives the same span by inclusion and the dimension bound.
For \(N\) disjoint from \(M\), set \(K = H_N\) and \(U = H_M\).
Galois correspondence gives \(K U = \Gamma_F\), hence
\(H_E = (K \cap H_E) U\). Since \(K \cap U = H_{NM}\), the span on
\(K \cap U\) equals the span on \(U\).
Left multiplication by \(r(k)\) for \(k \in K \cap H_E\) consequently puts
every \(r(ku)\) in the span on \(K \cap H_E\). The same argument applies to
a pair of actions in a product of endomorphism algebras. For an invertible
linear map \(e\), the equation \(e x e^{-1} = y\) is linear in \((x,y)\),
so agreement on the span detects the full intertwining equation.

## The quadratic extension

The abundance hypothesis at a single finite place outside \(S\) gives an
auxiliary field disjoint from any prescribed finite Galois field. Take an
initial auxiliary field \(E_0\), its action \(r\), and a span-stabilizing field
\(M\) for \(r\). For an auxiliary \(N\) disjoint from \(M\), transport the
\(H_N\)-action to the carrier of \(r\) by the compositum intertwiner. Choose
\(t \in H_N \setminus H_{E_0}\) and let \(T\) be its transported operator.
The two actions agree on \(H_{E_0} \cap H_N\), so \(T^2 = r(t^2)\).
Galois invariance supplies a linear equivalence implementing conjugation by
\(t\) on the first action. With that equivalence, the equation
\(T r(h) = r(tht^{-1}) T\) is linear in \(r(h)\). It holds on
\(H_{E_0} \cap H_N\) by multiplication in the transported action, and the
span equality extends it to \(H_{E_0}\).

`quadraticExtend` uses \(r(h)\) on the first coset and \(r(h)T\) on \(ht\).
The conjugation and square equations verify multiplication in the four coset
cases. This action agrees exactly with \(r\) and recovers the transported
\(H_N\)-action on both cosets. The operator \(T\) makes the constituent choices
of Sørensen's Steps 1 and 5 simultaneously. To see the relation, conjugation
by \(t\) permutes the \(H_{E_0}\)-isotypic components in orbits of size one or
two. On a two-element orbit \(T\) exchanges the two components and its square
determines the return operator from the forward one. On a fixed irreducible
type, Schur's lemma and a scalar square root give a normalized cyclic
intertwiner whose square is the action of \(t^2\). Dividing \(T\) by this
operator on the irreducible factor leaves an operator on the multiplicity
space whose square is the identity. Its \(+1\) and \(-1\) eigenspaces give
the two quadratic twist multiplicities. The Lean proof constructs \(T\)
directly on the full carrier.

## All auxiliary fields and uniqueness

Choose \(E_1\) disjoint from \(M\), and let \(a\) be the common extension
for \(E_0\) and \(E_1\). For \(N\) disjoint from \(M E_1\), construct the
common extension \(b\) for \(E_0\) and \(N\). Composing the intertwiners
from \(a\) to \(R(E_1)\), across the compositum, and from \(R(N)\) to \(b\)
gives one linear map intertwining \(a\) and \(b\) on \(H_{E_1 N}\).
The subgroup product calculation `inf_sup_eq_top` gives
\(H_{E_1 N} H_M = \Gamma_F\). Both extensions equal \(r\) on \(H_{E_0}\),
so the span argument makes this same map commute with \(r\) there.
The two subgroups \(H_{E_0}\) and \(H_{E_1 N}\) generate \(\Gamma_F\),
yielding an equivalence of the extensions and hence the desired
intertwiner on \(H_N\).

For any auxiliary \(E\), stabilize the span of the paired actions
\((a|_{H_E}, R(E))\) at a finite Galois field \(L\) containing \(E\).
Choose \(N\) disjoint from \(M E_1 L\). The preceding comparison and the
given compositum compatibility supply an intertwiner on \(H_{EN}\).
Applying the linear equation on the paired span proves that this map
intertwines on \(H_E\). For uniqueness, stabilize the paired span of the
two candidate actions on \(\Gamma_F = H_F\). Choose one auxiliary field
disjoint from its stabilizing field and compose the two equivalences with
the prescribed action there. The paired span promotes that map to an
equivalence on \(\Gamma_F\).

The patch has the original carrier of \(R(E_0)\), which gives the rank
equality. Its restriction to the open subgroup \(H_{E_0}\) is continuous
in the stated coefficient module topology. Continuity at the identity
there gives continuity on the whole Galois group. Semisimplicity on
\(H_{E_0}\) follows by reindexing along `toFixing`, and
`Langlands.finiteIndexSemisimplicityAscent` gives semisimplicity of the
extension in characteristic zero. The final restriction equivalences and
uniqueness equivalence use the published `FiniteRepresentation.Equiv`.
