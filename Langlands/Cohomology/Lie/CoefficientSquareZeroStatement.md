# Square-zero target for coefficient-valued Lie cochains

`Langlands.Cohomology.Lie.DifferentialSquareZero K L M` specifies the
square-zero property of the actual coefficient differential constructed in
`Langlands.Cohomology.Lie.CoefficientCochains`. It is a proposition definition;
its proof is a separate obligation.

## Exact scope

The scalar field `K : Type u` has characteristic zero. The Lie algebra
`L : Type v` has the given `LieRing` and `LieAlgebra K L` structures.
The coefficient space `M : Type w` has the given additive commutative group,
`K`-module, `LieRingModule L M` and `LieModule K L M` structures. The three
universes are independent. Neither the Lie algebra nor the coefficient
module is assumed finite dimensional. There is no topology, continuity,
compact-group action or relative subalgebra in this statement.

Write

$$
C^q=L[\mathop{\bigwedge}\nolimits^{\mathrm{Fin}\,q}]
  \mathbin{\longrightarrow_K}M,\qquad
d_q=\texttt{differential q}:C^q\longrightarrow_K C^{q+1}.
$$

The proposition is exactly

$$
\forall q\in\mathbb N,\qquad d_{q+1}\circ d_q=0
  \quad\text{in }\operatorname{Hom}_K(C^q,C^{(q+1)+1}).
$$

The equality is an equality of linear maps, with `0` the zero linear map.
Equivalently, it requires `differential (q+1) (differential q f) = 0`
for every natural number `q` and every cochain `f` of degree `q`, including
degree zero. Both factors are the imported constructed differential, with
its given left coefficient action and bracket; no differential is a
parameter or an additional hypothesis.

## Original source and translation

The original is Henri Cartan and Samuel Eilenberg, *Homological Algebra*
(Princeton University Press, 1956), Chapter XIII, Theorem 7.1 on printed
p.280 (PDF page302) and the coefficient cochain complex and displayed
coboundary formula in §8 on printed p.282 (PDF page304). The retained file is
`literature/Cartan-Eilenberg 1956 original- resolution comparison and derived functors.pdf`,
source ID
`provided-4e029ea5216cb6ce6bfc05060277910b86f223b69bc92c508711e3760612bd4e`,
content SHA256
`1e0915f23ec4a4bd638f469561931f5659a7a47faf92d48468bd290ddd726365`.
Worker 2 independently read the rendered original pages280 and282 and
checked that no source-specific errata file is present in the current
Library.

Theorem 7.1 identifies the exterior construction as a subcomplex of the
normalized standard complex. Section 8 applies `Hom` to this complex with
values in a left module and identifies its cochains with alternating
multilinear functions. Thus its displayed coboundary is a square-zero
operator. The source works over a ring with a free underlying Lie-algebra
module. The present field setting is a specialization: every vector space
admits a basis, without a finite-dimensionality restriction. No
resolution or Ext comparison is included in the Lean proposition.

In zero-based indices the source's operator is

$$
(d_qf)(x_0,\ldots,x_q)=
\sum_{i=0}^{q}(-1)^i[x_i,f(x_0,\ldots,\widehat{x_i},\ldots,x_q)]
+\sum_{0\leq a<b\leq q}(-1)^{a+b}
 f([x_a,x_b],x_0,\ldots,\widehat{x_a},\ldots,\widehat{x_b},\ldots,x_q).
$$

The coefficient action is on the left, the bracket is inserted first,
and the other entries retain their order. The source has one-based
action exponent `i+1` and bracket exponent `i+j`; shifting its indices
down by one gives the displayed signs. The imported
`differential_apply_zero` and `differential_apply_succ` identify the actual
Lean operator with this formula. In the latter theorem, the increasing
pair is `(a,b)=(i,j+1)` with `i ≤ j`, and the sign exponent `i+j+1` is
`a+b`. Its one-half construction of the bracket part is valid here
because the field has characteristic zero.

The new proposition only packages square-zero for that fixed operator.
It does not construct cohomology, prove that the operator preserves a
relative or compact-invariant subspace, or identify any cohomology with
an automorphic realization.

Authorship: Worker 2.
