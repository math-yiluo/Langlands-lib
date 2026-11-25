# Short exactness of the actual absolute-Galois character functor

`Langlands.GroupScheme.MultiplicativeTypeAbsoluteExactnessStatement.{u}`
declares the short-exact-sequence clause for the specific functor
`MultiplicativeTypeGroup.characterFunctor`. This file supplies a proposition
declaration; it is proved as `multiplicativeTypeAbsoluteExactness` in
[`MultiplicativeTypeAbsoluteExactnessProof`](MultiplicativeTypeAbsoluteExactnessProof.md).

## Groups, morphisms and characters

For every field `k : Type u`, let `N`, `E` and `Q` be objects of
`MultiplicativeTypeGroup k`, and let `i : N ⟶ E` and `q : E ⟶ Q`.
These are actual commutative group schemes over `Spec k`, with all their
ground-field group-scheme homomorphisms. Each satisfies the existing
`IsMultiplicativeType` predicate: after some field extension it is
isomorphic to the diagonalizable group of a finitely generated abelian
group. The predicate supplies no separable or finite splitting extension.
The statement requires no chosen splitting field or models.

Write `Ω = SeparableClosure k` and
`X = MultiplicativeTypeGroup.characterFunctor k`. The objects of the
sequence

```text
0 → X(Q) --X(q)→ X(E) --X(i)→ X(N) → 0
```

are the actual groups `Hom(H_Ω, Gm_Ω)`, with their canonical
absolute-Galois transport action. They lie in the published category
`FGDiscreteGaloisModule.{u,u} k`: finitely generated integral modules with
open vector stabilizers for `Aut_k(Ω)` with the Krull topology. Open
stabilizers express continuity for the discrete module topology.

In Lean, the contravariant maps are `X.map q.op` and `X.map i.op`.
`FGDiscreteGaloisModule.hom` exposes their underlying equivariant integral
linear maps, named `pullQ` and `pullN` in the statement. The published
`MultiplicativeTypeGroup.characterFunctor_map_apply` identifies their
values with precomposition by the actual base changes of `q.hom` and
`i.hom`. The maps are already equivariant morphisms of the discrete Galois
module category, so equivariance requires no additional premise or clause.

## The equivalence

The left side asserts that `i` is a closed immersion and that `q` is the
represented fppf quotient by the range of `i`. Precisely, it is

```text
IsClosedSubgroup (CommGroupScheme.groupHom i.hom)
  ∧ RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (CommGroupScheme.groupHom i.hom))
      (CommGroupScheme.groupHom q.hom).
```

The published quotient predicate says that the underlying scheme map of
`q` is flat, surjective and locally of finite presentation, and that its
actual scheme-theoretic kernel inclusion has the same range as `i` on
every test scheme over `Spec k`. Together with the closed immersion,
this identifies `N` with the full kernel and `Q` with the fppf sheaf
quotient. It uses nonreduced test schemes and allows nonsmooth kernels.

The right side is injectivity of `pullQ`, `Function.Exact pullQ pullN`,
and surjectivity of `pullN`. Here exactness means that a character of
`E_Ω` pulls back to zero on `N_Ω` if and only if it is the pullback of a
character of `Q_Ω`. These conditions express the displayed short exact
sequence of the actual discrete Galois modules. Its maps are additive
and integral linear by their construction.

No equation `i ≫ q = 0` is assumed separately: each side of the
equivalence enforces the trivial composite. No smoothness, connectedness,
reducedness, perfectness, freeness or characteristic restriction is
imposed. Torsion characters, including characteristic torsion, are
included. The sheaf quotient is not replaced by surjectivity on each test
scheme's group of points.

## Source and provenance

The original is J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

- Section 12.g, printed p.239 / PDF p.255, defines the actual
  separable-closure character functor, the Krull action and its
  continuity.
- Theorem 12.23, printed p.240 / PDF p.256, gives the contravariant
  equivalence and explicitly states that short exact sequences correspond
  to short exact sequences. Its proof reduces to the diagonalizable
  correspondence and Galois descent.
- Theorem 12.9(b) and its proof, printed pp.233–234 / PDF pp.249–250,
  give the reversed short-exact-sequence correspondence for
  diagonalizable groups.

The derived formulation expresses Milne's sequence clause through the
published actual character functor, all-test kernel and fppf quotient
interfaces. The explicit local finite presentation in the Library's
quotient predicate agrees with the finite-type field scope: multiplicative
type here has finitely generated diagonalizable models, so the groups are
affine of finite type over a field. Morphisms between such groups are
locally of finite presentation. The original passages and complete
retained official 2017 errata snapshot of 2 November 2026 were read; no
correction there affects these passages.

The separate `MultiplicativeTypeGaloisExactnessStatement` supplies a
finite-splitting-field interface with explicit diagonalizable models.
This proposition instead refers directly to the absolute functor for all
objects of its source category. It adds no categorical kernel or cokernel
construction to that category and asserts no equivalence of arbitrary
longer complexes. The published absolute character anti-equivalence and
the finite exactness proof are possible proof inputs; neither is assumed
as an extra hypothesis here.
