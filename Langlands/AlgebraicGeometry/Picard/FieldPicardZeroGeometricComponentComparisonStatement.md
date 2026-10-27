# Geometric-point families and the origin component of a universal field Picard parameter

`Langlands.AbelianScheme.FieldPicardZeroGeometricComponentComparisonStatement.{u}`
is a proposition definition. It states a comparison and proves nothing.

## The statement

Fix an arbitrary field `k : Type u` in an arbitrary universe `u`, and write

```text
S = Scheme.Spec.obj (Opposite.op (CommRingCat.of k)).
```

The statement quantifies over the existing data `A : AbelianScheme S`, a
parameter `P : Over S` and an actual rigidified family
`L : RigidifiedFamily A P`. It assumes `LocallyOfFiniteType P.hom` and a proof

```text
hL : RigidifiedLineBundle.IsUniversal A.X.hom
       (unitSection A) (unitSection_comp A) L.
```

These are the hypotheses of the published `FieldPicardZeroOpenLocusStatement`
and `FieldPicardZeroGeometricOpenLocusStatement`. `IsUniversal` is the full
universal property from
`Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalBundle`: it classifies
rigidified line-bundle isomorphism classes on every test scheme over `S`, not
only on field-valued tests. The field `k` need not be perfect or algebraically
closed.

There are no further hypotheses. The conclusion is that every algebraically
closed field `K : Type u` and every actual scheme morphism
`s : Spec (CommRingCat.of K) ⟶ P.left` satisfy

```text
IsPicardZeroFamily A
  ((RigidifiedLineBundle.relativePullback A.X.hom
    (unitSection A) (unitSection_comp A)
    (Over.homMk s rfl : Over.mk (s ≫ P.hom) ⟶ P)).obj L)
↔ Set.range s ⊆ connectedComponent (fullPicardOriginPoint k A L hL).
```

The composite `s ≫ P.hom` is the structure morphism of `Spec K` over `k`.
No separately chosen field homomorphism `k → K` and no compatibility
hypothesis is involved. The proof `hL` is bound by the universal quantifier
because the origin point takes it as an argument.

### The left side

The bundle is the actual rigidified relative pullback of the supplied family `L`
along `Over.homMk s rfl`. `IsPicardZeroFamily`, from
`Langlands.AlgebraicGeometry.Picard.RelativePicardZero`, moves its underlying
line bundle to the base-changed abelian scheme `A ×_k Spec K` with
`familyLineBundle`. It then applies `IsGeometricallyPicardZero` there. That
predicate requires, for every algebraically closed field `K' : Type u` and every
morphism `Spec K' ⟶ Spec K`, that the fibre bundle on the base change of
`A ×_k Spec K` to `Spec K'` be translation invariant under every `K'`-point.
So all further geometric fibres of the pulled-back family are tested, not only
the fibre over `s` itself. No representative bundle, algebraic-equivalence or
smooth-family predicate, and no membership in an abstract subgroup of classes,
replaces this condition.

### The right side

`fullPicardOriginPoint k A L hL : P.left` is the published point from
`Langlands.AlgebraicGeometry.Picard.FieldPicardIdentityComponent`, with `P`
implicit. It is the image of the unique point of `Spec k` under the published
section `RigidifiedLineBundle.trivialParameter` classifying the trivial
rigidified family. `connectedComponent` is Mathlib's topological connected
component in the underlying space of `P.left`. The statement introduces no
second origin, classifier or component predicate.

The right side keeps the range form used by
`FieldPicardZeroGeometricOpenLocusStatement`, with the specified component
in place of an existential open subset. Since `Spec K` has exactly one point,
mathematically it says that the image of that point lies in the connected
component of the origin.

## What the statement does not assert

This is a statement only. The module contains no theorem.

- The conclusion has no open-subset existential. It does not assert that the
  connected component of the origin is open, so it does not provide an open
  `U` satisfying `IsFullPicardIdentityComponentOpen k A L hL U`.
- It does not prove `FieldPicardZeroGeometricOpenLocusStatement`. Both
  this comparison and an independent proof that the component is open would
  be needed for that. It does not touch `IsPicardZeroOpenLocus` or the
  all-test-scheme criterion of `FieldPicardZeroOpenLocusStatement`.
- It assumes no group law on `P`, projectivity, ambient existence, smoothness,
  base-change or field-extension comparison, openness, or dual-scheme
  existence.

`LocallyOfFiniteType P.hom` is kept to match the hypotheses of the two
openness statements. In the source it is the hypothesis under which the
identity component is open, but no openness conclusion is drawn here.

## Dependency direction

This comparison is intended as an input to proofs of
`FieldPicardZeroGeometricOpenLocusStatement` and
`FieldPicardZeroOpenLocusStatement`. Its proof and prerequisites must not use
either openness statement, or assume `IsPicardZeroOpenLocus` for the supplied
universal family. A result that starts with a supplied Picard-zero open locus
and identifies its carrier with this component is downstream of the comparison
and cannot prove it. Accordingly, the module imports only
`Langlands.AlgebraicGeometry.Picard.FieldPicardIdentityComponent` and Mathlib's
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`. It imports neither openness
statement.

A later proof must obtain any group law, field-extension compatibility of
the component, identification of the universal family with the rigidified
Picard functor, or geometric comparison that it uses as proved prerequisites.
It may not add them as hypotheses to this statement.

## Original source and derived interface

The registered original is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft, source ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

- Paragraph (6.2), printed p.88 (PDF p.92), defines the functor of line
  bundles rigidified along a section, with pullback along base morphisms. If it
  is representable, the universal rigidified bundle is the Poincaré bundle.
- Chapter VI, §3, printed p.95 (PDF p.99), takes an abelian variety `X` over a
  field `k`. It admits from the general theory that `Pic_{X/k}` is a group
  scheme over `k`, and notes that it represents the rigidified functor with a
  rigidified Poincaré bundle.
- Paragraph (3.16), printed p.38 (PDF p.42), defines the identity component of
  a group scheme locally of finite type over a field as the connected
  component containing the origin. That component is open.
  Proposition (3.17)(i), printed pp.38-39 (PDF pp.42-43), shows that it is
  geometrically irreducible and that `(G⁰)_K = (G_K)⁰` for every field
  extension `k ⊂ K`.
- Theorem (6.18) and Definition (6.19), printed p.96 (PDF p.100), show that
  `Pic⁰_{X/k}` is an abelian variety, the dual of `X`.
- Printed p.104 (PDF p.108) defines the homomorphism
  `ϕ : Pic_{X/k} → Hom(X, X^t)`, `L ↦ ϕ_L`. On points `ϕ_L` is
  `x ↦ [t_x^*L ⊗ L⁻¹]` (printed p.95), so `ϕ_L = 0` expresses translation
  invariance of `L`. Lemma (7.15) gives `Pic⁰_{X/k} ⊂ Ker(ϕ)`.
- Proposition (7.21), printed p.105 (PDF p.109), works over an algebraically
  closed field. It writes every `M` with `ϕ_M = 0` as `t_x^*L ⊗ L⁻¹` for an
  ample `L`. Corollary (7.22), printed p.106 (PDF p.110), concludes that
  `Pic⁰_{X/k} = Ker(ϕ)`.

Classically, a geometric point of `Pic_{X/k}` over an algebraically closed `K`
is a rigidified bundle on `X_K`. By (7.22) over `K` and (3.17)(i), it lies in
`Pic⁰` exactly when that bundle is translation invariant. The present
declaration is an internal interface derived from this. It is not a verbatim
quotation of Corollary (7.22). The source's origin is the identity of the
group scheme `Pic_{X/k}`; here it is the published `fullPicardOriginPoint`,
the point classifying the trivial rigidified family. The source's group
structure, representability and identification with `Pic_{X/k}` are not
imported. The statement instead quantifies over an arbitrary supplied
universal pair `(P, L)`.

Corollary (7.22) alone does not establish this statement. A proof must also
transport the classical comparison to an arbitrary universal pair. It needs a
group structure or replacement argument that is not assumed here, and
compatibility of the component with the extension `k ⊂ K` defined by
`s ≫ P.hom`. It must also compare the actual pulled-back family's own
geometric-fibre condition, over every further algebraically closed field,
with the single bundle over `K`.
