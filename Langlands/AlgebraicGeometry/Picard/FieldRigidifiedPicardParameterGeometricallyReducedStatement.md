# Geometric reducedness of a universal rigidified Picard parameter over a field

`Langlands.AbelianScheme.FieldRigidifiedPicardParameterGeometricallyReducedStatement`
is a proposition definition (`def … : Prop`). It is stated without proof. Fix
an arbitrary field `k : Type u` in an arbitrary universe `u`, and write

```text
S = Scheme.Spec.obj (Opposite.op (CommRingCat.of k)).
```

The proposition quantifies over every existing `A : AbelianScheme S`, every
parameter scheme `P : Over S`, and every actual rigidified family
`L : RigidifiedFamily A P` on `A ×_S P`, rigidified along the unit section. It
asserts that if

```text
RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L
```

and `LocallyOfFiniteType P.hom`, then `GeometricallyReduced P.hom`.

## The reused definitions

Nothing is redefined here. The module imports the published
`Langlands.AlgebraicGeometry.Picard.RelativePicardZero` (for `unitSection`,
`unitSection_comp` and `RigidifiedFamily`, and through it `IsUniversal`) and
the Mathlib modules for `GeometricallyReduced` and `LocallyOfFiniteType`.

- `IsUniversal … L` is the existing universal property of the full rigidified
  class functor: for every test object `T : Over S`, the classifying map from
  `T ⟶ P` to isomorphism classes of rigidified families on `A ×_S T`, given by
  pulling back `L`, is bijective. It quantifies over every scheme over `S`,
  including nonreduced ones.
- `LocallyOfFiniteType P.hom` is Mathlib's `AlgebraicGeometry.LocallyOfFiniteType`.
- `GeometricallyReduced P.hom` is Mathlib's class
  `AlgebraicGeometry.GeometricallyReduced`: for every field `K` and every
  morphism `Spec K ⟶ S`, the fibre product `P.left ×_S Spec K` is reduced.
  This is stronger than reducedness of `P.left`.

## Exactly what is and is not assumed

The hypotheses are exactly those of the published
`FieldFullPicardIdentityComponentSmoothStatement`, without the open `U` and
its carrier predicate. The field `k` is arbitrary; it need not be perfect or
algebraically closed. The proposition does not assume projectivity or a
polarization of `A`, an ample line bundle, finite type or quasi-compactness of
`P`, a group law or group-object structure on `P`, smoothness of `P`, or any
dimension or tangent-space formula. It asserts no existence of `P` or `L`.

## Provenance

This proposition is derived and has no verbatim counterpart in the source.
The registered original is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft, source ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`
(PDF page = printed page + 4).

- Chapter VI §3, printed p.95 (PDF p.99). For an abelian variety `X` over a
  field `k`, the source *admits* that `Pic_{X/k}` is a group scheme with
  projective connected components, and notes that it also represents the
  functor of line bundles rigidified along the zero section.
- Theorem (6.18), printed p.96 (PDF p.100). `Pic⁰_{X/k}` is reduced, hence an
  abelian variety, and `dim Pic⁰_{X/k} = dim X = dim_k H¹(X, O_X)`. The proof
  uses the finite kernel `K(L)` of `φ_L` for an ample `L` (Lemma (2.17)) to
  get `dim Pic⁰ ≥ dim X`, and combines this with Corollary (6.6) (printed
  p.90, PDF p.94: the tangent space at the identity is `H¹(X, O_X)`, and
  `Pic⁰` is smooth if and only if `dim Pic⁰ = dim_k H¹(X, O_X)`) and
  Proposition (6.15) (printed p.94, PDF p.98: `dim_k H¹(X, O_X) ≤ dim X`).
  Hence `Pic⁰_{X/k}` is smooth over `k`.
- Proposition (3.17)(ii), printed p.38 (PDF p.42). For a group scheme
  locally of finite type over a field, smoothness of the identity component
  is equivalent to smoothness of the whole group scheme. So the whole
  Picard scheme `Pic_{X/k}` is smooth, and a smooth scheme over a field is
  geometrically reduced.

This geometric reducedness is what is stated here, for an arbitrary
universal parameter `(P, L)` in place of the Picard scheme. The source's
admitted representability is replaced by the actual universality hypothesis
`IsUniversal`.

Remark (3.18)(i), printed p.39 (PDF p.43), shows that over a non-perfect
field a reduced group scheme, such as `Spec k[X,Y]/(X^p + αY^p)` with
`α ∉ k^p`, need not be smooth. So the statement asserts geometric reducedness,
not reducedness.

## Intended use

The intended consumer is the proof of
`Langlands.AbelianScheme.FieldFullPicardIdentityComponentSmoothStatement`
(proof task `e689d392-8896-4255-835c-4beab40a2d45`). With a group-object
structure on `P` and local finite type, Mathlib's
`AlgebraicGeometry.smooth_of_grpObj` (a group scheme over a field that is
geometrically reduced and locally of finite type is smooth; compare
(3.17)(ii)) turns this geometric reducedness into smoothness of `P.hom`. The
open subscheme `openLocusParameter P U` then inherits smoothness, because its
structure map is `U.ι ≫ P.hom` and open immersions are smooth. Proving this
statement is a separate task.

Worker 859 wrote the Lean statement and the first version of this
explanation and compiled them in the pinned environment. Worker 1002 checked
the cited source passages and the reused declarations, revised this
explanation, and submitted the pair.
