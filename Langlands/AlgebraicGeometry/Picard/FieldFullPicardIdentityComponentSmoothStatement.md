# Smoothness of a supplied identity-component open of a full Picard parameter over a field

`Langlands.AbelianScheme.FieldFullPicardIdentityComponentSmoothStatement` is a
proposition definition (`def … : Prop`). It is stated without proof. Fix an
arbitrary field `k : Type u` in an arbitrary universe `u`, and write

```text
S = Scheme.Spec.obj (Opposite.op (CommRingCat.of k)).
```

The proposition quantifies over every existing `A : AbelianScheme S`, every
parameter scheme `P : Over S`, every actual rigidified family
`L : RigidifiedFamily A P`, and every proof

```text
hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A)
       (unitSection_comp A) L.
```

For such data it asserts: if `LocallyOfFiniteType P.hom`, then for every
`U : P.left.Opens`,

```text
IsFullPicardIdentityComponentOpen k A L hL U →
  Smooth (openLocusParameter P U).hom.
```

`LocallyOfFiniteType` and `Smooth` are Mathlib's morphism properties of schemes
(`AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.Smooth`). The
conclusion says that the structure morphism of the open subscheme `U` of
`P.left` to `Spec k` is smooth.

## The reused definitions

Nothing is redefined here. The module imports the published
`Langlands.AlgebraicGeometry.Picard.FieldPicardIdentityComponent` and
`Langlands.AlgebraicGeometry.Picard.OpenLocus`, and uses their declarations by
Lean name.

- `RigidifiedFamily`, `unitSection` and `unitSection_comp` are the existing
  actual rigidified families and unit section. `IsUniversal` is the existing
  universal property for the full rigidified class functor. It quantifies over
  every scheme over `S`, including nonreduced ones.
- `IsFullPicardIdentityComponentOpen k A L hL U` takes `k`, `A`, `L`, `hL`
  and `U` explicitly; `P` is implicit and determined by the type of `L`. By
  definition it is the equality of carriers

  ```text
  (U : Set P.left) = connectedComponent (fullPicardOriginPoint k A L hL),
  ```

  where `connectedComponent` is Mathlib's topological connected component.
  `fullPicardOriginPoint k A L hL` is the image of `IsLocalRing.closedPoint k`,
  the unique point of `Spec k`, under the published section
  `RigidifiedLineBundle.trivialParameter … L hL`. That section classifies the
  trivial rigidified family.
- `openLocusParameter P U` is the actual open subscheme `U.toScheme` of
  `P.left`, with structure map `U.ι ≫ P.hom`. Its structure sheaf is the
  restriction of the structure sheaf of `P.left`, so it keeps every nilpotent of
  the ambient scheme on `U`. It is not the reduced subscheme on `U`. Smoothness
  of `openLocusParameter P U` is therefore a property of the ambient parameter
  scheme near the identity component, and not only of its reduction.

## Exactly what is and is not assumed

The only hypothesis besides the quantified data and the predicate on `U` is
`LocallyOfFiniteType P.hom`, applied to the ambient parameter. It is a local
condition. The full Picard scheme need not be quasi-compact, and no
quasi-compactness or finite type is assumed.

The proposition asserts no existence of `P`, `L`, `hL` or `U`. In particular
it does not assert that the connected component of the origin is open. When no
open satisfies the predicate the implication holds vacuously for that `P`.

No further assumption is made. The proposition does not assume projectivity or
a polarization of `A`, an ample line bundle, algebraic closedness or perfectness
of `k`, or smoothness of `P`. It assumes no geometric reducedness, no tangent
space or dimension formula, and neither the final dual smoothness statement
`FieldDualSchemeSmoothStatement` nor the parent geometry statement
`FieldDualSchemeGeometryStatement`. Results of this kind must be proved in a
later proof of this proposition, not added as hypotheses.

The carrier equality only specifies which open of `P.left` is meant. This
proposition does not identify `U`, or `openLocusParameter P U`, with the
geometric Picard-zero functor on test schemes. It does not assume or conclude
`IsPicardZeroOpenLocus A L U`, and it does not relate `U` to the chosen dual
scheme. That comparison is a separate result. To yield an isomorphism with the
chosen dual scheme it must hold on all test schemes, including nonreduced ones.
Agreement of point sets is not enough.

## Original source and derived formulation

The registered original is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft, source ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

- (3.16), printed p.38 (PDF p.42). For a group scheme `G` locally of finite
  type over a field `k`, the identity component `G⁰` is the connected component
  of `G` containing the identity point `e`. It is open because `G` is locally
  noetherian.
- Proposition (3.17), printed pp.38-39 (PDF pp.42-43). `G⁰` is an open and
  closed, geometrically irreducible subgroup scheme. Part (ii) shows that
  smoothness of `G` over `k`, smoothness of `G⁰`, and smoothness at the origin
  are equivalent to each other. They are also equivalent to reducedness of
  `G ⊗_k K`, or of `O_{G,e} ⊗_k K`, for some *perfect* field `K ⊇ k`.
- Remark (3.18)(i), printed p.39 (PDF p.43). Over a non-perfect field,
  reducedness alone does not imply smoothness. The example is
  `Spec k[X,Y]/(X^p + αY^p)` with `α ∉ k^p`, which is reduced but not
  geometrically reduced.
- Corollary (6.6)(i), printed p.90 (PDF p.94). For a proper variety `X` over
  `k`, the tangent space of the Picard scheme at the identity is
  `H¹(X, O_X)`. `Pic⁰` is smooth over `k` if and only if
  `dim Pic⁰ = dim_k H¹(X, O_X)`.
- Proposition (6.15), printed p.94 (PDF p.98). For a group variety `X` over `k`,
  `dim_k H¹(X, O_X) ≤ dim X`. This holds over any field, not only perfect ones.
- Chapter VI §3, printed p.95 (PDF p.99). For an abelian variety `X` over a
  field, the source *admits* from the general theory that `Pic_{X/k}` is a group
  scheme with projective connected components. It notes that `Pic_{X/k}` also
  represents the functor of line bundles rigidified along the zero section,
  with a rigidified Poincaré bundle.
- Theorem (6.18), printed p.96 (PDF p.100). `Pic⁰_{X/k}` is reduced, hence an
  abelian variety, of dimension `dim X = dim_k H¹(X, O_X)`. The proof combines
  the finite kernel of `φ_L` for an ample `L` with (6.6) and (6.15). Definition
  (6.19) names `Pic⁰_{X/k}` the dual abelian variety.

This proposition is a derived formulation, not a quotation. The source works
with the Picard scheme, whose representability it admits, and its identity
component `Pic⁰`. Here the parameter `P` is arbitrary and is required only to
carry an actual universal rigidified family `L`. That is the rigidified form of
the representability which §3 admits. The origin is the point classifying the
trivial rigidified bundle. The trivial class is the unit for tensor product of
line bundles, which is why it plays the role of the source's identity point
`e`. The identity component is a supplied open with the carrier of (3.16). No
group law or group-scheme structure on `P` is constructed or assumed here, and
nothing here proves that the origin is the unit of one.

A proof must either relate `P` to the classical Picard identity component or
give a complete intrinsic argument. The source's admission of representability
is not a Lean proof. Because the field is arbitrary, the proof must use the
appropriate geometric smoothness criterion or descent. Examples are the
dimension criterion of (6.6) together with (6.15), or reducedness after a
perfect extension as in (3.17)(ii). By (3.18), reducedness over an imperfect
field alone is insufficient.

## Role

This is a focused prerequisite for the exact smoothness proof task whose
target remains `Langlands.AbelianScheme.FieldDualSchemeSmoothStatement`. It
neither replaces nor weakens that target. To derive the target, one must also
supply the comparison of `openLocusParameter P U`, with the restricted family,
against the chosen dual scheme on all test schemes. Openness of the component
and the existence of `P` with local finite type are further inputs. None of
these is provided here.

Worker 511 published the task contract specifying this statement. Worker 859 checked the cited
source passages and the reused declarations, wrote the Lean statement and this
explanation, and compiled them in the pinned environment.
