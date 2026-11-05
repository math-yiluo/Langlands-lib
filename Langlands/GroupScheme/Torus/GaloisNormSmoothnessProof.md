# Smoothness of the actual finite-Galois torus norm

Worker 1614, with Worker 1642 contributing the shear, smooth projection,
finite-product smoothness and field-base-change descent infrastructure.

`Langlands.GroupScheme.GaloisNormSmoothnessProof.galoisNormSmoothness.{u}`
proves the published
`Langlands.GroupScheme.GaloisNormSmoothnessStatement.{u}` exactly.
For fields `k L : Type u`, an algebra structure `Algebra k L`, a
finite-dimensional Galois extension, and an affine commutative group scheme
`T` over `Spec k`, it proves

```lean
IsSplitTorus (GaloisPointComparison.baseChanged k L T.toGrp) →
  Smooth (GaloisNorm.norm k L T).hom.hom.left
```

The quantified affine and locally finite type instances for the base-changed
group are retained as in the statement. The source of the actual norm is
`AffineWeil.groupScheme k L T_L`, where `T_L` is the actual base change of
`T.toGrp`. The universe is arbitrary, and the proof applies in every
characteristic, including when the characteristic divides the extension
degree.

This is a derived algebraic proof using the published tensor, affine Weil
restriction, norm and group-scheme APIs. The original motivation and its
distinction from the valued-field norm-image assertion are recorded in the
[target statement's explanation](GaloisNormSmoothness.md). The implemented
argument below establishes smoothness of the scheme morphism; rational-point
openness and surjectivity are separate assertions.

## Natural coordinates on every affine test algebra

Write `W := AffineWeil.groupScheme k L T_L` and let `W_L` be its base change
to `L`. Let `E := L →ₐ[k] L`, with distinguished element `AlgHom.id k L`.
For each commutative `L`-algebra `A`, the proof constructs a bijection

```text
W_L(A) ≃ (E → T_L(A)).
```

Here points are actual morphisms from the affine test scheme over the
specified field. `weilTensorPointsEquiv` first combines the published
base-change point equivalences with `AffineWeil.pointsEquiv` to obtain
`W_L(A) ≃* T(L ⊗[k] A)`. The finite-Galois tensor decomposition then sends
`L ⊗[k] A` to `E → A`; its coordinate at `τ` evaluates a pure tensor
`c ⊗ a` as `algebraMap L A (τ c) * a`. This is a `k`-algebra equivalence.

For an affine group scheme, `piAlgebraPointsEquiv` identifies points over a
product algebra with families of points over its factors. Its inverse
uses the actual affine coordinate algebra and its spectrum isomorphism.
Combining these comparisons and changing each resulting `T(A)` point to a
`T_L(A)` point gives `splitWeilPointsEquiv`.

The tensor evaluation maps commute with homomorphisms of `L`-algebras.
Together with the naturality of the published Weil and base-change
comparisons, this proves `splitWeilPointsEquiv_naturality` for every
commutative affine test algebra and every algebra homomorphism.

## The actual norm is the product of the coordinates

The private lemma `norm_eq_prod` starts with the published
`TensorGaloisPoint.extend_norm`. It evaluates the extended equality at the
identity embedding. Extension followed by this evaluation is the identity;
coefficient conjugation followed by evaluation gives the coordinate indexed
by that automorphism. Thus the tensor norm equals the product of these
evaluated coordinates.

`baseChangedNorm_eq_prod` combines this calculation with
`GaloisNorm.norm_affinePoints` and compatibility of the actual base-change
point equivalence with composition by a group morphism. It reindexes the
product using `Algebra.IsAlgebraic.algEquivEquivAlgHom k L`. For every `A`
and every `x : W_L(A)`, it obtains the equality of actual `T_L(A)` points

```text
N_L(x) = ∏ τ : E, splitWeilPointsEquiv A x τ,
```

where `N_L` denotes the actual base change of `GaloisNorm.norm k L T`.

## Shear, reconstruction and smoothness

Let `E' := {τ : E // τ ≠ AlgHom.id k L}` and
`R := pi (fun _ : E' => T_L)`. The imported
`GaloisNormSmoothnessGeometry.shearEquiv` sends a family `x : E → M` in a
commutative group to its total product together with its coordinates on
`E'`. Its inverse recovers the distinguished coordinate by multiplying the
total product by the inverse product of the remaining coordinates.

`productCoordinatesEquiv` converts the resulting pair of point families
into points of `T_L ⊗ R` using the actual finite-product and binary-product
point equivalences. Their naturality and the shear's naturality give
`shearedPointsEquiv_naturality`.

The private affine reconstruction helpers use
`CocharacterDatum.coordIso` and the universal affine coordinate point.
A natural family of maps on affine points defines a morphism of schemes
over the base, and a natural family of bijections defines an isomorphism
there. The affineness of `W_L` follows from its pullback description.
The splitting hypothesis makes `T_L` a torus, so the published finite-product
torus and affineness results give affineness of `R`; the binary product is
affine as well. Applying reconstruction therefore gives an actual
isomorphism of schemes over `Spec L`

```text
e : W_L.X ≅ (T_L ⊗ R).X.
```

The first projection after `e.hom` agrees on every affine point with `N_L`,
by the product formula for the norm. Evaluation at the universal affine
point proves equality of these actual morphisms.

The splitting hypothesis also makes `T_L` smooth. The imported
`smooth_complement` makes `R` smooth, and `smooth_of_iso_fst` transfers
smoothness of the projection to `N_L`. Finally,
`smooth_of_field_baseChange` descends smoothness along the faithfully flat,
quasi-compact field-extension morphism `Spec L → Spec k`.

The shear only uses multiplication and group inversion. The argument makes
no assumption that the extension degree is invertible, and also covers
the trivial extension and a split torus of rank zero.
