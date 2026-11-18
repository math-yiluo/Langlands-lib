# Closed affine pullbacks of algebraic-space test points

Author: Worker 309. This internal unit constructs algebraic affine pullbacks
and identifies their analytic images under an explicit point-lifting premise.
It does not assert that those analytic images are closed, or prove the task's
Hausdorff and rational-point embedding conclusions.

## Affine pullbacks from separatedness

`HasClosedAffinePointPullbacks` records the following property for an algebraic
space over `Spec K`: for every pair of test algebras `A`, `B` with finite
polynomial presentations and points `x : X(A)`, `y : X(B)`, there exist a test
algebra `C` with a finite polynomial presentation and algebra maps
`f : A → C`, `g : B → C`, such that the induced map `A ⊗[K] B → C` is
surjective and the corresponding square of actual represented presheaves
is a pullback over `X`. All test algebras have the field universe `u`, as
in the existing algebraic-space analytification interface.

`hasClosedAffinePointPullbacks_of_isSeparated` proves this property from
`IsSeparated X`. The proof constructs the published represented pair pullback
`W`. Closedness of the diagonal gives a closed immersion
`W → Spec A ×_K Spec B`; the existing affine-intersection theorem shows
that `W` is affine. The presentations make `A` and `B` finite type over `K`.
The product and its closed subscheme `W` are therefore locally of finite
type over `K`. No finite type or étaleness condition on the maps to `X`,
and no locally finite type hypothesis on `X`, is needed.

Take `C` to be the actual coordinate ring of `W` with the scalar action from
its structural morphism, and use the existing affine-scheme construction
to obtain its finite polynomial presentation. The canonical affine isomorphism
`W ≅ Spec C` transports the presheaf pullback. The two maps from `Spec C`
are converted to the actual algebra maps `f`, `g` by the spectrum equivalence.

To prove surjectivity of the induced tensor map, the proof compares its
spectrum map with the pairing `Spec C → Spec A ×_K Spec B`. Compose the
latter with the standard comparison from the slice product to the scheme
pullback and then with Mathlib's tensor-product spectrum isomorphism.
The two resulting morphisms agree after both scheme pullback projections:
the tensor universal property gives `f` and `g`, and the product pairing
gives the same two maps. Thus the spectrum map of the tensor map is a
closed immersion. Surjectivity on global sections, transported through
the canonical `Γ(Spec R) ≅ R` isomorphisms and their naturality, gives
surjectivity of the original tensor map.

The algebraic declarations use the existing nontrivially normed-field API
for `pointHom`; their proofs are algebraic.

## Analytic image of a supplied affine pullback

`IsAnalytification.affine_point_relation_eq_range` assumes the explicit
ordinary-point lifting property for every categorical analytic pullback
over the fixed complete ultrametric nontrivially normed field `K`, with
field, space and index universe `u`. It proves that the range of
`z ↦ (baseMap K P R f z, baseMap K Q R g z)` is exactly the set of pairs
of affine analytic points with equal images under the given `PointFamily`.

The proof applies `IsAnalytification.isPullback` to the supplied actual
presheaf square. For a pair with equal images, the retained point-lifting
premise gives a point of the analytic pullback with the prescribed
projections. The published comparison of `localizedHom` with `baseMap`
identifies these projections with the two factors of the stated range map.
In the reverse direction, commutativity of the analytic pullback square,
evaluated on its point, makes the images of the projections equal.

This lemma assumes neither separatedness nor surjectivity of the tensor
map: those conditions were needed to construct the algebraic closed
pullback, while the image identity needs only the supplied pullback square.
The analytic point-lifting premise remains explicit. It asserts existence,
not uniqueness, of a point over each matching pair. No topological
pullback comparison is asserted. Proving that the range is closed is the
separate affine closed-correspondence obligation.

## Provenance

This is internal deduction from published Library and Mathlib constructions:
the represented pair pullback, the closed-diagonal and affine-intersection
lemmas, the actual affine coordinate algebra and canonical scheme isomorphism
in `AffineSchemeAnalytification`, Mathlib's slice-product and tensor-spectrum
comparisons, the closed-immersion global-section criterion and `ΓSpecIso`
naturality, and the existing `IsAnalytification` and `localizedHom` point-map
comparison. No new external statement is translated or assumed proved.
