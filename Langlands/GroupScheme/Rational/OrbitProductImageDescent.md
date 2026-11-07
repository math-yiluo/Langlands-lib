# Actual orbit-product image ideals and their descent

This module connects the actual coordinate pullback in
`Langlands.GroupScheme.OrbitProductPullback` with the full defining ideal sheaf
of its morphism to the base-changed group scheme. Fixedness of the supplied
polynomial-valued point under the combined coefficient and variable action
then gives actual defining-ideal descent.

The fields `k` and `K` and the coordinate index type `I` lie in an arbitrary
universe `u`. An algebra structure `Algebra k K` and a group scheme `G` over
`Spec k` are supplied. The structure morphism of `G` is affine. Write
`A = CocharacterDatum.coordAlgebra G`, `R = MvPolynomial I K`, and `G_K` for
the actual base change of `G` along `Spec K → Spec k`.

For any actual point `x : Lie.AffinePoints G R`, the preceding module constructs
the `K`-algebra map

```text
pullbackK(x) : K ⊗[k] A →ₐ[K] R,
c ⊗ a ↦ C(c) · coord(x)(a).
```

Here `coord(x)` is the actual affine-coordinate evaluation of the scheme
morphism `x`, and `pullback(x)` is the same map restricted to `k`.

`morphism` is the composite of `Spec pullbackK(x)` with the existing
`TensorCoordinates.baseChangeIso`. Its target is `G_K.X.left`.
`morphism_fst` proves that its projection to `G.X.left` is exactly `x.left`.
The proof uses the tensor inclusion of `A`, the pure-tensor pullback formula
and `CocharacterDatum.map_coord`. `morphism_snd` proves that its projection
to `Spec K` is the structure morphism of `Spec R`, using the `K`-algebra
map's scalar compatibility.

Thus `point` is an actual `R`-valued point of `G_K`.
`affineBaseChangeEquiv_point` proves that the existing equivalence on actual
base-changed affine points sends it to `x`. This identifies the construction
with the usual base change of the supplied point.

`appTop_comp_sectionsEquiv` compares its actual map on global sections with
`pullback(x)`. Explicitly, after the existing ring equivalence

```text
e_K : K ⊗[k] A ≃+* Γ(G_K.X.left, ⊤),
```

the map on global sections equals `pullback(x)` followed by the canonical
isomorphism `R ≃ Γ(Spec R, ⊤)`. The proof composes the morphism with the
inverse tensor-coordinate presentation, applies global sections and uses
naturality of `Scheme.ΓSpecIso`.

`ideal_top_comap_sectionsEquiv` consequently identifies

```text
((morphism(x)).ker.ideal(⊤)).comap e_K = RingHom.ker pullback(x).
```

The ideal sheaf is the actual morphism kernel, hence the full defining ideal
of its scheme-theoretic image. The proof uses the affine formula for a
morphism's kernel ideal sheaf, the comparison of global-section maps and
injectivity of the spectrum/global-section isomorphism. The conclusion concerns
the full ideal, including its scheme structure.

Now supply a monoid homomorphism
`ρ : (K ≃ₐ[k] K) →* Equiv.Perm I` and suppose that `x` is fixed under
`Lie.affineMap G (PolynomialGalois.orbitAction k K I ρ σ)` for every `σ`.
This polynomial action conjugates coefficients by `σ` and sends `X i` to
`X (ρ σ i)`. `coefficientConjugate_mem` proves stability of the displayed
tensor-coordinate image ideal under conjugation of the `K` tensor factor.
It rewrites that ideal as the actual pullback kernel and applies
`PolynomialGalois.coefficientConjugate_mem_ker` with the full tensor
equivariance proved in `OrbitProductPullback`.

If in addition `[IsGalois k K]`, `definingIdealDescent` constructs

```text
DefiningIdealDescent
  (pullback.fst G.X.hom (algebraBaseMap k K))
  (morphism(x)).ker.
```

In particular its `ideal` field is an ideal sheaf `J` on `G.X.left`, and its
`eq_comap` field states that the full image ideal upstairs equals the pullback
of `J`. The construction applies
`AffineIdealDescent.ofGaloisStableTensorIdeal` with the existing ground and
extension global-section equivalences.
`TensorCoordinates.projection_comp_groundSectionsEquiv` supplies their
compatibility with the actual projection, so that compatibility is proved
and is not a new premise.

`blockProductDefiningIdealDescent` specializes this construction to the actual
ordered block product from `OrbitProductPullback`. Its explicit premises say
that each block is preserved as a multiset by every `ρ σ`, that the factor
list within each block is pairwise commuting, and that the polynomial action
sends factor `i` to factor `ρ σ i`. The preceding module's
`blockProduct_fixed` discharges point fixedness. There is no commutation
premise between different blocks.

This is internal support derived from the existing affine-coordinate,
tensor-coordinate, polynomial-equivariance and ideal-sheaf descent APIs.
It asserts no new literature-specific theorem. The Galois extension need not
be finite, and no perfectness, infinitude, reductivity or splitness assumption
is used. Consumers still have to construct compatible pinning and root
factors, verify the transport and commutation premises, identify the actual
Steinberg product with the morphism here, and prove the immersion, quotient,
exceptional even-type-A and rational-lifting geometry. This unit proves no
global section in even type A and does not prove
`QuasiSplitSteinbergQuotientStatement`.
