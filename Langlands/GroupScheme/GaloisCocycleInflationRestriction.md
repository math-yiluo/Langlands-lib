# Inflation and restriction for natural cocycles on finite Galois covers

Module: `Langlands.GroupScheme.GaloisCocycleInflationRestriction`.

This module proves a consequence of exactness at the middle term of inflation–restriction
for natural cocycles on finite Galois field covers. A cocycle of an affine group scheme
on `Spec K → Spec k` is trivial if its restriction to `Gal(K/E)` is a coboundary and every
cocycle on `Spec E → Spec k` is trivial, where `E/k` is a Galois subextension of `K/k`.
The module also gives a descent step along field towers and two facts about natural
cocycles. A natural cocycle `ξ` on `GaloisCocycle.cover k K` has Galois values
`GaloisCocycle.value ξ σ : G(K)` for `σ ∈ Gal(K/k)`, satisfying
`value ξ (σ τ) = value ξ σ · σ(value ξ τ)`, and `ξ.IsTrivial` means
`value ξ σ = f · σ(f)⁻¹` for one point `f ∈ G(K)` (`GaloisCocycle.isTrivial_iff`).

## Values of a twist

`GaloisCocycle.value_twist`: the twist `ξ.twist f`, with values
`(a, b) ↦ f(a)⁻¹ ξ(a, b) f(b)`, has Galois values `f⁻¹ · value ξ σ · σ(f)`. This is the
definition read at the identity and the arrow of `σ`.

## Inflation–restriction

`GaloisCocycle.isTrivial_of_restrict`. Let `k → E → K` be a tower of fields with `K/k` and
`E/k` finite Galois, and let `G` be a group scheme over `k` with `IsAffine G.X.left`. Let
`ξ` be a cocycle of `G` on `Spec K → Spec k`. Assume

- there is `f ∈ G(K)` with `value ξ σ = f · σ(f)⁻¹` for every `σ ∈ Gal(K/k)` with
  `σ.restrictNormal E = 1`, i.e. for every `σ ∈ Gal(K/E)`;
- every cocycle of `G` on `Spec E → Spec k` is trivial.

Then `ξ` is trivial. Proof: the twist `ξ.twist f` has values `c σ = f⁻¹ · value ξ σ · σ(f)`,
equal to `1` on `Gal(K/E)`. The published construction `GaloisCocycleTowerRecovery`
descends such a crossed homomorphism to values `v τ ∈ G(E)`, `τ ∈ Gal(E/k)`, satisfying the
cocycle law, with `c σ` the image of `v (σ|_E)` in `G(K)` (`extend_value`). The published
`GaloisCocycle.ofValues` turns `v` into a natural cocycle `ζ` on `Spec E → Spec k`, which is
trivial by hypothesis. Its refinement to `Spec K` along `GaloisCocycle.coverMap k E K` is
trivial and has the values `c σ` (`value_refine`, `value_ofValues`), so by
`GaloisCocycle.toFun_eq_of_value_eq` it agrees with `ξ.twist f` on every test scheme. Hence
`ξ.twist f` is trivial, and so is `ξ` (`Cocycle.IsTrivial.of_twist`).

## Restriction along a base change of the field

The remaining results of the `GaloisCocycle` namespace concern a tower `K → F → M` and a
field `M₀` with `K → M₀ → M`. Here `ξ` is a cocycle of `G` on `Spec M₀ → Spec K` with `M₀/K`
normal, and `ξ_M = ξ.refine (GaloisCocycle.coverMap K M₀ M)` is its refinement to
`Spec M → Spec K`. The scalar extension `GaloisCocycle.scalarExtension` (module
`GaloisCocycleScalarExtension`) is the cocycle of the base change `G_F` on `Spec M → Spec F`
obtained from the base change of `ξ` to `Spec F`.

- `scalarExtensionPointsEquiv_value`: under the published identification
  `scalarExtensionPointsEquiv` of `G_F`-points over `M` with `G`-points over `M`, the value
  of the scalar extension at `τ ∈ Gal(M/F)` is `value ξ_M τ`, where `τ` is viewed in
  `Gal(M/K)`.
- `exists_value_refine_of_scalarExtension_isTrivial` and
  `exists_value_refine_of_baseChangePullback_isTrivial`: if the scalar extension is trivial
  (for instance, if `ξ.baseChangePullback (Spec.algebraMap K F)` is trivial), then for one
  `f ∈ G(M)` one has `value ξ_M τ = f · τ(f)⁻¹` for every `τ ∈ Gal(M/F)`. These assume
  `M/F` finite Galois.
- `isTrivial_of_forall_value_refine`: for `M/K` finite Galois, if
  `value ξ_M σ = f · σ(f)⁻¹` for all `σ ∈ Gal(M/K)`, then `ξ` is trivial. The refinement is
  trivial by `isTrivial_iff`, and `Cocycle.IsTrivial.of_refine_fpqcCover` descends this
  along the fpqc cover `Spec M → Spec K`.
- `exists_value_refine_of_restrict` (one descent step): let `K → F → F₁ → M` be field
  extensions with `M/K` finite Galois and `F₁/F` finite Galois, let `G` be affine over `K`,
  and assume every cocycle of `G_F` on `Spec F₁ → Spec F` is trivial. If
  `value ξ_M τ = f · τ(f)⁻¹` for every `τ ∈ Gal(M/F₁)`, then the same holds, for some point,
  for every `τ ∈ Gal(M/F)`. Proof: inflation–restriction over `F`, applied to the scalar
  extension of `ξ` to `Spec M → Spec F` with the intermediate field `F₁`. An automorphism of
  `M/F` restricting to the identity on `F₁` is an automorphism of `M/F₁`, so the first
  hypothesis holds by the value comparison above. The conclusion follows from
  `exists_value_refine_of_scalarExtension_isTrivial`.

## Two facts about cocycles

In the namespace `Cocycle`:

- `IsTrivial.congr`: a cocycle with the same values on every test scheme as a trivial
  cocycle is trivial.
- `isTrivial_baseChangePullback_map`: if `ξ.baseChangePullback b` is trivial, then so is
  `(ξ.map φ).baseChangePullback b` for every homomorphism `φ : G ⟶ H`. The trivializing point
  is the image of the given one under the base change of `φ`; the comparison uses
  `baseChangePointsEquiv_comp`.

## Source

J.-P. Serre, *Galois Cohomology*, Springer (1997), registered as
`serre-1997-galois-cohomology`: Chapter I, §5.8 "Complements", item (a) "Group extensions",
printed p. 56 (PDF p. 64). For a closed normal subgroup `H` of `G` and a `G`-group `A`, the
sequence `1 → H¹(G/H, A^H) → H¹(G, A) → H¹(H, A)^{G/H}` is exact. In the field tower,
exactness at `H¹(K/k, G(K))` says that a class trivial on `Gal(K/E)` comes from
`H¹(E/k, G(E))`. The theorem `isTrivial_of_restrict` applies this argument when
`H¹(E/k, G(E))` is trivial.
