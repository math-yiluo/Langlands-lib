# Density of rational points of tori split by a finite Galois extension

Worker 1110. The main result is a form of Milne, *Algebraic Groups*
(2017), Corollary 12.65 (printed p.251, PDF p.267): if `T` is a torus over
an infinite field `k`, then `T(k)` is dense in `|T|`. Here the torus
hypothesis takes the form "`T` becomes a split torus over a finite Galois
extension". This matches Milne's Definition 12.14 (printed p.236, PDF
p.252) once a torus is known to split over such an extension. That splitting
result is the separate Library statement
`Langlands.GroupScheme.TorusFiniteGaloisSplittingStatement`; it is neither
used nor proved here. Milne deduces 12.65 from unirationality (12.59–12.64,
via induced tori and Weil restriction). The Lean proof below follows a
different, elementary route: norms of `K`-points and Dedekind independence
of characters. The Milne errata snapshot of 2 November 2026 has no entry
for printed pp.236 or 250–251.

All declarations are in the namespace `Langlands.GroupScheme.TorusDensity`.
The algebra comes from `Langlands.GroupScheme.Torus.GaloisDensityAlgebra`.
The module's record names the definition `normPoint` (the Galois norm of a
`K`-point, see "Laurent coordinates and norms" below) as its entry
declaration. That construction is internal and has no literature
counterpart; the module's main result is the theorem in the next section.

## Main theorem

`dense_rationalPoints_of_isSplitTorus_baseChange`. Let `k` and `K` be
fields in the same universe, with `[Algebra k K]`, `[Infinite k]`,
`[FiniteDimensional k K]` and `[IsGalois k K]`. Let `T` be any group
scheme over `Spec k`; it need not be affine or of finite type. Suppose the
Library's `IsSplitTorus` holds for the base change of `T` along
`specBase k K = Spec.map (CommRingCat.ofHom (algebraMap k K))`, that is,
`GroupScheme.baseChange (specBase k K)` applied to `T`. Then the union of
the images of all rational points, `⋃ p : RationalPoint k T.X, Set.range
p.left`, is dense in the underlying space of `T.X`. This is
`HasDenseRationalPoints k T.X` from
`Langlands.AlgebraicGeometry.PointTopology.RationalDensityStatement`,
unfolded. The rank may be zero.

## Galois descent of points

`specGal σ` is the automorphism `Spec σ` of `Spec K` for
`σ : K ≃ₐ[k] K`. `specGal_comp_specBase`, `specGal_comp_specGal` and
`specGal_one` record that it lies over `Spec k` and composes contravariantly.

`exists_rationalPoint_of_fixed` (finite Galois `K / k`): let `X` be a
scheme over `Spec k` and `z : Spec K ⟶ X.left` a morphism over `Spec k`
with `Spec σ ≫ z = z` for all `σ`. Then some rational point `p` satisfies
`specBase k K ≫ p.left = z`. Proof: `Spec K` has one point, so `z` factors
through an affine open `Spec R ⟶ X.left` (`Scheme.exists_Spec_apply_eq`,
`IsOpenImmersion.lift`). The factorization is `Spec ψ` for a ring map
`ψ : R → K` (`Spec.preimage`). By faithfulness of `Spec`, `ψ` is fixed by
every `σ`, so its values lie in `k` (`IsGalois.mem_range_algebraMap_iff_fixed`).
This gives `ψ₀ : R → k` and the point `p₀ = Spec ψ₀ ≫ (Spec R ⟶ X.left)`.
Since `p₀` lies over `Spec k` after base change to `K`, and `k → K` is
injective, `p₀` is a section.

## Galois action on `K`-points

- `testObj K` is `Spec K` over itself; `testObjBase k K` is `Spec K` over
  `Spec k`. `laurent_point_left` shows that a `K`-point of the Laurent
  group scheme `splitTorus.laurentGroupScheme I K` is the spectrum of the
  evaluation map `lev K t` at its unit coordinates `t`.
- `galHom σ` is `Spec σ` as an endomorphism of `testObjBase k K`, and
  `galAct T σ` is precomposition with it. It is a group endomorphism of the
  `K`-points of `T` because precomposition respects the group law
  (`MonObj.comp_mul`). `galAct_galAct` gives the composition rule.
- `twistMap T σ` is the automorphism `id ×_k Spec σ⁻¹` of the base change
  `pullback T.X.hom (specBase k K)`. `baseChangePoints T` is the Library
  bijection `GroupScheme.baseChangePointsEquiv` between `K`-points of the
  base change and `K`-points of `T`. `baseChangePoints_symm_galAct_left`
  says that the base-change point of `galAct T σ y` is
  `Spec σ ≫ x ≫ twistMap T σ`, where `x` is the base-change point of `y`.

## Laurent coordinates and norms

Fix an isomorphism `Λ` of group schemes over `Spec K` from the base change
of `T` to `splitTorus.laurentGroupScheme I K`, with `I` finite.

- `coordEquiv Λ` is the resulting multiplicative bijection from the
  `K`-points of `T` to `I → Kˣ`, and `chart Λ` is the underlying scheme
  isomorphism with `Spec K[t_i^{±1}]`. `coordEquiv_left` writes the chart
  image of a point as `Spec` of evaluation at its coordinates.
- `galScheme Λ σ` is `twistMap T σ` in the chart, and `galRingHom Λ σ` is the
  ring endomorphism of the Laurent algebra whose spectrum it is.
  `galUnit Λ σ i` is the image of the coordinate unit `t_i`. Since
  `twistMap T 1` is the identity, `galUnit Λ 1 i = t_i` (`galUnit_one`).
- `coordEquiv_galAct`: the `i`-th coordinate of `galAct T σ y` is `σ`
  applied to the value of `galUnit Λ σ i` at the coordinates of `y`. This
  follows from `baseChangePoints_symm_galAct_left` and injectivity of
  `Spec.map` on ring maps. `coordAct Λ σ` is the same action transported to
  `I → Kˣ` (`coordAct_apply`, `coordAct_coordAct`).
- `normPoint Λ t` is the `K`-point with coordinates `∏_σ coordAct Λ σ t`.
  It is fixed by every `galAct T τ` because left multiplication by `τ`
  permutes the Galois group (`galAct_normPoint`). Its coordinates are
  `normFamily (galUnit Λ) t` (`coordEquiv_normPoint`).

## Proof of the main theorem

Choose `Λ` as the given isomorphism followed by the Library's
`splitTorus.laurentIso`. Let `U` be a nonempty open set of `T.X` with a
point `x0`. Some point `w` of the base change lies over `x0`
(`Scheme.Pullback.exists_preimage_pullback`). In the chart, the preimage
`W` of `U` is open and contains the image of `w`, so it contains a basic
open set `D(F)` around that image. Hence `F` is a nonzero Laurent
polynomial. `exists_lev_normFamily_ne_zero`, applied with `galUnit Λ` and
`galUnit_one`, gives `t : I → Kˣ` with `F(normFamily (galUnit Λ) t) ≠ 0`.
The norm point `z = normPoint Λ t` is Galois-fixed. So
`exists_rationalPoint_of_fixed` gives a rational point `p` whose image is
the image of `z`. In the chart, the base-change point of `z` is the
spectrum of evaluation at `normFamily (galUnit Λ) t`. That evaluation does
not kill `F`, so its image lies in `D(F) ⊆ W`. Projecting to `T.X`, the
image of `p` lies in `U`.

The module sets `backward.isDefEq.respectTransparency false` (and the
`.types` variant) and `backward.defeqAttrib.useBackward true`, like the
Library modules it builds on.
