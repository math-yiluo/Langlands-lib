# Smooth projection dimension from a represented fppf kernel

This internal derived unit concerns a supplied fppf quotient homomorphism
`q : G ⟶ Q` and a specified representative `z : Z ⟶ G` of its kernel
subgroup functor. It constructs the isomorphism from `Z` to the actual kernel,
proves smoothness of a quasi-compact projection from smoothness of `Z`, and
over a field with connected source identifies the projection's smooth relative
dimension with that of `Z`. A final theorem combines this with the existing
action and dimension adapter.

## Objects and scope

The base of the first section is an arbitrary `B : Scheme.{u}`. The groups
`Z`, `G` and `Q` are actual group objects in schemes over `B`, and the maps
are actual group-scheme homomorphisms. The hypotheses are the existing
predicates

```lean
hq : IsFppfQuotient N q
hz : N.IsRepresentedBy z
```

The first asserts flatness, scheme surjectivity and local finite presentation
of the underlying `q`, together with
`SubgroupFunctor.range (kernelι q) = N`. The second asserts that `z` is
monomorphic as a morphism over `B` and that its range is `N`. Both equalities
of subgroup functors apply to every scheme test over `B`.

The entry `IsFppfQuotient.kernelIso hq hz` is an isomorphism of group schemes
`Z ≅ kernel q`. The theorem `kernelIso_hom_comp` proves that its homomorphism
followed by the actual kernel inclusion is `z`. Neither conclusion requires
smoothness, affineness, connectedness or centrality.

`IsFppfQuotient.fibers_iff` states, for every test `T` and `g,h : T ⟶ G.X`,
that equality of their images in `Q` is equivalent to
`g⁻¹ * h ∈ (SubgroupFunctor.range z).carrier T`. It asserts an exact fiber
criterion, without surjectivity on each test's original point group.

`IsFppfQuotient.smooth_of_smooth_kernel` additionally assumes
`QuasiCompact q.hom.hom.left` and `Smooth Z.X.hom`, and concludes
`Smooth q.hom.hom.left`.

The field section works over any `k : Type u` with `Field k`, at arbitrary
universe `u`. The theorem
`IsFppfQuotient.smoothOfRelativeDimension_of_kernel` assumes that `q` is
quasi-compact, that `G.X.left` is connected, and that `Z.X.hom` is smooth of
prescribed relative dimension `n`. It concludes that `q` is smooth of relative
dimension `n`. It makes no additional connectedness assumption on `Z`, and
requires no affineness or unipotence assumptions.

## Provenance and proof

The construction and its consequences are internal derivations from:

- `SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` and its inclusion
  compatibility theorem in `RepresentedSubgroup`;
- `mem_range_kernelι_iff` in `CentralIsogeny.Basic`;
- `QuotientCell.multiplication_isPullback`;
- the actual kernel pullback `kernel_isPullback_scheme` in
  `Langlands.AbelianScheme.Kernel`;
- Mathlib's fpqc descent for smoothness in `Morphisms.LocalFlatDescent`, smooth
  base change and composition of smooth relative dimensions;
- the published `smoothConnectedRelativeDimension` and
  `fieldSmoothClosedPointStalkDimension` proofs;
- the quotient consequences proved in `Rational.FppfQuotientAction`.

No new external structural theorem is assumed. Worker 362 authored this pair;
imported constructions retain their existing authorship.

The entry compares the two representatives of `N`: the given `z`, and the
actual kernel inclusion, whose representation property is exactly the
kernel-range clause of `hq`. The existing uniqueness-of-representatives
construction supplies the group-scheme isomorphism and its compatibility
with the inclusions.

For the fiber criterion, rewrite both ranges as the actual kernel range.
Membership there means that `g⁻¹ * h` is killed by `q`. Preservation of
multiplication and inversion turns this into
`(g ≫ q)⁻¹ * (h ≫ q) = 1`, equivalent to equality of the images.

Apply `QuotientCell.multiplication_isPullback` with cell `G.X` and cell
inclusion the identity. The resulting actual kernel-pair square has maps
`(g,v) ↦ g * z(v)` and `(g,v) ↦ g`. The second map is the base change of the
smooth structure map of `Z`. Flip the square so this smooth projection is
the first leg, then apply Mathlib's descent of smoothness along the
quasi-compact flat surjective `q`. This proves smoothness of `q`.

Over a field, the published connected-source theorem assigns some constant
smooth relative dimension `m` to this smooth `q`. Pulling back along the unit
of `Q` gives relative dimension `m` for the actual kernel. Forgetting the
group structure on `kernelIso` gives an isomorphism of schemes over the
field. It is smooth of dimension zero, so composition transports dimension
`m` to `Z`.

The imported `relativeDimension_eq` from `FppfQuotientAction` applies to any
nonempty scheme over the field
with two prescribed smooth relative dimensions. Smoothness implies local
finite type and hence the Jacobson property. Choose a closed point and apply
`fieldSmoothClosedPointStalkDimension` with each dimension; equality of their
casts in the stalk-dimension value implies equality in `ℕ`. For `Z`, the
unit supplies nonemptiness from the nonempty spectrum of the field. Thus
the given dimension `n` equals `m`, proving the asserted dimension of `q`.

## Action and strict decrease

`IsFppfQuotient.exists_action_relativeDimension_of_kernel` assumes `G` and `Q`
affine over the field, `G` connected and unipotent in the existing
representation-theoretic sense, a stable subgroup `N` for the given
`AutomorphicAction H G`, and prescribed smooth dimensions `d` of `G` and
`n` of `Z`, with `0 < n`. It returns an actual action `b` on `Q` and a natural
number `m`, with smoothness, connectedness and unipotence of `Q`,
`SmoothOfRelativeDimension n q.hom.hom.left`,
`SmoothOfRelativeDimension m Q.X.hom`, `d = n + m`, `m < d`, and

```lean
b.act h (g ≫ q.hom.hom) = a.act h g ≫ q.hom.hom
```

on every scheme test and for every acting point `h` and group point `g`.
The acting group `H` is arbitrary; no torus assumption is needed here.

Affineness supplies quasi-compactness of `q`: its composite with the structure
map of `Q` is the affine structure map of `G`, and the affine structure map
of `Q` is quasi-separated. The new kernel dimension theorem now supplies the
projection dimension. The previously proved
`IsFppfQuotient.exists_action_relativeDimension` gives the remaining
conclusions, and the final theorem retains the derived projection dimension
explicitly in its conclusion.

The quotient `Q`, the homomorphism `q`, their fppf properties, and the
representation of the kernel remain inputs. In the final theorem,
affineness of both groups and the positive smooth kernel dimension are also
inputs. This unit proves neither quotient existence nor quotient affineness,
central subgroup existence, `CentralSmoothQuotientStatement`, or the full
`SemigroupOrderedProductStatement`.
