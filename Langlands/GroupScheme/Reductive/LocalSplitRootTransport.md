# Transport of root parametrizations and Weyl points along group maps

Module `Langlands.GroupScheme.Reductive.LocalSplitRootTransport`, namespace
`Langlands.GroupScheme.LocalSplitCell`.

## Setting

`R` is a commutative ring, `I` a finite type, and `G`, `H` are group schemes over `Spec R`. The
notions `Ga R`, `rootPoint`, `weylPoint`, `IsRootParametrization` and `IsWeylPoint` are those of
the Library module `Langlands.GroupScheme.Reductive.LocalSplitCell`: `rootPoint u Z c` is the
value `u(c)` of `u : Ga R ⟶ G` at a global function `c` on a test scheme `Z`, and
`weylPoint u u'` is the base point `u'(-1) u(1) u'(-1)`.

## Results

- `rootPoint_comp`: for `u : Ga R ⟶ G` and a homomorphism `f : G ⟶ H`,
  `rootPoint (u ≫ f) Z c = rootPoint u Z c ≫ f`.
- `weylPoint_comp`: `weylPoint (u ≫ f) (u' ≫ f) = weylPoint u u' ≫ f`.
- `IsRootParametrization.comp_iso`: let `i : T_I ⟶ G` and `i' : T_I ⟶ H` be maps from the
  coordinate split torus `T_I = splitTorus (Spec R) I`. Let `Φ : G ≅ H` be an isomorphism with
  `i ≫ Φ.hom = i'`. If `u` is a root parametrization of `i` for the exponent `m : I → ℤ`, then
  `u ≫ Φ.hom` is a root parametrization of `i'` for the same `m`.
- `toUnit_comp_eq_constantPoint`: pulling a base point `n` back to a test scheme `Z` along
  `Z ⟶ 𝟙_` is the Library's `G.constantPoint n Z`.
- `IsWeylPoint.isNormalizingPoint`: if `IsWeylPoint i n f`, that is `n i(t) n⁻¹ = i(f(t))` on
  every test scheme, where `f` acts on `T_I` through `splitTorus.exponentIso`, then `n` is a
  normalizing point of `i` in the sense of the Library (`IsNormalizingPoint`, an equation of
  group-scheme maps `i ≫ int(n) = σ ≫ i`) with `σ = splitTorus.exponentCommIso _ I f`.
- `IsWeylPoint.mem_normalizerPoints`: hence `n ∈ normalizerPoints i`.

## Proof

`rootPoint_comp` and `weylPoint_comp` unfold the definitions: composition of group-scheme
morphisms is composition of the underlying maps, and composition with a homomorphism preserves
products of points (`MonObj.mul_comp`).

`IsRootParametrization.comp_iso` checks the three fields. Representation: the Library lemma
`IsRepresentedBy.comp_iso` moves the represented subgroup functor along `Φ`. The Library lemma
`RelativeRoot.subgroup_comap_of_transport`, applied with the identity of the torus and with
`Φ.symm`, identifies the transported functor with the root subgroup functor of `i'` for the
same character. Closedness: `IsClosedSubgroup.comp_iso`. Equivariance: rewrite `i'` as
`i ≫ Φ.hom` and use `rootPoint_comp`. Composition with `Φ` preserves products and inverses of
points, so the equation for `u` gives the one for `u ≫ Φ.hom`.

`IsWeylPoint.isNormalizingPoint`: both sides are homomorphisms `T_I ⟶ G`, so by `Grp.hom_ext`
it suffices to compare the underlying maps. These are the universal points, obtained by taking
the test scheme `T_I` itself and `t = 𝟙`. There the hypothesis reads
`constantPoint n * i * (constantPoint n)⁻¹ = exponentIso f ≫ i`. The left side is
`i ≫ int(n)` by the Library lemma `GroupScheme.comp_innerIso_hom`.

## Provenance

These are internal lemmas for the proof of the Isomorphism Theorem over a reduced local ring
(`LocalSplitReducedIsomorphismTheoremStatement`), written for this project. They connect the
predicates of `LocalSplitCell` with the Library's normalizer API (`Torus/Maximal.lean`) and
transport them along group isomorphisms. They follow no printed source.
