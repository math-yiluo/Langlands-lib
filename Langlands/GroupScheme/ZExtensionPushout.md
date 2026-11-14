# Pushing a central cover out along an embedding of its kernel into an induced torus

This module proves `ZExtensionPushout.exists_zExtension_of_centralCover`, the general step of
the construction of z-extensions. Throughout, `k` is a field. All groups are group schemes over
`Spec k`, and points are morphisms from arbitrary test objects `T` over `Spec k`.

## Main theorem

`exists_zExtension_of_centralCover` assumes the following data:

* `G` and `A₀` are connected reductive (`hG`, `hA₀`);
* `m : A₀ ⟶ G` is a homomorphism whose underlying morphism of schemes is flat and surjective
  (instance arguments), and whose kernel inclusion `kernelι m` is central (`hm`);
* `c₀ : C ⟶ A₀` is a homomorphism whose underlying morphism in `Over (Spec k)` is a
  monomorphism;
* `C` is simply connected (`hC : IsSimplyConnected C`);
* every commutator `x * y * x⁻¹ * y⁻¹` of two `T`-points of `A₀` is `w ≫ c₀` for some
  `T`-point `w` of `C` (`hc₀`);
* `Z` is an induced torus (`hZ : IsInducedTorus Z`);
* `j : kernel m ⟶ Z.toGrp` is a homomorphism whose underlying morphism is a monomorphism.

The conclusion is `Nonempty (ZExtension G)`: a z-extension `1 → Z → H → G → 1` in the sense of
`Langlands.GroupScheme.IsZExtension`. The extension has the given induced torus `Z` as kernel.

## Auxiliary results

Section `General` (over an arbitrary base scheme):

* `mono_of_comp_eq_one`: a homomorphism whose kernel has only the trivial point on every test
  object is a monomorphism of underlying objects.
* `kernelι_comp_eq_one`: `kernelι f ≫ f` is trivial.
* `Dynamic.exists_kernel_point`, reused from [SchemeDecomposition](Dynamic/SchemeDecomposition.md): a point killed by `f` factors through `kernelι f`.
* `prodInl_hom_fst`, `prodInl_hom_snd`, `prodInr_hom_fst`, `prodInr_hom_snd`: the projections
  of the published factor inclusions `prodInl A B` and `prodInr A B` into `A ⊗ B` are the
  identity on the corresponding factor and trivial on the other. They are computed from
  `comp_homOfPoints`.
* `isCentral_prodInr`: the inclusion of a commutative second factor is central.
* Instances `mono_prodInl`, `mono_prodInr`.

Section `Embedding` (over `Spec k`, for `m : A₀ ⟶ G` and `j : kernel m ⟶ Z.toGrp`):

* `embedding m j := lift (kernelι m) j : kernel m ⟶ A₀ ⊗ Z.toGrp`, the map `y ↦ (y, j y)`.
  Its projections are `kernelι m` and `j` (`embedding_hom_fst`, `embedding_hom_snd`). It is a
  monomorphism (`mono_embedding`).
* `isClosedSubgroup_embedding`: its composite with the first projection is the closed immersion
  `kernelι m`. That projection is separated, since `Z` is separated over a field
  (`fieldSeparated`). Hence the embedding is a closed immersion
  (`IsClosedImmersion.of_comp`).
* `isCentral_embedding`: if `kernelι m` is central, so is the embedding. The first component
  is central by hypothesis and the second lies in the commutative group `Z`. Both projections
  are compared with `CartesianMonoidalCategory.hom_ext`.

## Proof of the main theorem

1. **The product.** `Z` is a torus split by the field in `hZ`, hence connected reductive
   (`IsTorus.isConnectedReductive_of_fieldSplitting`). Hence `A₀ ⊗ Z` is connected reductive
   (`directProductReductive`), and in particular smooth and affine.
2. **The quotient `H = (A₀ × Z)/K`**, where `K := kernel m` is embedded by `embedding m j`.
   This embedding is a closed subgroup with normal range, since it is central. The published
   `normalSubgroupQuotient` gives `q : A₀ ⊗ Z ⟶ H` with `H` smooth and affine and
   `IsFppfQuotient (range (embedding m j)) q`. In particular `q` is flat and surjective. It
   is also quasi-compact: its composite with the structure morphism of `H` is the quasi-compact
   structure morphism of the affine `A₀ ⊗ Z`, and `H` is separated (`fieldSeparated`). `H` is connected reductive by the published
   `centralQuotientReductive`, since the range of the embedding lies in the centre. A point
   `g` of `A₀ ⊗ Z` satisfies `g ≫ q = 1` exactly when `g = κ ≫ embedding m j` for some
   point `κ` of `K` (`hker`).
3. **The map `p : H ⟶ G`.** The homomorphism `m' := fst ≫ m : A₀ ⊗ Z ⟶ G` kills
   `kernelι q`: a kernel point of `q` has the form `κ ≫ embedding m j`, and its first
   component `κ ≫ kernelι m` is killed by `m`. The published fpqc descent of homomorphisms
   gives `p := FpqcHomDescent.hom q m' hk` with `q ≫ p = fst ≫ m`.
4. **`p` is flat, surjective and locally of finite presentation.** The published
   `HomImage.exists_image p` factors `p` as a flat, surjective, locally finitely presented map
   `fac` followed by a closed immersion `inc`. The composite `q ≫ fac ≫ inc` equals
   `fst ≫ m`, an epimorphism (`fst` is split by `prodInl`; `m` is flat and surjective). So
   `inc` is an epimorphism and a closed immersion, hence an isomorphism
   (`isIso_of_isClosedImmersion_of_epi_over`). Thus `p` has the three properties of `fac`.
5. **The central torus `iS := prodInr ≫ q : Z ⟶ H`.**
   * It is central (`isCentral_prodInr` and `IsCentral.comp_flat_surjective`).
   * It is a monomorphism by `mono_of_comp_eq_one`. If `s ≫ prodInr ≫ q = 1`, then
     `s ≫ prodInr = κ ≫ embedding m j`. The first projection gives `κ ≫ kernelι m = 1`, so
     `κ = 1`. The second projection then gives `s = κ ≫ j = 1`.
   * `Z` is smooth, connected and affine, so `iS` is a closed subgroup
     (`HomImage.isClosedSubgroup_of_mono`).
6. **Exactness: `IsFppfQuotient (range iS) p`.** The kernel of `p` equals the range of `iS`.
   * Points of the range are killed by `p`, because `prodInr ≫ fst = 1`.
   * Conversely, let `x` be a point of `H` killed by `p`. By
     `SubgroupFunctor.mem_range_of_local_quotient_lift` it suffices to treat local lifts
     `a ≫ x = g ≫ q`. Then `(g ≫ fst) ≫ m = 1`, so `g ≫ fst = κ ≫ kernelι m` for a point
     `κ` of `K`. Put `s := (κ ≫ j)⁻¹ * (g ≫ snd)`. Then
     `g = (κ ≫ embedding m j) * (s ≫ prodInr)`, which gives `a ≫ x = s ≫ iS`.
7. **The simply connected derived group `c := c₀ ≫ prodInl ≫ q : C ⟶ H`.**
   * *Monomorphism.* If `y ≫ c = 1`, then `y ≫ c₀ ≫ prodInl = κ ≫ embedding m j`. The second
     projection gives `κ ≫ j = 1`, so `κ = 1` because `j` is a monomorphism. The first
     projection then gives `y ≫ c₀ = 1`, so `y = 1`. As `C` is smooth, connected and affine
     (it is semisimple, hence connected reductive), `c` is a closed subgroup.
   * *Commutators.* Let `x, y` be points of `H`. Apply
     `mem_range_of_local_quotient_lift` twice to lift `x` and `y` locally to points `g, g'` of
     `A₀ ⊗ Z`. By `hc₀` the commutator of their first components is `w ≫ c₀`. Their second
     components commute in `Z`. So the commutator of `g` and `g'` is `w ≫ c₀ ≫ prodInl`,
     and the commutator of `x` and `y` is locally `w ≫ c`. Hence the range of `c` contains
     all commutators, and `derivedSubgroup_le_range` gives `derivedSubgroup H ≤ range c`.
   * *Reverse inclusion.* `C` is perfect, `derivedSubgroup C = ⊤` (`semisimplePerfect`). Let
     `i' : H' ⟶ H` be a closed subgroup whose range contains all commutators. The published
     subgroup intersection `subgroupIntersectionFst c i'` is a closed subgroup of `C`
     (`isClosedSubgroup_subgroupIntersectionFst`). Its range is the preimage under `c` of the
     range of `i'` (`range_subgroupIntersectionFst_eq_comap`), so it contains all commutators
     of `C`. Therefore it contains every point of `C`, and every point of the range of `c`
     lies in the range of `i'`. By definition of `derivedSubgroup H` as the intersection of
     such ranges, `range c ≤ derivedSubgroup H`.

   Hence `IsDerivedSubgroup c`, and with `hC` the source `H` has simply connected derived
   group.
8. The structure `ZExtension G` is assembled from `Z`, `H`, `iS` and `p` with the fields
   proved above.

## Provenance

This is the pushout step of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Construction 11.4.1 (printed p. 428). KP push the extension
`1 → μ → Z(G)° × G_sc → G → 1` out along an embedding `μ → Z` into an induced torus, putting
`G̃ = (Z × Z(G)° × G_sc)/μ`. KP embed `μ` into `Z` by the inverse of the given embedding; here
it is embedded by `y ↦ (y, j y)`. The two choices differ by the automorphism
`(a, z) ↦ (a, z⁻¹)` of `A₀ × Z`. The module abstracts the
pushout: any flat surjective central cover `m : A₀ ⟶ G` qualifies if a simply connected
subgroup of `A₀` contains its commutators. Its use with `A₀ = R × G_sc` is in
`Langlands.GroupScheme.ZExtensionExistenceProof`. KP state the conclusions briefly ("Since `G̃`
is a quotient of a connected reductive group, it is itself connected and reductive", and the
image of `G_sc` is the derived subgroup). The arguments above supply them for fppf
exactness with nonreduced test objects, using only published Library results.
