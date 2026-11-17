# Proof: conjugacy and density of Cartan subgroups

Worker 387.

The module proves

```lean
theorem Langlands.GroupScheme.cartanConjugacyDensity :
    CartanConjugacyDensityStatement.{u}
```

for the unchanged published proposition of
[`Cartan.ConjugacyDensityStatement`](ConjugacyDensityStatement.md), at an arbitrary universe `u`
and in every characteristic, with no additional hypotheses. Fix an algebraically closed field
`k : Type u` and a group scheme `G` over `Spec k` with `Smooth G.X.hom`, `IsAffineHom G.X.hom`
and `ConnectedSpace G.X.left`. The theorem gives:

1. for Cartan subgroups `c : C ⟶ G` and `c' : C' ⟶ G`, a `k`-point `g` of `G` with
   `SubgroupFunctor.range (c ≫ (G.innerIso g).hom) = SubgroupFunctor.range c'`;
2. for a Cartan subgroup `c : C ⟶ G`, an open dense `U : Set G.X.left` contained in the range of
   the conjugation morphism `G × C ⟶ G`, `(x, y) ↦ x c(y) x⁻¹`.

The module adds one lemma on schemes, three lemmas and one definition on Cartan subgroups, and
the target theorem. It uses only published Library results and adds no axioms. Axioms of the
target theorem: `propext`, `Classical.choice`, `Quot.sound`.

## An open dense subset in the range of a tangent-surjective morphism

`Langlands.AlgebraicGeometry.TangentSmoothness.exists_isOpen_dense_subset_range_of_isTangentSurjectiveAt`:
let `K` be a field and `f : X ⟶ Y` a morphism with `f ≫ q = p`, where `p : X ⟶ Spec K` is
smooth, `q : Y ⟶ Spec K` is locally of finite type and `Y` is irreducible. If `f` is surjective
on rational tangent vectors (`IsTangentSurjectiveAt p q f x`) at a `K`-rational point `x` of `X`
(`IsRationalPoint p x`), then there is an open dense `U ⊆ Y` with `U ⊆ Set.range f`.

Proof. This is the proof of the Library theorem `denseRange_of_isTangentSurjectiveAt` (same
namespace, module `Langlands.AlgebraicGeometry.TangentSmoothness`), which concludes only
`DenseRange f`. Here the open set it builds is kept. `f` is locally of finite presentation
(`locallyOfFinitePresentation_of_comp_eq`), and the image point of `x` lies in the smooth locus
of `f` (`mem_smoothLocus_of_isTangentSurjectiveAt`). The restriction `f.smoothLocus.ι ≫ f` of
`f` to its smooth locus is smooth (Mathlib's `Scheme.Hom.smoothLocus_eq_top_iff` and
`Scheme.Hom.preimage_smoothLocus_eq`). Smooth morphisms are open maps, so
`U := Set.range (f.smoothLocus.ι ≫ f)` is open. It is nonempty, since it contains the image of
`x`. A nonempty open subset of an irreducible space is dense (`IsOpen.dense`). Finally
`U ⊆ Set.range f`.

## The conjugation map of a dynamic centralizer

The declarations of this and the next section are in the namespace
`Langlands.GroupScheme.CartanConjugacyDensity`, inside which the module sets `backward.isDefEq.respectTransparency false`, as the Borel proof below does.
`conjugation iZ` is the Library's
`Langlands.GroupScheme.BorelPointContainment.conjugation`
([`Absolute.BorelPointContainmentDensity`](../Absolute/BorelPointContainmentDensity.md)): for
`iZ : Z ⟶ G` it is `fst G.X Z.X * (snd G.X Z.X ≫ iZ.hom.hom) * (fst G.X Z.X)⁻¹`, by definition.

`exists_isOpen_dense_subset_range_conjugation_centralizer`: let `k` be algebraically closed, `G`
smooth, affine and connected, `χ : (Gm (Spec k)).toGrp ⟶ G` a cocharacter, and `iZ : Z ⟶ G` with
`Z` smooth and affine and `(Dynamic.centralizer χ).IsRepresentedBy iZ`. Then the range of
`(conjugation iZ).left` contains an open dense subset of `G.X.left`.

Proof. This is the proof of the Library lemma
`BorelPointContainment.denseRange_conjugation_centralizer` by Worker 1095
([`Absolute.BorelPointContainmentProof`](../Absolute/BorelPointContainmentProof.md)), copied
with only its last step changed. That lemma has the same hypotheses and concludes
`DenseRange (conjugation iZ).left`.

- `exists_generic_affinePoint` gives a generic `k`-point `u` of `𝔾_m` for `χ` (an algebraically
  closed field is infinite).
- The range of `χ` lies in its dynamic centralizer (`torusCentralizer_gm_eq_dynamicCentralizer`
  and `range_le_torusCentralizer`), so `χ = χ' ≫ iZ` with `χ' := hZ.factorHom χ _`.
- `z₀ := (e ≫ u⁻¹) ≫ χ'` is a `k`-point of `Z`, where `e` identifies `Spec k` with its
  `CommAlgCat` form `P`. The constant point of `z₀ ≫ iZ` over `P` is `(u ≫ χ)⁻¹`.
- `G.X ⊗ Z.X` is smooth over `k` (`smooth_tensor`) and `G.X.left` is irreducible
  (`DynamicConnected.irreducibleSpace_of_smooth`).
- The lemma of the previous section, applied to `conjugation iZ` at the rational point
  `lift 1 z₀`, reduces the claim to tangent surjectivity there. Lemma B of the Borel proof,
  `isTangentSurjectiveAt_conjugation`, reduces tangent surjectivity to writing every Lie vector
  `W` of `G` as `Ad(g₀⁻¹) X · dιZ(ξ) · X⁻¹`, with `g₀ = (u ≫ χ)⁻¹` the constant point of
  `z₀ ≫ iZ`, `X` a Lie vector of `G` and `ξ` a Lie vector of `Z`. As `g₀⁻¹ = u ≫ χ`, this is
  `exists_adjoint_sub_add_eq` applied to `Additive.ofMul W`, translated to multiplicative
  notation with `adjoint_toMul` and `lieKernelTargetLinear_toMul`.

## Cartan subgroups

`groupIso`: an isomorphism `φ : T ≅ T'` of commutative group schemes gives the isomorphism
`T.toGrp ≅ T'.toGrp` with components `CommGroupScheme.groupHom φ.hom` and
`CommGroupScheme.groupHom φ.inv`.

`exists_range_comp_innerIso_eq` (part 1): let `k` be algebraically closed, `G` smooth, affine
and connected, and `c : C ⟶ G`, `c' : C' ⟶ G` Cartan subgroups. Then there is a `k`-point `g`
of `G` with `SubgroupFunctor.range (c ≫ (G.innerIso g).hom) = SubgroupFunctor.range c'`.

Proof. By `IsCartanSubgroup.exists_centralizer_representation`, `c` represents
`torusCentralizer j` and `c'` represents `torusCentralizer j'` for maximal tori
`j : T.toGrp ⟶ G` and `j' : T'.toGrp ⟶ G`. The published theorem `maximalTorusConjugacy`
(Milne 17.10) gives a `k`-point `g` and an isomorphism `φ : T ≅ T'` with
`j ≫ (G.innerIso g).hom = CommGroupScheme.groupHom φ.hom ≫ j'`. Write `ι := G.innerIso g`. Then

- `range (c ≫ ι.hom) = (torusCentralizer j).comap ι.inv`
  (`SubgroupFunctor.IsRepresentedBy.comp_iso`);
- `torusCentralizer j = (torusCentralizer (j ≫ ι.hom)).comap ι.hom`
  (`torusCentralizer_eq_comap_of_iso`), and pulling back along `ι.hom` and then `ι.inv` is the
  identity (`SubgroupFunctor.comap_iso_hom_inv`);
- `torusCentralizer (CommGroupScheme.groupHom φ.hom ≫ j') = torusCentralizer j'`
  (`torusCentralizer_eq_of_iso` with `groupIso φ`), and `torusCentralizer j' = range c'`.

So `range (c ≫ ι.hom) = range c'`.

`exists_isOpen_dense_subset_range_conjugation` (part 2): let `k` be algebraically closed, `G`
smooth, affine and connected, and `c : C ⟶ G` a Cartan subgroup. Then the range of
`(conjugation c).left` contains an open dense subset of `G.X.left`.

Proof. Again `c` represents `torusCentralizer j` for a maximal torus `j : T.toGrp ⟶ G`. `T` is
split, because `k` is algebraically closed
(`IsTorus.isSplitTorus_of_finiteGaloisSplitting` with the published theorem
`torusFiniteGaloisSplitting`). The Library theorem `IsSplitTorus.exists_cocharacter_centralizer_eq`
gives a cocharacter `ν` of `T` whose dynamic centralizer is the centralizer of `T`:
`Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ j) = torusCentralizer j`. So `c` represents
the dynamic centralizer of the cocharacter `χ := CommGroupScheme.groupHom ν ≫ j` of `G`. `C` is
smooth (`IsCartanSubgroup.smooth_connected`, module `Torus.CentralizerConnected`) and affine
(`IsClosedSubgroup.isAffineHom`). The previous section's lemma for `χ` and `iZ := c` gives the
open dense subset.

## The main theorem

`Langlands.GroupScheme.cartanConjugacyDensity`: for `k`, `G` and the instances of the statement,
part 1 is `exists_range_comp_innerIso_eq` and part 2 is
`exists_isOpen_dense_subset_range_conjugation`. The morphism in the statement,
`fst G.X C.X * (snd G.X C.X ≫ c.hom.hom) * (fst G.X C.X)⁻¹`, is `conjugation c` by definition, so
part 2 applies without rewriting.

## Use of the hypotheses

- `IsAlgClosed k`: conjugacy of maximal tori (`maximalTorusConjugacy`); maximal tori are split;
  `k` is infinite, so a generic point of `𝔾_m` exists.
- `Smooth G.X.hom`, `IsAffineHom G.X.hom`, `ConnectedSpace G.X.left`: hypotheses of
  `maximalTorusConjugacy` and of the Borel-proof lemmas; smoothness of the Cartan subgroup; `G` is
  irreducible, so the nonempty open image of the smooth locus is dense.

## Comparison with the literature

The target is the second sentence of Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, Proposition 17.44 (printed p.364), with its proof on printed p.365.
For part 1 the Lean proof follows Milne: the maximal tori `T` and `T'` are conjugate by a
`k`-point `g` (17.10), so `C' = C_G(gTg⁻¹) = g C_G(T) g⁻¹`.

For part 2 Milne cites Theorem 17.33(a) (printed p.362): `⋃_{g∈G(k)} g|C|g⁻¹` contains a nonempty
open subset of `G`, proved through Lemma 17.32(b) (pp.361-362) and a dimension count. The Lean
proof argues differently. It chooses a cocharacter `χ` of the split torus `T` with
`C_G(χ) = C_G(T)`, and shows that the conjugation map `G × C ⟶ G` is surjective on tangent spaces
at the `k`-point `(1, χ(u)⁻¹)` for a generic `u ∈ 𝔾_m(k)`; this argument is Worker 1095's, from
the Library proof that every rational point lies in a Borel subgroup. The image of the smooth
locus of the conjugation map is then a nonempty open subset of `G`, dense because `G` is
irreducible. The statement Markdown explains why this scheme-theoretic form of density is
Milne's assertion about the union of the Cartan subgroups.
