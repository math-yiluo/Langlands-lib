# Existence of z-extensions over every field: proof

This module proves `Langlands.GroupScheme.zExtensionExistence :
ZExtensionExistenceStatement.{u}`. For every field `k` and every connected reductive group
scheme `G` over `Spec k`, there is a z-extension of `G` (`Nonempty (ZExtension G)`). This means
an fppf-exact sequence `1 → Z → H → G → 1` with the following properties:

* `Z` is an induced torus;
* `Z → H` is a closed central subgroup;
* `H` is connected reductive with simply connected derived group.

See `Langlands/GroupScheme/ZExtension.md` and
`Langlands/GroupScheme/ZExtensionExistenceStatement.md` for the definitions.

## Proof

The proof supplies the hypotheses of `ZExtensionPushout.exists_zExtension_of_centralCover`
(module `Langlands.GroupScheme.ZExtensionPushout`). It takes `A₀ := R × C`, where `C` is the
simply connected cover of the derived subgroup and `R` is a central torus.

1. **Derived subgroup, simply connected cover, central torus.** The published
   `simplyConnectedDerivedCoverExistence` gives a derived subgroup `d : D ⟶ G` and a simply
   connected cover `π : C ⟶ D` (`h : IsSimplyConnectedDerivedCover d π`). The published
   `reductiveCentralTorusSurjectivity` gives a closed central torus `i : R ⟶ G`, affine and
   locally of finite type over `k`, such that the multiplication map
   `subgroupProductMap i d : R × D → G` is surjective on underlying schemes. `C` is simply
   connected, hence semisimple and connected reductive. `R` is connected reductive
   (`IsTorus.isConnectedReductive_of_fieldSplitting`).
2. **The central cover `m : R × C ⟶ G`, `(r, c) ↦ i(r) · d(π(c))`.** This is the published
   `CommutatorCoverImage.coverMultiplication i hi`. Its properties are established as in the
   proof of the published `IsSimplyConnectedDerivedCover.exists_comp_eq_commutator`.
   * *Surjective.* Its underlying morphism is `(R ◁ π) ≫ subgroupProductMap i d`. The first
     factor is a base change of the surjective central isogeny `π`
     (`MorphismProperty.pullbackMap`), and the second is surjective by step 1.
   * *Flat.* This follows from `subgroupMultiplication_flat_of_surjective`. Its inputs are:
     `R` and `C` are quasi-compact and locally of finite type, `G` is smooth, `i` is central,
     and `m` is surjective.
   * *Central kernel.* The kernel inclusion `kernelι m` is central by the published
     `CommutatorCoverImage.isCentral_kernel_coverMultiplication`.
3. **`A₀ := R × C` is connected reductive** (`directProductReductive`).
4. **`c₀ := prodInr R C : C ⟶ R × C` contains all commutators.** For points `x, y` of
   `R × C`, take `w` to be the commutator of the second components `x ≫ snd` and `y ≫ snd`.
   Then `w ≫ prodInr` equals `x * y * x⁻¹ * y⁻¹`. The second projections agree by
   `prodInr_hom_snd`. The first projections agree because the commutator of the first
   components is trivial in the commutative group `R`, and `prodInr_hom_fst` makes the first
   component of `w ≫ prodInr` trivial. `prodInr` is a monomorphism (`mono_prodInr`).
5. **Embedding the kernel into an induced torus.**
   * `R × C` is smooth and affine, so the published `maximalTorusExistence` gives a maximal
     torus `jT : T ⟶ R × C`. It is a closed subgroup, hence a monomorphism.
   * By the published `maximalTorusCentralizer`, the centralizer `torusCentralizer jT` equals
     the range of `jT`. So `jT` represents `torusCentralizer jT`.
   * The kernel of `m` is central, so its range lies in the centre of `R × C`
     (`isCentral_iff_range_le_center`), and hence in `torusCentralizer jT`.
   * `SubgroupFunctor.IsRepresentedBy.liftOfLE` therefore gives `κ : kernel m ⟶ T` with
     `κ ≫ jT = kernelι m`. `κ` is a monomorphism because `kernelι m` is one.
   * `IsTorus.exists_mono_inducedTorus` (module `Langlands.GroupScheme.Torus.InducedEmbedding`)
     gives an induced torus `S` and `φ : T ⟶ S` whose underlying morphism is a monomorphism.
   * Put `j := κ ≫ groupHom φ : kernel m ⟶ S`, a composite of monomorphisms.
6. **Conclusion.** `exists_zExtension_of_centralCover hG hA₀ m hm (prodInr R C) hc₀ hC hS j`
   gives the z-extension. Its kernel is the induced torus `S`, and its source is
   `H = ((R × C) × S)/kernel m`.

The proof uses the standard axioms `propext`, `Classical.choice` and `Quot.sound` only.

## Provenance

This proof follows Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Construction
11.4.1 (printed p. 428, PDF p. 459). KP form the extension
`1 → μ → Z(G)° × G_sc → G → 1` and push it out along an embedding of `μ` into an induced torus.
The implemented route differs from KP in two inputs.

* In place of the identity component `Z(G)°` of the centre, it uses the published closed central
  torus `R` with `R × D → G` surjective (`reductiveCentralTorusSurjectivity`). Only centrality
  and the surjectivity are used.
* KP embed `μ` into an induced torus by presenting the Galois module `X^*(μ)` as a quotient of
  a free module. The Library has no Galois splitting theorem for groups of multiplicative
  type. The proof instead places the central kernel inside a maximal torus of `R × C`, which is
  self-centralizing, and embeds that torus into an induced torus by the dual lattice
  presentation (module `InducedEmbedding`).

The remaining steps of KP's construction are in `Langlands.GroupScheme.ZExtensionPushout`:
`G̃` is connected reductive, `Z` is central with `G̃/Z ≅ G`, and the image of `G_sc` is the
derived subgroup.
