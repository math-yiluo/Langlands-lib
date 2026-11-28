# Cartan matrices of Tits indices of groups isomorphic over the separable closure

Module: `Langlands.GroupScheme.Reductive.TitsIndexCartanIsoComparison`.

Two connected reductive groups over a field `k` that become isomorphic over a separable
closure `k_s` have the same absolute root system. In particular, the Cartan matrices of their
absolute Tits indices agree after a bijection of the simple vertices. This module proves this
comparison for the Library's Tits index data `TitsIndexData` (module
`Langlands.GroupScheme.Reductive.TitsIndex`). The Cartan matrix there is
`d.cartan a b = d.pinning.rootDatum.pairing a b` on the simple vertices
`d.Vertex = d.pinning.base.support` of the split pinning over `SeparableClosure k`. It is a
standard fact. In J. Tits, *Classification of algebraic semisimple groups* (1966), §2.3,
printed p.39 (source `tits-1966-classification-algebraic-semisimple`), the index of a group
over `k` consists of the system of simple roots and the Dynkin diagram of the group over the
separable closure, together with the anisotropic vertices and the star action. The Lean
proofs combine results already in the Library and follow no particular source.

## `SplitPinning.exists_rootDatumEquiv_base_of_iso`

```lean
theorem exists_rootDatumEquiv_base_of_iso (p : SplitPinning G) (q : SplitPinning H)
    (f : G ≅ H) :
    ∃ e : RootPairing.Equiv p.rootDatum q.rootDatum,
      ∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support
```

Here `G` and `H` are affine group schemes over `Spec k`, `p` and `q` are split pinnings of `G`
and `H` (module `Langlands.GroupScheme.Reductive.Pinning`), and `f` is an isomorphism of
group schemes over `k`. The conclusion: some equivalence of root data from `p.rootDatum` to
`q.rootDatum` sends the simple roots of `p` exactly onto the simple roots of `q`.

Proof.

1. The composite `p.inclusion ≫ f.hom` embeds the split torus of `p` in `H` as a maximal
   torus (`IsMaximalTorus.comp_iso`), hence as a maximal split torus
   (`IsMaximalTorus.isMaximalSplitTorus`). The torus of `q` is a maximal split torus of `H`
   too.
2. `smoothMaximalSplitTorusConjugacy` (module
   `Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof`) gives a point `g`
   of `H` over `k` and a torus isomorphism `t` with
   `p.inclusion ≫ f.hom ≫ (H.innerIso g).hom = t.hom ≫ q.inclusion`. It applies because `H`
   is smooth, affine and connected, being connected reductive.
3. Put `F := (f ≪≫ H.innerIso g).symm : H ≅ G` and `φ := t⁻¹` as an isomorphism of
   commutative group schemes. Then `q.inclusion ≫ F.hom = φ.hom ≫ p.inclusion`.
   `rootDatumEquivOfTorusCompatibleIso` (module
   `Langlands.GroupScheme.Reductive.GeometricRootDatumComparison`) turns this square into an
   equivalence `e₀ : RootPairing.Equiv p.rootDatum q.rootDatum`. The root datum is
   contravariant in the group, which is why `F` goes from `H` to `G`.
4. `e₀` need not preserve the chosen bases.
   `StarActionIndependence.exists_weyl_comp_preserves_base` (module
   `Langlands.GroupScheme.Reductive.StarActionIndependenceProof`) gives a Weyl element `w` of
   `q.rootDatum` such that `w ∘ e₀` sends the base of `p` onto the base of `q`. The
   equivalence is `RootPairing.Equiv.comp w e₀`.

## `separableClosureIsoOfBaseChangeIso`

```lean
def separableClosureIsoOfBaseChangeIso {k L : Type u} [Field k] [Field L] [Algebra k L]
    [Algebra.IsSeparable k L] {G H : GroupScheme (Spec (CommRingCat.of k))}
    (f : (GroupScheme.baseChange (algebraBaseMap k L)).obj G ≅
      (GroupScheme.baseChange (algebraBaseMap k L)).obj H) :
    (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G ≅
      (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj H
```

An isomorphism `G_L ≅ H_L` over a separable algebraic extension `L/k` gives an isomorphism
`G_{k_s} ≅ H_{k_s}`. Construction: choose a `k`-embedding `ι : L → SeparableClosure k`
(`IsSepClosed.lift`), so that `Spec k_s → Spec L → Spec k` is the structure map of `k_s`. Base
change `f` along `Spec k_s → Spec L`, and compose on both sides with the comparison
isomorphisms of iterated base change `Descent.pullbackComparison` (module
`Langlands.GroupScheme.Descent.Data`).

## `TitsIndexData.exists_cartanEquiv_of_separableClosureIso`

```lean
theorem exists_cartanEquiv_of_separableClosureIso (d : TitsIndexData G) (d' : TitsIndexData H)
    (f : (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj G ≅
      (GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj H) :
    ∃ v : d.Vertex ≃ d'.Vertex, ∀ a b, d'.cartan (v a) (v b) = d.cartan a b
```

Here `G` and `H` are affine and locally of finite type over `Spec k`. If `G` and `H` are
isomorphic over `SeparableClosure k`, then the simple vertices of their Tits index data
correspond bijectively, with equal Cartan entries.

Proof. The split pinnings `d.pinning.toSplitPinning` and `d'.pinning.toSplitPinning` are split
pinnings of `G_{k_s}` and `H_{k_s}`. Apply `SplitPinning.exists_rootDatumEquiv_base_of_iso` to
them and `f`. This gives an equivalence `E` of root data preserving the bases. Then `v` is the
restriction of the index bijection `E.indexEquiv` to the base supports
(`Equiv.subtypeEquiv`). The Cartan entries agree because root-datum homomorphisms preserve the
pairing (`RootPairing.Hom.pairing`).

A local instance in the module records that the base change of an affine group to
`SeparableClosure k` is again affine, since the base change of an affine morphism is affine.
