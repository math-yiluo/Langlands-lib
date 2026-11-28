# Split components of nested Levi subgroups over a field extension

`Langlands.GroupScheme.fieldLeviSplitComponentInclusion` proves
[`FieldLeviSplitComponentInclusionStatement`](FieldLeviSplitComponentStatement.md).
Let `K/k` be a field extension, `G` a connected reductive group over `k`, `M` a rational
Levi factor of a rational parabolic `P` of `G`, and `M₁` a rational Levi factor of a rational
parabolic `P₁` of `G_K` with `m : M₁ ⟶ M_K` satisfying `m ≫ (l ≫ p)_K = l₁ ≫ p₁`. For split
components `a : A ⟶ M` and `a₁ : A₁ ⟶ M₁`, the theorem gives `j : A_K ⟶ A₁` with
`j ≫ a₁ ≫ m = a_K`.

## Proof

The proof follows the same-field argument of `leviSplitComponentInclusion`
([LeviSplitComponentInclusionProof](LeviSplitComponentInclusionProof.md)) over `K`, with `M_K`
in the role of the larger Levi.

`connectedReductiveFieldExtensionStatement` shows that `G_K` is connected reductive, so
`leviSplitComponentCentralizer` over `K` identifies the centralizer of the image of `A₁` in
`G_K` with the subgroup represented by the closed embedding `l₁ ≫ p₁`. Base change preserves
centrality (`IsCentral.baseChange`) and closed embeddings (`IsClosedSubgroup.baseChange`), so
`a_K` is central in `M_K` and `(l ≫ p)_K` is a closed embedding. Since `A₁` maps to `M_K` by
`a₁ ≫ m`, `IsCentral.range_comp_le_torusCentralizer_of_factor` puts the image of
`a_K ≫ (l ≫ p)_K` in the centralizer of `A₁`, and `SubgroupFunctor.IsRepresentedBy.factorHom`
lifts it to `g : A_K ⟶ M₁`. Cancelling the closed embedding `(l ≫ p)_K` gives `g ≫ m = a_K`.
The morphism `m` is a closed embedding because its composite with `(l ≫ p)_K` is `l₁ ≫ p₁`,
so `IsCentral.of_comp` shows that `g` is central in `M₁`. The base change of the split torus
`A` is split (`IsSplitTorus.baseChange`), and `IsSplitComponent.exists_factor` factors `g`
through `a₁`; `Additive.ofMul` views the factor as `j`.

## Source

J. Arthur, *An introduction to the trace formula* (2005), §17, printed p.99 (PDF p.111),
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`: for a Levi subgroup `M₁` of `G`
over an extension contained in `M`, `𝔞_M` is contained in `𝔞_{M₁}`. Borel–Tits,
*Groupes réductifs* (1965), 4.15 b), printed pp.90–91, `borel-tits-1965-groupes-reductifs`:
Levi subgroups are centralizers of their split components.
