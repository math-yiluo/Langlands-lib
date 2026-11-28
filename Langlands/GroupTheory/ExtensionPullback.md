# Pullback of a group extension

Gan and Gao form the local covering L-group by pulling back an extension along
`W_F → Fˣ/Fˣⁿ` and describe its canonical splitting over the kernel of this
map. The global construction uses the analogous Weil projection. The source is
Gan–Gao, *The Langlands–Weissman program for Brylinski–Deligne extensions*,
Astérisque 398 (2018), §5.2, printed p. 213 (PDF p. 231), §13.2, printed pp.
244–245 (PDF pp. 262–263), and the first paragraph of §13.3, printed p. 245
(PDF p. 263). The registered source `gan-gao-2018-langlands-weissman-program`
has SHA-256 `fabbe056bdec2a5d57a22a0d3ad275640d0343c3f71092a7df427f7ebaebe892`.

In `Langlands.GroupTheory`, `Pullback p f` is the equalizer subgroup of the
maps `p ∘ fst` and `f ∘ snd` on `E × D`. `pullbackFst` and `pullbackSnd`
restrict the coordinate homomorphisms. The subgroup membership proof gives
`pullback_condition`. The paired homomorphism `pullbackLift` takes values in the
subgroup by compatibility, and its coordinate equations and `pullback_hom_ext`
give the universal property.

For a Mathlib `GroupExtension A E B` with projection `p`, `pullbackExtension`
embeds `a` as `(i(a), 1)` and projects to the second coordinate. Injectivity
follows from the first coordinate. A pair whose second coordinate is `1` has
first coordinate in `ker p`, so exactness of the original sequence gives its
kernel representative. Surjectivity comes from lifting `f(d)` under `p`.
`pullbackExtension_central` checks commutation in both coordinates when the
original kernel is central.

On `ker f`, the pair `(1, d)` satisfies the compatibility equation.
`pullbackKerLift` gives this homomorphism into the original pullback and its
second coordinate is the subgroup inclusion. `pullbackKerSplitting` packages
the same formula as a Mathlib splitting of the extension over `ker f`.
These are constructions on abstract groups. The field and Weil group enter
through the choice of extension and base homomorphism.
