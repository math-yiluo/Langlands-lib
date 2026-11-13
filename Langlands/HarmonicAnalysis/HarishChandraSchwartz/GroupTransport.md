# Transport of Harish-Chandra Schwartz spaces

This module derives transport of the Schwartz-space construction in `Basic` under a
topological group isomorphism matching its weights. It is an internal compatibility
construction.

The source convention is Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), III.6, printed p.271 (PDF p.37), including property (1).
The new equivalence is derived from those definitions rather than a separately numbered
source assertion.

For groups `G`, `H` with topologies, let `e : H ≃ₜ* G` and let real weights satisfy
`ΞH(h) = ΞG(e(h))` and `σH(h) = σG(e(h))`. The groups may have independent universes.
The weights are arbitrary; positivity, height estimates and measure choices are not
needed for this comparison.

`nu_comp_equiv` reindexes the supremum defining every extended-real seminorm `ν_r`.
It uses only an equivalence of types and matching weights. `IsBiInvariant.comp_monoidHom`
pulls bi-invariance back to the preimage subgroup under a group homomorphism.
`CompactOpenSubgroup.comap` forms the preimage of a compact open subgroup along `e`;
compactness follows from the homeomorphism.

`Level.comapLinear` sends a function `f` to `f ∘ e` on the corresponding preimage level.
`Level.seminorm_comapLinear` proves equality of all real seminorms defining the level
topologies. `Level.comap` is the resulting continuous complex-linear map.

`Space.comapLinear` restricts precomposition to the supremum of the level submodules.
Its membership proof uses the supremum property directly, so it does not require a
separate hypothesis that a compact open subgroup exists. `Space.comap` is continuous
by the locally convex inductive-limit universal property from `Basic`: each level
restriction factors through its continuous level pullback followed by the inclusion
of the preimage level.

The recorded construction `Space.comapEquiv` is a continuous complex-linear equivalence
from `Space ΞG σG` to `Space ΞH σH`. Its forward map is `f ↦ f ∘ e` and its inverse is
`f ↦ f ∘ e.symm`, as recorded by the two application lemmas. The inverse is continuous
by the same level argument with the inverse isomorphism. The inverse identities
follow pointwise from those of `e`. `Space.nu_comapEquiv` preserves every `ν_r`
exactly on Schwartz functions; the earlier `nu_comp_equiv` also applies to arbitrary
functions whose seminorms may be infinite.

This result compares chosen weights and the existing locally convex topologies.
It proves neither analytic estimates for the actual reductive-group weights nor
completeness, convolution or Plancherel assertions.
