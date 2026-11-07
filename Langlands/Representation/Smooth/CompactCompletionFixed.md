# Fixed completion families and cofinal fixed components

Author: Worker 1775.

Module `Langlands.Representation.Smooth.CompactCompletionFixed`.
The main namespace is `Langlands.CompactCompletion`. This is a derived
supporting construction for the completion argument in Renard VI.9.7; it does
not prove either represented-parabolic target.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant argument is VI.9.7, printed pp.205–206 / PDF pp.211–212,
especially the identification of the stable-image limit with the radical-fixed
completion on PDF p.212. Its structural input is VI.9.1, Remark 2, printed
pp.197–198 / PDF pp.203–204. The concrete limit is the already published
`completion`, using normalized compact averages as transition maps.

## Generality

Let `G : Type uG` be a topological group and `V : Type uV` a complex module,
with independent universes. Let `ρ` be a smooth representation of `G` on `V`.
The module assumes no Hausdorff, local compactness or nonarchimedean instance.
It works with the compact open subgroups that exist. Compact subgroups below
are subgroups of `G` compact as subsets of `G`; they need not be open in `G`.

## Compact cores and fixedness

`CompactOpenSubgroup.exists_le_normalizedBy_compact` says that every compact
open `K` contains a compact open `L` normalized by every element of a given
compact subgroup `C`. The proof takes the subgroup of those `x` for which
`c x c⁻¹ ∈ K` for every `c ∈ C`. The tube lemma applied to conjugation over
`C × {1}` shows that this subgroup contains a neighborhood of the identity,
so it is open. It lies in `K` and is closed as an open subgroup, hence is
compact. Reindexing the defining condition by multiplication in `C` proves
normalization.

`component_fixed_of_conj_eq` evaluates the fixed-family equation at an index
unchanged by conjugation. It follows that a family fixed by `C` has `C`-fixed
components at all the compact cores above. Thus
`cofinal_fixed_components_of_fixed` gives a cofinal set of `C`-fixed
components.

Conversely, `translate_eq_of_cofinally_fixed` proves that a completion family
is fixed by `c` if cofinally many of its components are fixed by `c`. To compare
the translated and original components at `K`, choose a common smaller index
below `K` and `c⁻¹ K c` at which the component is fixed. Compatibility and
conjugation of compact averages then identify the two components.

If a subgroup `H` is covered by its compact subgroups, these results give
`mem_completionFixed_iff_cofinal_fixed_components`: a completion family is
`H`-fixed exactly when, for each compact subgroup `C ≤ H`, its `C`-fixed
components form a cofinal set. The covering property is an explicit premise:
for every `h ∈ H` there must be a compact subgroup `C ≤ H` containing `h`.

## The component-subspace comparison

`componentsIn ρ hρ S W` is the submodule of completion families `v` such that
`v_K ∈ W K` for every `K ∈ S`, where `S` is any set of compact open subgroups
and `W K` is a submodule of `V`.

`componentsIn_eq_completionFixed` identifies this submodule with the
`H`-fixed completion under the covering property above and two explicit
structural hypotheses:

1. For every `K ∈ S`, some compact `C ≤ H` satisfies
   `e_K (V^C) ⊆ W K`.
2. For every compact `C ≤ H`, the indices `K ∈ S` with `W K ⊆ V^C` form a
   cofinal set.

For the forward inclusion, condition 2 gives cofinally many `C`-fixed
components, and the fixedness criterion applies. For the reverse inclusion,
choose `C` using condition 1, then choose a smaller index with a `C`-fixed
component by the compact-core argument. Averaging that component to `K`
gives `v_K`, so condition 1 puts it in `W K`.

These are derived statements isolating the limit argument, rather than claims
that Renard states these particular general interfaces. In the intended
application, `W K` is the image in `V` of the stable subspace of `V^K`.
Remark 2 and the cofinal small-subgroup argument in VI.9.7 supply the needed
averaged-image and fixedness conditions. This module does not prove those
conditions for actual represented parabolics, the compact covering of their
radical, or compatibility of Jacquet isomorphisms with transitions. It also
does not construct the isomorphism with the opposite-Jacquet completion.
Those obligations and both exact parent propositions remain open.
