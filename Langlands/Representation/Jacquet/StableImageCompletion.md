# Stable-image families and the fixed completion

Author: Worker 1775.

This is a derived supporting argument for Renard VI.9.7, printed
pp.205–206 / PDF pp.211–212, using the averaged-image description of
VI.9.1, Remark 2, printed pp.197–198 / PDF pp.203–204. The source is
David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The setting is a topological group `G : Type uG`, a complex module
`V : Type uV`, and a smooth representation `ρ`; the universes are
independent. Neither admissibility nor finite dimensionality is assumed.

`IsIwahoriContraction.exists_uniform_exhaust` upgrades the elementwise
exhaustion field of an Iwahori contraction to one exponent for an arbitrary
compact subset of its upper subgroup. The normalizer inclusion for the Levi
is explicit. The proof covers the compact set by the open preimages of `K`
under conjugation by powers of `g`, takes a finite subcover, and takes the
maximum exponent. The upper contraction law puts every member of that finite
cover into the final conjugate preimage.

Apply this to the opposite contraction, with element `g⁻¹`. Then every
compact subgroup `C ≤ Nbar` is contained in some actual expanded lower
factor `g^b(K ∩ Nbar)g^-b`. The range identity in `StableImageAveraging`
and `stableImage ⊆ range A^b` imply

`stableImage.map (V^K).subtype ⊆ e_K(V^C)`.

This inclusion is proved by `stableImage_le_average_compact_fixed` and
requires both Iwahori contractions, Levi centrality of `g`, and the lower
normalizer inclusion, but no stationarity or closedness assumption.

The component argument is `componentsIn_le_completionFixed_of_average_fixed`.
It assumes that `H` is covered by compact subgroups and, for each compact
`C ≤ H`, cofinally many indices `K ∈ S` satisfy `W K ⊆ e_K(V^C)`.
For a target index `J`, take a compact core `L ≤ J` normalized by `C`, then
a suitable smaller `K ≤ L`. If `v_K = e_K w` with `w ∈ V^C`, compatibility
and `e_L e_K = e_L` give `v_L = e_L w`. Since `C` normalizes `L`, averaging
over `L` preserves `C`-fixedness. Thus the family's `C`-fixed components
are cofinal. The existing fixed-component criterion gives `H`-fixedness.
The normalized outer index `L` need not itself admit an Iwahori factorization.

`oppositeCompressionIndices N M Nbar g` is the set of compact open indices
admitting both contractions for the fixed element `g` and its inverse.
`stableImageCompletion` is the submodule of compatible completion families
whose components at these indices lie in the stable compression images
included in `V`.

`stableImageCompletion_eq_completionFixed` identifies that submodule with
the `Nbar`-fixed completion, retaining the following hypotheses explicitly:
closedness of `Nbar`, normalization of `Nbar` by `M`, centrality of `g` in
`M`, an opposite Iwahori contraction basis for this fixed `g`, covering of
`Nbar` by compact subgroups, and stationarity of the compression range at
each such index.

The first inclusion uses the compact-exhaustion and compact-core argument
above. The reverse inclusion takes the compact averaged-image witness
provided by stationarity in `StableImageAveraging`. An `Nbar`-fixed family
has a smaller component fixed by that compact subgroup. Averaging it to `K`
places `v_K` in the stable image.

This module proves the fixed-completion identification from the stated
structural inputs. It does not establish those inputs for actual rational
parabolics, construct the opposite-Jacquet completion isomorphism, or prove
either exact parent proposition.
