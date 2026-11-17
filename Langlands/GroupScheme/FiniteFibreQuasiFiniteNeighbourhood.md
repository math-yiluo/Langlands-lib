# Quasi-finite neighbourhoods of finite fibres of affine group schemes

This supporting unit implements the quasi-finite-locus construction in SGA 3, Exposé IX, Lemma 6.3 for affine group schemes locally of finite type. Every scheme, field and group in the module belongs to the arbitrary universe `u`.

For a group scheme `G` over a scheme `S`, with structure morphism locally of finite type, `quasiFiniteUnitLocus G` is the open subset

\[
U=\eta_G^{-1}\bigl(\operatorname{QF}(G/S)\bigr)\subseteq S.
\]

Here `η[G.X].left` is the unit section and `G.X.hom.quasiFiniteLocus` is Mathlib's open locus of quasi-finiteness. This definition needs no affineness hypothesis.

The supporting theorems have the following meanings.

- `isFinite_of_open_chart_algClosed`: over an algebraically closed field, an affine group scheme locally of finite type is finite if it has an open subscheme locally quasi-finite over the field through which the unit section factors.
- `isFinite_of_open_chart`: the same conclusion holds over any field.
- `locallyQuasiFinite_of_open_chart`: over any scheme, an affine group scheme locally of finite type is locally quasi-finite if it has such an open chart containing the entire unit section.
- `locallyQuasiFinite_baseChange_quasiFiniteUnitLocus`: if `G` is affine and locally of finite type over `S`, its base change to `quasiFiniteUnitLocus G` is locally quasi-finite.
- `mem_quasiFiniteUnitLocus_of_isFinite_fibre`: for any `G` locally of finite type over `S`, a point `s` whose residue-field fibre is finite belongs to `quasiFiniteUnitLocus G`.
- `exists_locallyQuasiFinite_neighbourhood_of_isFinite_fibre`: for an affine `G` locally of finite type, a finite residue-field fibre at `s` gives an open neighbourhood `U` of `s` on which the base-changed group is locally quasi-finite.

In the algebraically closed field case, the locally quasi-finite chart is locally Artinian and has discrete underlying space. Its point above the unit therefore maps to an open singleton of the group. The published theorem `FiniteCenterOfNoCentralSubgroups.isFinite_of_open_singleton` proves finiteness, including the possible nonreduced structure. Over an arbitrary field the proof extends scalars to an algebraic closure, applies this result to the pulled-back chart and unit, then descends finiteness along the faithfully flat quasi-compact field extension. The general-base chart theorem applies the field theorem to every residue-field fibre and uses Mathlib's fibrewise criterion for local quasi-finiteness.

For the neighbourhood construction, let `Q` be the quasi-finite locus of `G → S`. Over `U`, the restriction of the unit to `Q` gives a section of `Q ×ₛ U`; its composite with the pulled-back open immersion is the base-changed unit. The chart theorem then applies. If the fibre at `s` is finite, its underlying space is discrete; Mathlib's characterization of quasi-finiteness by an open singleton in the fibre shows that the unit at `s` is in `Q`, hence `s ∈ U`.

No flatness, reducedness, finite-presentation or noetherian hypothesis is used. The construction and chart lemmas are internal reorganizations of the quasi-finite-locus and group-translation argument in Lemma 6.3, using published field geometry and fpqc descent. This unit proves local quasi-finiteness; the further finiteness conclusion for subgroups of multiplicative-type groups requires additional results.

Source: SGA 3, Exposé IX, Gille–Polo recomposed edition (2009), registered source `sga3-expose-ix-gille-polo-2009`, Lemma 6.3, p.54 (original margin p.66). The chart lemmas are internal reorganizations of its group-translation step, using published field geometry.
