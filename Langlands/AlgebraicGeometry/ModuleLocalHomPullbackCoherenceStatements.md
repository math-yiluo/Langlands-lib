# Identity and composition targets for local internal-Hom pullback

These proposition-valued definitions state coherence of the fixed canonical
`localHomPullback` from `ModuleLocalHomPullback` for arbitrary schemes and
module sheaves. They do not prove the laws.

`LocalHomPullbackIdentityStatement` identifies pullback along the identity with
conjugation by the actual Mathlib `Scheme.Modules.pullbackId`: its forward map
on the source module is followed by the given local map, and then by its inverse
on the target module, all restricted to the open U.

`LocalHomPullbackCompositionStatement` compares successive pullbacks along
f : X → Y and g : Y → Z with pullback along f ≫ g. Starting with a local map h
on U in Z, the left side pulls h back along g and then along f. The right side
is the local pullback along f ≫ g, conjugated by the forward and inverse maps
of Mathlib's actual `Scheme.Modules.pullbackComp f g` on the source and target
modules, respectively. Both sides are maps between the successive pullbacks
on f⁻¹(g⁻¹U), which is definitionally the inverse image of U under f ≫ g.

`LocalHomPullbackCoherenceStatement` is the conjunction of these two universally
quantified laws. Neither law adds flatness, finite presentation or local freeness
hypotheses. No isomorphism claim about the internal-Hom comparison is made.

## Provenance

These are derived coherence targets for the canonical local-map construction
underlying the internal-Hom comparison in the registered source
`stacks-relative-differentials-internal-hom-2026-10-21`, *Stacks Project — Relative
differentials and internal Hom (HTML snapshot 2026-10-21)*, folder SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`.
The opening of `01CM.html`, Section 17.22 ([tag 01CM](https://stacks.math.columbia.edu/tag/01CM)),
identifies internal-Hom sections with local module morphisms. Lemma 17.22.5
([tag 0C6I](https://stacks.math.columbia.edu/tag/0C6I)) displays the canonical
pullback comparison. The identities here express functoriality of pullback of
these local maps and use the canonical identity and composite comparisons of
Mathlib's chosen pullback functors. They are implementation-level derived
targets, not separate statements quoted from that lemma. Its hypotheses for
invertibility are not needed for these coherence targets.
