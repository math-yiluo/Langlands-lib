# Full strong local maps glued after a constructed source refinement

This derived construction glues a literally compatible family of full strong
maps on actual original-chart domains over an arbitrary quasinet cover.
It constructs a refining source selection and a full global strong numerator
on that selected source. The complete local bounded pullbacks are recovered
on every selected-source domain.

## Provenance and scope

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Definition 1.3.1 on printed p.23 / PDF p.20 supplies the domain convention;
Proposition 1.3.2 on printed p.24 / PDF p.21 motivates morphism descent;
the G-topology paragraph on printed p.25 / PDF p.22 supplies quasinet
coverings. The registered original is `berkovich-1993-etale-cohomology`,
SHA-256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

The construction uses actual original-chart atlas presentations. Its input
local maps agree as whole strong maps on their actual intersections.
Strictification of matching families given only in the source quotient,
identification with all finite-gluing analytic spaces and full analytic
morphism descent remain separate obligations.

## Implemented construction

`StrongHom.restrictSelectedDomainSource` retains the actual domain subspace
and every bounded pullback, retaining the identical original index in the
selected-source chart. Direct restriction to smaller domains commutes with
this operation by full strong-map extensionality.

`OriginalDomainStrongMatchingFamily.selectedSource` transports every given
local map to the selected source. The commutation law and the given literal
intersection equations prove literal matching there.

`domainCoverSourceSelection` applies the constructed domain-cover selection
to the top local selections. Thus it retains precisely the original charts
contained in some cover member. The quasinet cover proves the resulting
selection is locally refining; its defining witnesses prove every retained
whole chart lies in a member of the transported cover.

`refinedGlue` applies full strong chart reconstruction to the transported
matching family on that source. `refinedGlue_restrictSubspace` recovers every
selected local map, including all admissible bounded algebra homomorphisms.
The field, ambient space, chart-index and cover-index universes are
independent. Empty cases are governed by the quasinet condition; no
nonemptiness premise is added.
