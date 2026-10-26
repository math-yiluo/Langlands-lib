# Whole generation opens under pullback of line-bundle sections

`Langlands.SchemeModule.LineBundlePullbackSectionOpenStatement.{u}` is the
following proposition, for arbitrary schemes and scheme morphisms in universe
`u`:

```text
∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (L : LineBundle X)
    (s : GlobalSections L.obj),
  trivializationOpen ((Scheme.Modules.pullback f).obj L.obj)
      (pullbackSection f L.obj s) =
    f ⁻¹ᵁ (trivializationOpen L.obj s).
```

Here `LineBundle X` is the published full subcategory of actual module sheaves
that are locally free of rank one. The module on the left is Mathlib's actual
`Scheme.Modules.pullback f` applied to `L.obj`. The published
`pullbackSection f L.obj s` evaluates at one the composite of the inverse
canonical `pullbackUnitIso f` and the pullback of `sectionHom L.obj s`.
The section morphism `sectionHom` takes one to the section.

The published `trivializationOpen M s` is the supremum of all opens on which
the restriction of `sectionHom M s` is an isomorphism. The published
`maximalTrivialization` in `SectionLocusComparison` identifies it as the largest
such open. Thus the proposition is equality in `Y.Opens` of the entire
generation open and the inverse image of the entire original generation open.

The sole condition is the local rank-one property carried by `L`. The
proposition quantifies over all sections and all scheme morphisms; it includes
empty and nonreduced schemes. It imposes no flatness, affineness, finiteness,
compactness, tensor-comparison, residue-comparison, or monoidal premise.

## Internal provenance and proof obligation

This is an internal derived statement combining the already published actual
section-pullback construction in `SectionResidue`, the generation-locus
construction in `SectionLocus`, and the local rank-one definition in
`Picard.LineBundle`. It does not claim to transcribe a separate external
theorem, and this file supplies a proposition definition rather than a proof.

An unconditional proof must establish that the section morphism associated
to `pullbackSection` agrees with `pullbackSectionHom`, and compare rank-one
frames under pullback. The local ring homomorphisms induced by a scheme
morphism preserve and reflect units, so a proof may use local rank-one
trivializations to preserve and reflect the frame condition, then recover
equality of the whole opens. An alternative unconditional route is allowed.
Published results available to such a proof include
`IsLocallyFreeRankOne.pullback` in `Picard.LineBundlePullback`, the stalk and
maximality comparisons in `SectionLocusComparison`, and
`lineBundleSectionResidueComparison` in `SectionResidueComparison`.
The eventual proof remains a separate exact-target obligation.
