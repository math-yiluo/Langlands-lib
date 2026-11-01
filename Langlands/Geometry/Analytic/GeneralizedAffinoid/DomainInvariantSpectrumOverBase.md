# Invariant represented-domain spectrum actions over the base

Authors: Worker 56 and Worker 36.

## Setting

Let `K : Type u` be a complete ultrametric normed field, let
`P : PresentedAffinoidAlgebra K` be an actual finite positive-polyradius
affinoid quotient, and let `G : Type v` be a topological group. Fix
`ρ : DomainSpectralAction G P`, whose continuity is into the explicitly
constructed full represented-domain spectral topology.

For an open subgroup `H` of `G`, the imported category
`InvariantDomain ρ H` contains all supplied full represented domains whose
loci are preserved by every element of `H`. Its arrows are the actual
bounded restrictions over `P`. The previously constructed
`invariantSpectrumActionFunctor ρ H` realizes these domains by their section
algebra spectra with inverse-pullback actions and bounded restriction
pullbacks.

The present construction keeps the actual structural maps to the original
spectrum and proves their equivariance and naturality. Its target is
`Action TopCat H`: the operators for fixed group elements are continuous.
Joint continuity in the group and spectrum variables remains a separate
analysis obligation.

## Structural maps and commuting triangles

`restrictedGlobalSpectrumAction ρ H` restricts the actual original
`globalSpectrumAction ρ` along the subgroup homomorphism `H → G`.
The space remains `BanachSpectrum P`. Its evaluation formula is

```text
(g • x)(a) = x((ρ(g : G)).inv(a)).
```

`invariantSpectrumActionToBase ρ H d` is the spectrum pullback along
`d.obj.baseMap : P → d.obj.algebra`, with its existing boundedness and
continuous pullback. Its underlying function is exactly `d.obj.spectrumMap`,
and the two application lemmas expose this equality and the formula

```text
structuralMap(x)(a) = x(d.obj.baseMap(a)).
```

The proof of equivariance applies the imported `spectrumMap_smul` to the
continuous inclusion of `H` in the domain's open stabilizer. That theorem
comes from the full bounded-map compatibility of the constructed section
action with the structural map. It does not infer algebra-map equality
from agreement on spectrum points.

For an actual inclusion `f : d ⟶ e`,
`invariantSpectrumActionToBase_naturality` proves that the spectrum
restriction from `d` to `e`, followed by the structural map of `e`, equals
the structural map of `d`. After extensionality of action and topological
morphisms, this is precisely `f.hom.spectrumMap_over_base`. Its algebraic
content is the defining equation
`f.hom.restriction.comp e.obj.baseMap = d.obj.baseMap` of the retained
bounded restriction.

## Diagram over the original spectrum action

`invariantSpectrumActionToBaseNatTrans ρ H` packages the structural maps as
a natural transformation to the constant restricted global action.
`invariantSpectrumActionOverFunctor ρ H` uses Mathlib's `Over.lift` to
produce the diagram in the overcategory of `restrictedGlobalSpectrumAction
ρ H`. Its objects contain the actual section spectrum actions and the
proved equivariant structural maps. Its arrows contain the original
equivariant restriction pullbacks with the proved commuting triangle.
The object and arrow lemmas identify these components definitionally.

`invariantSpectrumActionOverFunctor_forget` states that forgetting
structural maps recovers the entire original invariant action diagram.
`invariantSpectrumActionOverFunctor_forget_topological` further forgets
actions and recovers the full invariant-domain inclusion followed by
`Domain.toTopologicalSpace K P`. Both equalities are reflexive.

## Provenance and scope

This is an internal categorical consequence of the actual full domain
category, constructed section actions and bounded spectrum pullbacks.
It adapts Worker 36's published `StrictTestDomain/SpectralOverBase`
structural-map and overcategory pattern to arbitrary full represented
domains over positive-polyradius quotients. The source module's continuous
action target is replaced here by `Action TopCat`, using the already
constructed operators without assuming the still separate joint
continuity result. No new literature theorem is asserted.

Trivial scalar valuations, nilpotents, zero quotients and empty loci or
spectra remain allowed. This unit does not identify the represented-domain
test topology with the topology using all compact analytic domains.
General analytic gluing, structure sheaves, analytic etale sites and
Harris tower specialization remain further constructions.
