# Pullback of sections and values on residue-field fibres

For a scheme map `f : Y → X`, an actual module sheaf `M : X.Modules`
and a global section `s`, `pullbackSectionHom f M s` is the composite

```
𝒪_Y → f*𝒪_X → f*M.
```

The first arrow is the inverse of the constructed canonical
`Langlands.Scheme.Modules.pullbackUnitIso f`. The second arrow is the
actual module pullback of `sectionHom M s`, the map taking one to `s`.
`pullbackSection f M s` evaluates this composite on one over the top
open of `Y`; its result belongs to `GlobalSections (f*M)`. Thus both the
module and the section are constructed using Mathlib's pullback functor.

For `x : X`, `residueFibre M x` is the actual pullback of `M` along
`X.fromSpecResidueField x : Spec κ(x) → X`. It is a module sheaf on that
one-point scheme, rather than an abstract fibre supplied as additional
data. `residueSection M s x` specializes `pullbackSection` to this map.
`NonvanishingAt M s x` means that this element of the global sections
of the residue-field fibre is nonzero. `nonvanishingLocus M s` is the
set of such points. The membership lemma unfolds these definitions.
These constructions apply to every module sheaf; no local freeness
or quasi-coherence assumption is required.

This is derived infrastructure for the nonvanishing condition in Stacks
Project Lemma 17.25.10, tag [01CY](https://stacks.math.columbia.edu/tag/01CY).
The source describes the condition as the germ not belonging to
`𝔪_x L_x`. For schemes the geometric residue-field presentation pulls the
section back to `Spec κ(x)`. Here that geometric presentation is constructed
directly, without choosing a stalk basis or a trivialization. The retained
source is `stacks-invertible-picard-ampleness-2026-10-21`, directory SHA256
`2a0bbd01484fc7cef97110a88cf4b3e472574fbbb9469d037170744a1462f835`,
file `01CY.html`, statement and proof of Lemma 17.25.10.

This definition unit asserts no comparison with the quotient of a stalk
by its maximal ideal, the stalk-frame predicate, or the local
trivialization locus. In particular it does not assert that
`nonvanishingLocus` is open for an arbitrary module. The line-bundle
comparison, openness and local trivialization are separate statement
and proof obligations. No ampleness predicate or tensor-power assertion
is included here.
