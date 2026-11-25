# Harris's domains `U(f)` of Drinfeld's upper half space are distinguished

This module states, without proof, item 2 of
`DistinguishedCoveringStatement` (module `DrinfeldCoveringStatement`) on its
own: Harris's domains `U(f) = Res⁻¹(B(f, ε))` are distinguished. It contains
one Prop-valued definition,
`Langlands.Analytic.DrinfeldUpperHalfSpace.FacetDomainDistinguishedStatement`.

## Statement

Let `F` be a non-Archimedean local field (`NontriviallyNormedField`,
`IsUltrametricDist`, `ProperSpace`). Let `K` be a complete ultrametric
nontrivially normed field with `[NormedAlgebra F K]`, and `d ≥ 1`
(`[NeZero d]`). Then there is `ε₀ > 0` such that for every `0 < ε < ε₀` and
every facet `S` of the building (`NormClass.IsFacet S`) there are analytic
domains `V`, `W` of `SaturatedAtlasPresentation.ofSaturation (presentation F K d)`,
both compact in the sense `IsCompactDomain` (compact and Hausdorff), with

`facetDomain K S ε = V.carrier \ W.carrier`.

`facetDomain K S ε` is `Res⁻¹(B(S, ε))` (module `DrinfeldBuildingCovering`).
The analytic domains are those of the constructed saturation of the published
atlas of `Ω = Omega F K d` (module `DrinfeldUpperHalfSpace`).

The body of the definition is item 2 of `DistinguishedCoveringStatement`
verbatim, with its own `ε₀`. Items 1 and 3 of that statement concern only
norms on `F^{d+1}` and points of `Ω` over them; this item is the one that
needs the analytic geometry of `Ω` (rational domains and the apartments of the
building).

## Original source

Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper half
spaces* (1997), registered as `harris-1997-drinfeld-cohomology`, SHA256
`aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`, §2,
printed p.90 / PDF p.16: "Berkovich defines a distinguished open subset of an
analytic space X to be the complement V − U, where U and V are compact analytic
subsets of X." And, after defining `B(e, ε)` and `B(f, ε)`: "Then for each facet
e ⊂ BT the subset U(e) = Res⁻¹(B(e, ε)) ⊂ Ω is distinguished, and the covering
of Ω by the {U(e)} is admissible (cf. [BC])."

Harris 1999, *Galois properties of cohomological automorphic forms on GL(n)*,
registered as `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, §2,
printed p.303 / PDF p.5: "The open subsets U(e) are distinguished, in
Berkovich's sense; i.e., can be realized as the complement V(e) − V'(e), where
V(e) and V'(e) are compact analytic sets."

## Derived choices

These are the choices of `DistinguishedCoveringStatement`, item 2:

- `B(e, ε)` is formed with the Goldman–Iwahori distance `NormClass.distRatio`
  (multiplicative form) instead of a Euclidean metric.
- Harris allows any small `ε`; here `ε` ranges over an interval `(0, ε₀)`.
- "Compact analytic sets" are compact analytic domains.
