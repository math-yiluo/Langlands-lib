# Harris's domains form a distinguished covering of Ω with the nerve of the building

Author: Worker 21.

This module states, without proof, the properties of Harris's domains
`U(f) = Res⁻¹(B(f, ε))` of Drinfeld's upper half space that Harris uses. The
domains are defined in module `DrinfeldBuildingCovering`. The module contains
one Prop-valued definition,
`Langlands.Analytic.DrinfeldUpperHalfSpace.DistinguishedCoveringStatement`.

## Statement

Let `F` be a non-Archimedean local field (`NontriviallyNormedField`,
`IsUltrametricDist`, `ProperSpace`). Let `K` be a complete ultrametric
nontrivially normed field with `[NormedAlgebra F K]`, and `d ≥ 1`. Then there
is `ε₀ > 0` such that for every `0 < ε < ε₀`:

1. covering: the union of the `facetDomain K {e} ε` over all vertices `e` is
   all of `Ω = Omega F K d`;
2. distinguished: for every facet `S` (`NormClass.IsFacet S`) there are
   analytic domains `V`, `W` of the saturated presentation of `Ω`, compact in
   the sense `IsCompactDomain` (compact and Hausdorff), with
   `facetDomain K S ε = V \ W`;
3. nerve: for every nonempty finite set `S` of vertices, `facetDomain K S ε`
   (the intersection of the `U(e)`, `e ∈ S`) is nonempty if and only if `S` is
   a facet.

The analytic domains are those of
`SaturatedAtlasPresentation.ofSaturation (presentation F K d)`, the constructed
saturation of the published atlas of `Ω` (module `DrinfeldUpperHalfSpace`). Its
space is `Omega F K d`.

## Original source and derived provenance

Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper half
spaces* (1997), registered as `harris-1997-drinfeld-cohomology`, SHA256
`aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`, §2,
printed p.90 / PDF p.16: "Berkovich defines a distinguished open subset of an
analytic space X to be the complement V − U, where U and V are compact analytic
subsets of X." And, after defining `B(e, ε)` and `B(f, ε)`: "Then for each facet
e ⊂ BT the subset U(e) = Res⁻¹(B(e, ε)) ⊂ Ω is distinguished, and the covering
of Ω by the {U(e)} is admissible (cf. [BC])." The proof of Lemma 6, printed
pp.91–92 / PDF pp.17–18, computes compactly supported cohomology by the Čech
spectral sequence of this covering, with terms indexed by facets and
differentials given by the face relations. This uses item 3.

Harris 1999, *Galois properties of cohomological automorphic forms on GL(n)*,
registered as `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
SHA256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, §2,
printed p.303 / PDF p.5: "The open subsets U(e) are distinguished, in
Berkovich's sense; i.e., can be realized as the complement V(e) − V'(e), where
V(e) and V'(e) are compact analytic sets."

Derived choices:

- `B(e, ε)` is formed with the Goldman–Iwahori distance instead of a Euclidean
  metric (see `DrinfeldBuildingCovering`). This distance is polyhedral in each
  apartment, which is what one expects to make the complements analytic
  domains.
- Harris allows any small `ε`; here `ε` ranges over an interval `(0, ε₀)`.
- Item 1 is stated for the vertex domains. The facet domains are their
  intersections.
- In item 2, "compact analytic sets" are compact analytic domains.
