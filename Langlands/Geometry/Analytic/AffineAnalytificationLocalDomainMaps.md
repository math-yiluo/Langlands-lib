# Bounded maps out of local-domain algebras of a polynomial-locus analytification

This module collects affine facts about the Library's polynomial-locus
analytification `Space K P` of `Spec A`, for a finite polynomial presentation
`P` of a `K`-algebra `A`. The main theme is that a bounded map out of the
algebra of a local affinoid domain of the atlas `atlas K P` is determined by its
values on `A`, and that a `K`-algebra map from `A` to a presented affinoid algebra
extends boundedly to such an algebra exactly when its spectrum lands in the
domain. The module is internal supporting material for the analytic structure on
the glued analytification of a scheme (`SchemeAnalytificationAnalyticStructure`).

## Contents

Charts and coordinates.

* `coordinate_eq_algebraMap`: the coordinates of the `m`-th chart algebra
  `algebra K P m` are the images of the generators of `A` under
  `PolynomialLocus.algebraMap`.
* `chart_hom_ext`: two bounded maps out of `algebra K P m` that agree on the image
  of `A` are equal (`hom_ext_coordinate`).
* `comap_comp`: the spectrum map of a composite is the composite of the spectrum
  maps.
* `restriction_algebraMap`: the polydisc restriction `restriction K P h` sends the
  image of `a ∈ A` at level `k` to its image at level `m`.

Points given by algebra maps. For a presented affinoid algebra `R` and
`α : A →ₐ[K] R`, the Library map `affinoidBaseMap K P R α : M(R) → Space K P` is
used throughout.

* `chart_comap_eq_affinoidBaseMap`: if a bounded map `γ` out of the `m`-th chart
  algebra restricts to `α` on `A`, then `chart K P m (comap γ x)` is
  `affinoidBaseMap K P R α x`. The proof compares `γ` with the Library's
  `affinoidChartMap` on a common larger chart, using `chart_hom_ext` and
  `chart_pull`.
* `pointSeminorm_affinoidBaseMap` and `kernel_affinoidBaseMap`: the seminorm of
  `affinoidBaseMap K P R α x` is `a ↦ x (α a)`, and its kernel is the preimage
  under `α` of the kernel of `x`.
* `affinoidBaseMap_comp_left` and `baseMap_affinoidBaseMap`: naturality in `R`
  (composition with a bounded map `ρ : R → R'`) and in `A` (composition with an
  algebra map `A → B`, through the Library's `baseMap`).
* `exists_chart_lift`: if `affinoidBaseMap K P R α` lands in the range of the
  `m`-th chart, then `α` extends to a bounded map out of `algebra K P m`. The
  proof starts from `affinoidChartMap` at the radius level of `α` and factors it
  through the restriction from a common larger chart, using
  `represents_restriction`.

Affinoid domains of chart algebras. For a full domain `D` of `algebra K P m`,
`domainAlgebraMap P D : A →ₐ[K] D.algebra` is `D.baseMap` composed with
`PolynomialLocus.algebraMap`.

* `domain_hom_ext`: bounded maps out of `D.algebra` are determined on `A`
  (uniqueness in `D.represents` plus `chart_hom_ext`).
* `chart_spectrumMap_comap` and `affinoidBaseMap_domainAlgebraMap`: the point of
  `Space K P` given by a bounded map `β` out of `D.algebra` is the affinoid base
  map of `β ∘ domainAlgebraMap P D`. In particular, the points of `D.algebra` go
  to the chart images of the points of `D`.
* `exists_domain_lift`: if `affinoidBaseMap K P R α` lands in
  `chart K P m '' D.locus`, then `α` factors through `domainAlgebraMap P D` by a
  bounded map. The proof applies `exists_chart_lift` and then the universal
  property of `D`.

Local domains of the atlas. For `L : LocalDomain (atlas K P)`,
`localAlgebraMap P L` is `domainAlgebraMap` at the chart of `L`. The wrappers
`localDomain_hom_ext`, `ambientMap_comap`, `affinoidBaseMap_localAlgebraMap` and
`exists_localDomain_lift` restate the domain results in terms of
`L.ambientMap` and `L.locus`.

Compatibility with restrictions and with induced maps.

* `atlas_restriction_algebraMap`: the atlas restrictions are the polydisc
  restrictions on the image of `A`.
* `inclusion_localAlgebraMap`: for an inclusion `f : U ⟶ V` of local domains,
  `f.restriction (localAlgebraMap P V a) = localAlgebraMap P U a`. The proof
  evaluates `f.comp_chart` on a common chart containing both charts, given by
  `atlas_hasDirectedCharts`, and rewrites both sides with
  `domainChartRestriction_of_chartSubset`.
* `strongHom_pullback_algebraMap`: for `φ : A →ₐ[K] B` and presentations `P`, `Q`,
  every bounded pullback of the Library strong map `strongHom K P Q φ` sends the
  image of `a` to the image of `φ a`. The proof compares the pullback with the
  selected chosen-chart pullback on a common chart, using
  `pullback_comp_restriction`, `ofDirected_pullback_selected` and
  `pullback_algebraMap`.
* `localDomainPullback_localAlgebraMap`: the same compatibility for the bounded
  maps `localDomainPullback` between local domains. The target local domain `V` is
  included in the whole original chart `q` that contains its chart and the image
  of the source chart. Then `localDomainPullback_target`,
  `localDomainPullback_comp_baseMap` and
  `localChartPullback_of_parent_admissible` reduce the claim to
  `strongHom_pullback_algebraMap`. The coherence of the strong map is
  `strongHom_hasCoherentPullbacks`.
* `saturatedHom_pullback_localAlgebraMap`: the bounded pullbacks of the
  saturated morphism `saturatedHom K P Q φ` are compatible with the
  coordinate-algebra maps of the chosen local-domain representatives and `φ`.
  These pullbacks are by definition the maps `localDomainPullback`.

## Provenance

Internal. The statements are elementary consequences of the Library's
constructions in `AffineAnalytificationGluing`, `AffineAnalytificationAtlas`,
`AffineAnalytificationAffinoidMap`, `AffineAnalytificationMap`,
`AffineAnalytificationLocalizedMap` and the general local-domain machinery
(`AtlasDomainCategory`, `CoherentStrongLocalDomain`). They make precise, for the
polynomial-locus model, the identification
`Hom_k(M(R), Spec A) = Hom_k(A, R)` used in step (1) of the proof of Theorem
3.4.1 of Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean
Fields* (1990), printed p.64/PDF p.78 (registered source
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`, SHA256
`9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`). They also
make precise its restriction to affinoid domains. No spectral theory, Tate
acyclicity or seminorm comparison is used. Bounded extensions come from the norm
bound built into `affinoidChartMap`.
