# Finite volume through a split kernel with compact rational quotient

This module proves the Levi reduction step for finite volume of the actual norm-one adelic
rational quotient `normOneRationalQuotientHaarMeasure` of `AdelicGroupHaarMeasure`. Let
`F` be a number field, `G` and `L` affine finite-type group schemes over `F`, and
`p : G ⟶ L`, `j : L ⟶ G` homomorphisms with `j ≫ p = 𝟙 L`. Write `U` for the
scheme-theoretic kernel `GroupScheme.kernel p` with inclusion `GroupScheme.kernelι p`.
If `U(F) \ U(𝔸)` (`RationalQuotient F U`) is compact and `L(F) \ L(𝔸)¹` has finite
Haar volume, then `G(F) \ G(𝔸)¹` has finite Haar volume.

The module assumes nothing about smoothness, connectedness, reductivity or unipotence. In
the intended application `L` is a Levi factor of a smooth connected `G` and `U` its
unipotent radical, but here these are only the hypotheses stated above.

## Statement

`LeviReductionFiniteVolumeStatement` is the Prop-valued statement quantified over every
number field `F` (in universe `u`), every pair `G`, `L` with `IsAffine` and
`LocallyOfFiniteType` instances, and every `p`, `j` with `j ≫ p = 𝟙 L`: compactness of
`RationalQuotient F (GroupScheme.kernel p)` and `IsFiniteMeasure` of
`normOneRationalQuotientHaarMeasure F L` imply `IsFiniteMeasure` of
`normOneRationalQuotientHaarMeasure F G`. The theorem
`leviReductionFiniteVolumeStatement` proves it by
`isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_section`, which is the same
assertion for fixed data, with the two hypotheses as instance arguments.

## Supporting results

* `GroupScheme.isEmbedding_affinePointPostcomp`: for an affine group scheme `G` over
  `Spec R` and a morphism `f : G.X ⟶ H.X` whose map on global sections is surjective,
  postcomposition `x ↦ x ≫ f` on points with coefficients in a topological `R`-algebra
  `A` is a topological embedding. The point topology is induced by evaluation on global
  sections (`isEmbedding_affinePointEvaluation`), and precomposition with a surjection is
  an embedding of function spaces, with a left inverse given by precomposition with a
  chosen section (`Function.surjInv`).
* `LeftCosetSpace.exists_isCompact_cover`: if `Γ \ H` is compact for a subgroup `Γ` of a
  locally compact topological group `H`, there is a compact `K ⊆ H` with
  `∀ h, ∃ γ ∈ Γ, γ * h ∈ K`. Finitely many images of interiors of compact neighbourhoods
  cover the quotient, because the quotient map is open; `K` is the union of those
  neighbourhoods.
* `isEmbedding_map_of_surjective`, `isEmbedding_mapNormOne_of_surjective`: a homomorphism
  of group schemes surjective on global sections induces topological embeddings
  `AdelicGroupPoints.map` and `mapNormOne` (the latter as a restriction to subtypes).
* `mem_normOneSubgroup_of_compactSpace`: if `RationalQuotient F U` is compact, every
  adelic point of `U` lies in the norm-one subgroup. For an algebraic character `χ`, the
  character norm `characterNorm F U χ` is trivial on rational points, so its range is the
  image of the compact covering set `K`. A compact subgroup of `ℝ≥0ˣ` is trivial
  (the published `continuousMonoidHom_eq_one_on_compactSubgroup`).
* `kernel_isClosedImmersion`, `kernel_isAffine`, `kernel_locallyOfFiniteType`: for a
  homomorphism `p : G ⟶ L` with `L` affine, the kernel inclusion is a closed immersion
  (the base change of the unit section of the separated scheme `L`); hence the kernel is
  affine when `G` is, and of finite type when `G` is.

## Proof of the main theorem

`isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_section` applies the published
`LeftCosetSpace.Semidirect.isFiniteMeasure_haarQuotientMeasure` of
`LeftCosetSemidirectFiniteVolume` with `H = G(𝔸)¹`, `N = U(𝔸)¹`, `M = L(𝔸)¹`,
`i = mapNormOne (kernelι p)`, `j = mapNormOne j`, `p = mapNormOne p`, the discrete
subgroups `Γ = rationalNormOneSubgroup F G` and `ΓM = rationalNormOneSubgroup F L`.
Its hypotheses are verified as follows.

* `p ∘ j = id` on norm-one points follows from `j ≫ p = 𝟙 L` by associativity of
  composition of points.
* `p ∘ i = 1` and "every `h` with `p h = 1` is in the range of `i`" come from the
  published `GroupScheme.kernelPointsEquiv`, which identifies `𝔸`-points of the kernel with
  `𝔸`-points of `G` killed by `p`. For the second, the preimage point of `U(𝔸)` is norm
  one by `mem_normOneSubgroup_of_compactSpace`.
* `i` is an embedding by `isEmbedding_mapNormOne_of_surjective`; the kernel inclusion is a
  closed immersion into an affine scheme, hence surjective on global sections
  (`IsClosedImmersion.isAffine_surjective_of_isAffine`). The maps `j` and `p` are
  continuous homomorphisms.
* The compact set covering `N` is the preimage in `U(𝔸)¹` of the compact set `K0 ⊆ U(𝔸)`
  given by `LeftCosetSpace.exists_isCompact_cover`; it is compact because `U(𝔸)¹` is
  closed (`isClosed_normOneSubgroup`). The covering elements are images of rational points
  `rationalNormOne F U z`, whose images under `i` are rational by
  `mapNormOne_rationalNormOne`.
* `j` maps `ΓM` into `Γ` by `mapNormOne_rationalNormOne`.
* Finiteness of `haarQuotientMeasure ΓM _` is the instance on
  `normOneRationalQuotientHaarMeasure F L`, which is this measure by definition.

## Provenance

This is internal support for the finite-volume assertion of Getz–Hahn, *An Introduction to
Automorphic Representations*, Theorem 2.6.3 (printed page 69), which Getz–Hahn state for
smooth connected `G` and prove by citing Conrad [Con12a, Theorem 1.3.6]. The module is
one step of the characteristic-zero route chosen for this proof: pass from `G` to a Levi
factor `L`, using compactness of the rational adelic quotient of the unipotent radical. The
formulation through a split homomorphism `p` with section `j` and its kernel, rather than
through a Levi decomposition, is internal; it avoids constructing quotient group schemes.
The supporting lemmas are standard, and their formulations and proofs here are internal.
