# Boundary supports and the half modulus for Renard VII.3.5 (ii)

Author: Worker 115. Module
`Langlands.Representation.Intertwining.InnerLeviBoundaryTransfer`.

This module is supporting material for Renard VII.3.5 (ii) (David Renard,
*Représentations des groupes réductifs p-adiques*, French version of 9 July 2026,
VII.3.5, printed pp.237–240 / PDF pp.243–246). It uses the same setting as
`InnerLeviIntegrationDomain`:

- represented parabolics `P₁ = MN₁` and `P₂ = MN₂` of `G` with `P₁(F), P₂(F) ⊂ Q(F)`,
  where `Q = LU`;
- parabolics `P₁' = MN₁'` and `P₂' = MN₂'` of `L` whose rational points are
  `Pᵢ'(F) = Pᵢ(F) ∩ L(F)` inside `G(F)` (`hPL₁`, `hPL₂`).

Renard's proof restricts functions on `G(F)` to `L(F)`. Two facts make that work: the
boundary of the identity double coset in `L(F)` maps into the corresponding boundary in
`G(F)`, and the half modulus `δ_U^{1/2}` is trivial where the integration domain lives.
These are internal helpers derived for this proof; the literature does not state them
separately.

## Declarations

- `HaarModulus.closedHalfCharacter_eq_one_of_mem_isCompact`: in a locally compact
  nonarchimedean group, take a closed subgroup `U` and a subgroup `P` that normalizes it.
  The half modulus `δ_U^{1/2}` of `P` is `1` at every point of a compact subgroup `J` of
  `P`. Proof: the modulus `δ_U` has open kernel, so it is continuous, and a continuous
  positive character is trivial on a compact subgroup
  (`RankinSelberg.LastRowReduction.eq_one_of_isCompact`). The kernel of `δ_U^{1/2}`
  equals the kernel of `δ_U` (`closedHalfCharacter_eq`, `halfCharacter_ker`).
- `IsSemidirectDecomposition.eq_one_of_mem_of_mem`: in a semidirect decomposition
  `P = M ⋉ U`, an element of both `M` and `U` is `1`. Its Levi projection is the element
  itself and also `1`.
- `mem_identityDoubleCoset_iff`, `identityDoubleCoset_eq`: the identity double coset
  `P · 1 · Q` is the product set `P Q`.
- `mem_mul_of_map_mem_mul`: if `x ∈ L(F)` and `emb x ∈ P₁(F) P₂(F)`, then
  `x ∈ P₁'(F) P₂'(F)`. Proof: by `nestedParabolicPointDecomposition`,
  `Pᵢ(F) = Pᵢ'(F) U(F)`. Write `emb x = e₁ u₁ e₂ u₂` with `eᵢ ∈ emb(Pᵢ'(F))` and
  `uᵢ ∈ U(F)`. Since `Q(F)` normalizes `U(F)`, this is `e₁ e₂ u` with
  `u = e₂⁻¹ u₁ e₂ u₂ ∈ U(F)`. Also `u = (e₁ e₂)⁻¹ emb x ∈ L(F)`, so `u = 1` by the
  semidirect decomposition `Q(F) = L(F) ⋉ U(F)`. Injectivity of `emb` gives `x = z₁ z₂`
  with `zᵢ ∈ Pᵢ'(F)`.
- `halfModulus_eq_one_of_mem_innerRadical`: let `c = δ_U^{1/2}` be the half modulus of
  `Q(F)` acting on `U(F)`. Then `c(x) = 1` for every rational point `x` of the unipotent
  radical `N'` of a closed subgroup `P'` of `L`. Here `x` is viewed in `Q(F)` through
  `leviPointsEquiv`. Proof: `isLimitOfCompactSubgroups_pointImage_radical` puts the image
  of `x` in a compact subgroup of `N'(F) ⊆ Q(F)`, and the first lemma applies.
- `map_mem_identityBoundary`: for the canonical point topologies on `L(F)` and `G(F)`,
  `emb` maps the boundary `closure(P₁'P₂') \ P₁'P₂'` of the identity double coset of `L(F)`
  into the boundary `closure(P₁P₂) \ P₁P₂` of `G(F)`. Proof: `emb` is continuous
  (`isEmbedding_leviPoints`) and maps `P₁'(F) P₂'(F)` into `P₁(F) P₂(F)`. So it maps the
  closure into the closure. A point outside `P₁'(F) P₂'(F)` maps outside `P₁(F) P₂(F)` by
  `mem_mul_of_map_mem_mul`.

The semidirect-intersection theorem is reused from `Langlands.Representation.Aubert.General.SemidirectIntersection`.
