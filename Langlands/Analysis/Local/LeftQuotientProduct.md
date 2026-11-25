# Left quotients of product groups

This module collects generic facts about left quotients `H \ G` (the Library's
`LeftQuotient H`, the quotient of `G` by the relation `x ~ h x`) of product
groups. It is a helper for premise B (`UnipotentClassProductStatement`) of the
published reduction `ArchimedeanFactorizationReduction`. There, the
semilocal part of `N(𝔸) \ GL_m(𝔸)` is identified with a product of local
quotients `N(F_v) \ GL_m(F_v)` and of a compact factor, and two right-invariant
measures on it are compared. Everything here is standard point-set topology and
measure theory. The provenance is internal: the module records routine facts in
the form that proof needs, and no literature result is formalized.

All declarations live in the namespace `Langlands.QuotientIntegration`.

## Membership in a coset

- `leftQuotient_mk_eq_mk_iff`: the classes of `x` and `y` in `H \ G` agree iff
  `y * x⁻¹ ∈ H`.
- `leftQuotient_mk_out_eq`: for the representative `out` of the class of `x`,
  `x * out⁻¹ ∈ H`.

## Products of two groups

Let `A ≤ G₁` and `B ≤ G₂` be subgroups of topological groups.

- `leftQuotientProdHomeomorph A B : LeftQuotient (A.prod B) ≃ₜ LeftQuotient A × LeftQuotient B`
  sends the class of `(x, y)` to `([x], [y])` (`leftQuotientProdHomeomorph_mk`,
  which holds by `rfl`). The inverse sends `(p, q)` to the class of
  `(p.out, q.out)`. The forward map is continuous because it lifts a continuous
  map through the quotient map. The inverse is continuous because the product of
  the two quotient maps is an open quotient map (`IsOpenQuotientMap.prodMap`
  applied to the Library's `leftQuotient_isOpenQuotientMap`), and composing the
  inverse with that product map gives the quotient map of `G₁ × G₂`.
- `leftQuotientProdHomeomorph_rightTranslate`: the homeomorphism intertwines
  the right translation by `g = (g₁, g₂)` on `(A × B) \ (G₁ × G₂)` (the
  Library's `rightTranslate`) with the product of the right translations by `g₁`
  and `g₂`. On classes this holds by `rfl`.
- `prodSubgroupHomeomorph A B : (A.prod B) ≃ₜ* A × B` is Mathlib's
  `Subgroup.prodEquiv` with both directions shown continuous.
  `prodSubgroupHomeomorph_apply` records its formula.

## Products of a family of groups

Let `A i ≤ G i` be subgroups of topological groups for `i` in an arbitrary
index type `ι`, and let `Subgroup.pi Set.univ A ≤ ∀ i, G i` be their product.

- `leftQuotientPiHomeomorph A : LeftQuotient (Subgroup.pi Set.univ A) ≃ₜ ∀ i, LeftQuotient (A i)`
  sends the class of `x` to `([x i])_i` (`leftQuotientPiHomeomorph_mk`). The
  inverse is built from representatives as above, and its continuity uses
  `IsOpenQuotientMap.piMap`. An arbitrary product of open quotient maps is an
  open quotient map, so `ι` need not be finite.
- `leftQuotientPiHomeomorph_rightTranslate`: the coordinatewise intertwining of
  right translations.
- `piSubgroupHomeomorph A : (Subgroup.pi Set.univ A) ≃ₜ* ∀ i, A i`.

## Measures

- `measurePreserving_map_symm_of_conj`: let `Θ : Q ≃ᵐ X` be a measurable
  equivalence, `P` a measure on `X`, and `T : Q → Q` a measurable map with
  `Θ (T q) = T' (Θ q)` for a map `T'` that preserves `P`. Then `T` preserves the
  transported measure `Measure.map Θ.symm P`. The proof rewrites
  `T ∘ Θ.symm = Θ.symm ∘ T'` and composes pushforwards. In the proof of premise B
  this gives right invariance of a product measure moved to a quotient by the
  homeomorphisms above.
- `isMulRightInvariant_of_continuousMulEquiv`: let `e : N ≃ₜ* M` be an
  isomorphism of topological groups with Borel σ-algebras, where `M` is locally
  compact and second countable. If `M` carries a right-invariant Haar measure
  `μ`, then every Haar measure `ν` on `N` is right invariant. Proof: `map e ν` is
  a Haar measure on `M` (`ContinuousMulEquiv.isHaarMeasure_map`), so by Mathlib's
  uniqueness of left Haar measures (`isMulLeftInvariant_eq_smul`) it is a scalar
  multiple of `μ` and therefore right invariant. The Library’s
  `isMulRightInvariant_map` in `QuotientMeasureEquiv` pushes this back along `e.symm`, and
  `map e.symm (map e ν) = ν`. In the proof of premise B this shows that a Haar
  measure on the unipotent subgroup of the semilocal product group is right
  invariant, as the Library's quotient-measure uniqueness theorem
  `exists_pos_smul_eq_of_rightInvariant_quotient` requires.
