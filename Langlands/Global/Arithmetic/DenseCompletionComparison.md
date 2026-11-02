# Completions of number fields at dense nonarchimedean embeddings

This module identifies a field with an adic completion of a number field once the
number field embeds densely into it. Throughout, `K` is a number field and `F` is a
complete, nontrivially normed field whose norm is ultrametric. The input is a ring
homomorphism `j : K →+* F` with dense range.

## The prime

- `norm_ringOfIntegers_le_one`: for every algebraic integer `a`, `‖j a‖ ≤ 1`. The
  image `j a` is integral over `ℤ`, hence over the valuation ring of the norm
  valuation `NormedField.valuation` of `F`, and valuation rings are integrally
  closed.
- `exists_ne_zero_norm_lt`: by density, `K` has nonzero elements of arbitrarily
  small norm. A small nonzero element of `F` is approximated more closely than its
  own norm, and the ultrametric inequality bounds the norm of the approximation.
- `normLtOneIdeal j` is the set of algebraic integers `a` with `‖j a‖ < 1`. It is an
  ideal by the ultrametric inequality and the bound above. It is prime
  (`normLtOneIdeal_isPrime`): one is not in it, and if neither factor of a product has
  norm below one, both factors have norm one. It is nonzero
  (`normLtOneIdeal_ne_bot`): a nonzero element `n / d` of norm below one has
  numerator `n` of norm below one, since `‖j d‖ ≤ 1`.
- `densePrime j hj` is this ideal as an element of `HeightOneSpectrum (𝓞 K)`, and
  `mem_densePrime` states its membership condition `a ∈ v.asIdeal ↔ ‖j a‖ < 1`.

## Valuation and norm

Write `v = densePrime j hj`.

- `norm_le_one_of_valuation_le_one` and `norm_lt_one_of_valuation_lt_one`: if
  `v.valuation K x ≤ 1`, Mathlib writes `x * d = n` with `n` integral and `d` an
  integer outside `v`; then `‖j d‖ = 1`, so `‖j x‖ = ‖j n‖`. This is at most one,
  and below one when `v.valuation K x < 1`, because then `n ∈ v`.
- `valuation_le_one_iff` and `valuation_lt_one_iff` add the converse directions by
  passing to `x⁻¹`.
- `valuation_lt_iff`: `v.valuation K x < v.valuation K y ↔ ‖j x‖ < ‖j y‖`, obtained
  from the previous item applied to `x / y`.

## Completion

- `isUniformInducing_of_lt_iff`: for any valuation `w` on `K` whose strict order
  agrees with the norm order along `j`, and for which `K` has nonzero elements of
  arbitrarily small norm, the map `WithVal w → F` given by `j` is uniformly inducing.
  The proof compares the basis of valuation entourages
  `Valued.hasBasis_uniformity` with the metric basis
  `Metric.uniformity_basis_dist` through
  `Filter.HasBasis.isUniformInducing_iff`. Each value `γ` of the valuation is a
  quotient `w r / w s` (`Valuation.exists_div_eq_of_unit`), which matches the radius
  `‖j r‖ / ‖j s‖`.
- `completionPackage`: `F` with the coercion `j` is an `AbstractCompletion` of
  `WithVal w`; it is complete, Hausdorff, uniformly inducing and dense.
- `completionRingEquiv w j hj hu : w.Completion ≃+* F` is Mathlib's comparison
  equivalence `AbstractCompletion.compareEquiv` between the uniform-space completion
  and this package. It is a ring isomorphism because it is the extension
  `UniformSpace.Completion.extensionHom` of the ring map. Its two continuity lemmas
  come from uniform continuity of the comparison maps, and `completionRingEquiv_coe`
  states that it extends `j`.
- `exists_adicCompletion_ringEquiv`: the main theorem. With `v = densePrime j hj`, it
  composes Mathlib's identification `HeightOneSpectrum.adicCompletion.equiv` of
  `v.adicCompletion K` with `(v.valuation K).Completion`, which is continuous in both
  directions, with `completionRingEquiv`. The result `φ : v.adicCompletion K ≃+* F`
  is continuous in both directions and satisfies
  `φ (algebraMap K (v.adicCompletion K) x) = j x`. The prime is characterized by
  `a ∈ v.asIdeal ↔ ‖j a‖ < 1`.

No topology on `F` other than its norm topology is used. Applications to fields that
carry a separately defined topology must first identify that topology with the
norm topology.

## Provenance

This is a supporting construction for the totally real Galois realization in
Henniart (2000), Section 3.3, printed page 449 (PDF page 11), source
`henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`. That passage
asks for a topological isomorphism between the completion `(E⁺)_{v₀}` of a totally
real number field at a finite place and the given p-adic field. Henniart does not
say how to identify a completion. The construction here is internal: the prime cut
out by the norm, the comparison of valuation and norm, and the use of the
uniqueness of completions. It is the standard argument that a dense embedding into
a complete field realizes the completion. Every lemma is proved from Mathlib's
completion and adic-valuation API, and no fact about p-adic fields is used.
