# The quadratic extension cut out by an outer star action

Module: `Langlands.GroupScheme.SimplyConnected.OuterTypeAQuadraticExtension`
(namespace `Langlands.GroupScheme.TitsIndexData`).

Throughout, `K` is a field, `G` an affine group scheme of finite type over
`Spec K`, and `d : TitsIndexData G` actual Tits index data. Absolute Galois
elements are `σ : SeparableClosure K ≃ₐ[K] SeparableClosure K`, with the Krull
topology from Mathlib, and `d.star σ` is the Library's full star action on the
simple vertices `d.Vertex`.

## Definitions

- `starKernel d : Subgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K)` is the
  set of `σ` with `d.star σ a = a` for every simple vertex `a`. It is a subgroup
  by `star_one` and `star_mul`; `mem_starKernel_iff` unfolds membership.
- `starField d : IntermediateField K (SeparableClosure K)` is
  `IntermediateField.fixedField (starKernel d)`, the fixed field of the star
  kernel inside the separable closure.

## Results

- `starKernel_isOpen`, `starKernel_isClosed`: the proved Library theorem
  `starActionContinuity` (applied to `d.pinning` with `E = SeparableClosure K`)
  gives a finite-dimensional intermediate field `L` such that every `σ` fixing
  `L` pointwise has trivial star action. Hence `L.fixingSubgroup ≤ starKernel d`.
  `L.fixingSubgroup` is open (`IntermediateField.fixingSubgroup_isOpen`), so the
  star kernel is open by `Subgroup.isOpen_mono`, and closed by
  `Subgroup.isClosed_of_isOpen`.
- `starField_fixingSubgroup : (starField d).fixingSubgroup = starKernel d`: this is
  Mathlib's infinite Galois correspondence
  `InfiniteGalois.fixingSubgroup_fixedField` for the closed subgroup
  `starKernel d` (the separable closure is Galois over `K`).
- `fixes_starField_iff σ : (∀ x ∈ starField d, σ x = x) ↔ ∀ a, d.star σ a = a`:
  a Galois element fixes the star field pointwise exactly when its star action is
  trivial. This is the previous item read through
  `IntermediateField.mem_fixingSubgroup_iff`.
- `isSeparable_starField : Algebra.IsSeparable K (starField d)`: the star field
  lies in the separable closure. It needs no hypothesis on `d`.
- `finrank_starField : Module.finrank K (starField d) = (starKernel d).index`, by
  `IntermediateField.finrank_eq_fixingSubgroup_index`. Both sides are `0` when
  the index is infinite.
- `mul_inv_mem_starKernel`: for a numbering `e : d.Vertex ≃ Fin n` and a
  permutation `τ` of `Fin n`, if `σ` and `ρ` both satisfy
  `e (d.star _ a) = τ (e a)` for every `a`, then `σ * ρ⁻¹ ∈ starKernel d`.

Results under a star image pair `h : d.StarImagePair e τ`. This hypothesis says
that `τ ≠ 1`, that every `σ` acts through the identity or through `τ` in the
numbering `e`, and that some `σ` acts through `τ`. The outer type A hypothesis
`HasRankOneOuterAIndex` supplies such a pair with `τ = Fin.revPerm`.

- `StarImagePair.not_mem_starKernel_iff`: `σ ∉ starKernel d` exactly when
  `σ` acts through `τ`, that is, `∀ a, e (d.star σ a) = τ (e a)`.
- `StarImagePair.starKernel_index : (starKernel d).index = 2`. Take `σ₀` acting
  through `τ`. Then `σ₀⁻¹` is not in the kernel, and every `b` outside the kernel
  acts through `τ`, so `b * σ₀⁻¹` lies in the kernel by `mul_inv_mem_starKernel`.
  Mathlib's `Subgroup.index_eq_two_iff_exists_notMem_and` concludes. The proof
  does not use that `τ` is an involution.
- `StarImagePair.finrank_starField : Module.finrank K (starField d) = 2`.
- `StarImagePair.isQuadraticExtension :
  Algebra.IsQuadraticExtension K (starField d)`.
- `StarImagePair.isGalois : IsGalois K (starField d)`. A subgroup of index two
  is normal (`Subgroup.normal_of_index_eq_two`), and a normal fixing subgroup
  makes the fixed field Galois (`InfiniteGalois.normal_iff_isGalois`).
- `StarImagePair.restrict_eq_conjugation`: if `σ` acts through `τ`, then for
  every `x` in the star field, `σ x` equals
  `SU3Root.conjugation K (starField d) x`. Here `SU3Root.conjugation` is the
  Library's nonidentity automorphism of a separable quadratic extension, the
  automorphism underlying `SU3Root.fieldInvolution`, which the target Hermitian
  models use. Proof: the restriction `σ.restrictNormal (starField d)` is not the
  identity, since otherwise `σ` would fix the star field and lie in the kernel. So
  it equals the conjugation by `SU3Root.conjugation_unique`, and
  `AlgEquiv.restrictNormal_commutes` transports this to the separable closure.
- `StarImagePair.exists_quadraticField`: packages the previous results. Some
  intermediate field `F` of `SeparableClosure K / K` satisfies
  `Module.finrank K F = 2` and `IsGalois K F`, and for every `σ`,
  `(∀ x ∈ F, σ x = x) ↔ ∀ a, d.star σ a = a`.

## Provenance

Derived (internal) construction, no literature citation. In the theory of
Tits indices, the kernel of the Galois action on the Dynkin diagram is an open
subgroup of the absolute Galois group. Its fixed field is the field over which
the group becomes an inner form. For the indices of outer type `A` (Tits'
`²A`) this field is quadratic, and it is the quadratic extension of the
corresponding unitary groups. The module builds this field from the Library's
own star action `TitsIndexData.star` and from Mathlib's infinite Galois theory.
It is not a transcription of a source definition. Every statement is about the
actual Library objects listed above. The module does not prove that `G`
becomes an inner form over the star field.
