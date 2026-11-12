# The face height of a based root datum

Authors: Worker 187.

The module `Langlands.LinearAlgebra.RootDatumFaceHeight` (namespace
`Langlands.LinearAlgebra.RootDatumFaceHeight`) proves combinatorial facts about a root
datum `P : RootDatum J M N`, a base `B` and a coweight `ν : N`. They are used to show
that the simple roots of a face base restrict to simple relative roots (module
`Langlands.GroupScheme.Rational.FaceSimpleRootRestriction`) and to compute the
characters of cocenters (module
`Langlands.GroupScheme.SimplyConnected.LeviCocenterKernelGenerationProof`).

Throughout, "`ν` is dominant for `B`" is the hypothesis
`hdom : ∀ i ∈ B.support, 0 ≤ P.root' i ν`.

## Provenance

This is an internal helper with no direct literature counterpart. The face height
counts, with multiplicity, the simple roots not vanishing on `ν`. It is the tool of
the formal argument, in `FaceSimpleRootRestriction`, for the part of Borel–Tits,
*Groupes réductifs* (1965), Proposition 6.8 (registered as
`borel-tits-1965-groupes-reductifs`) that the kernel generation proof needs. The
statements here are standard root-system facts; the proofs were written for this
formalization.

## Root span action

- `smul_mem_rootSpan`, `rootSpanMap g`: a root-datum automorphism `g : P.Aut` maps
  the integral root span `P.rootSpan ℤ` into itself; `rootSpanMap g` is the
  restricted `ℤ`-linear map. `coe_rootSpanMap`, `rootSpanMap_one`, `rootSpanMap_mul`
  and `rootSpanMap_rootSpanMem` record that this is an action that permutes the roots
  by `g.indexEquiv`.

## Face height

- `faceHeight B ν : P.rootSpan ℤ →ₗ[ℤ] ℤ` is the linear form, defined on the basis
  `B.toWeightBasisInt` of simple roots, sending a simple root `i` to `0` if
  `P.root' i ν = 0` and to `1` otherwise.
- `faceHeight_simple`: this value on a simple root.
- `faceHeight_eq_sum`, `root'_eq_sum`: if a root-span element (resp. a root) is
  `∑ f j • root j` over the simple roots, then its face height is
  `∑ f j * [root' j ν ≠ 0]` (resp. its value on `ν` is `∑ f j * root' j ν`).
- `faceHeight_root_of_eq_zero`: if `ν` is dominant for `B` and the root `j` vanishes
  on `ν`, then `faceHeight B ν (root j) = 0`. Proof: by
  `Base.exists_root_eq_sum_nat_or_neg`, `root j` is `± ∑ f i • root i` with all
  `f i ≥ 0`. All terms `f i * root' i ν` are nonnegative and sum to `0`, so each
  vanishes. Hence `f i = 0` whenever `root' i ν ≠ 0`, and the face height is `0`.
- `one_le_faceHeight_root_of_pos`: if `ν` is dominant for `B` and `0 < root' j ν`,
  then `1 ≤ faceHeight B ν (root j)`. Proof: the negative case contradicts
  dominance. In the positive case some term `f i * root' i ν` is positive, so
  `root' i ν ≠ 0` and `f i ≥ 1`, and that term contributes at least `1` to the sum of
  nonnegative terms.
- `faceHeight_comp_rootSpanMap_of_mem`: if `ν` is dominant for `B`, every `w` in
  `reflectionSubgroup P {i | P.root' i ν = 0}` preserves the face height. Proof:
  induction on the subgroup closure. A generating reflection `s_j` changes `x` by a
  multiple of `root j`, whose face height is `0` by `faceHeight_root_of_eq_zero`.
- `faceHeight_comp_rootSpanMap`: if `ν` is dominant for `B`, every automorphism `δ`
  with a based correction `C : Correction P ν B δ` (module
  `LinearAlgebra.RootDatumBasedCorrection`) preserves the face height. Proof:
  `C.weyl.val * δ` permutes the simple roots by `C.perm` and preserves vanishing on
  `ν` (`C.index_eq`, `C.zero_iff`), so it preserves the face height on the basis.
  `C.weyl.val⁻¹` preserves it by the previous item, and `δ` is the product.

## Coroot spans and annihilators

- `coroot_span_zero_eq_of_dominant`: if `ν` is dominant for `B`, the coroots of the
  roots vanishing on `ν` span the same `ℤ`-module as the simple coroots among them.
  Proof: transport `ν` to a functional on coweights through `P.CoPolarization`
  (`dual_copolarization_coroot_eq_zero_iff`,
  `SplitExistence.dual_polarization_root_pos_iff`). Then apply
  `coroot_span_zero_eq_span_simple` (module `LinearAlgebra.LeviCorootSpan`).
- `annihilator_iff_of_dominant`: hence a weight annihilates all coroots of roots
  vanishing on `ν` iff it annihilates the simple ones.
- `mem_range_iff_of_dominant` (range transfer): let `g : V →ₗ[ℤ] M` be injective
  with range the annihilator of the coroots of roots vanishing on a coweight `μ`.
  Let `π : W →ₗ[ℤ] V` be such that the range of `g ∘ π` is the annihilator of the
  coroots of roots vanishing on `ν`, with `ν` dominant for `B`. Then `x ∈ range π`
  iff `g x` annihilates the coroots of the simple roots `i` with `root' i μ ≠ 0` and
  `root' i ν = 0`. Proof: one direction is immediate. For the other, use
  `annihilator_iff_of_dominant`: at a simple root vanishing on `μ`, `g x` already
  annihilates its coroot because `g x ∈ range g`. So `g x ∈ range (g ∘ π)`, and
  injectivity of `g` gives `x ∈ range π`.
- `face_dominant`: for a reduced finite root datum, the coweight `ν` is dominant for
  the base of every coweight face `C : RootDatumCoweightFace.Face P ν`. Proof: a
  simple root `i` of `C.base` lies in the indecomposable base of the regular
  refinement, so `0 < root' i C.regular`. If `root' i ν ≠ 0`, `C.signs` gives
  `0 < root' i ν`.
