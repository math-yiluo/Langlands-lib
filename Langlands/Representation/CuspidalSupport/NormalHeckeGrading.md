# The grading of End(ind_H^G ρ) by a degree on G

Author: Worker 1826.

This is a supporting module for the proofs of Renard VI.4.4 (the Theorem
`RationalSummandEndCenterStatement`, the Corollary
`RationalSummandEndNoetherianStatement` and the Proposition
`RationalSummandCenterGroupAlgebraStatement`). It extends Worker 1789's generic
module `Langlands.Representation.CuspidalSupport.NormalSubgroupHecke`, in
namespace `Langlands.CuspidalSupport.NormalHecke`. Source: David Renard,
*Représentations des groupes réductifs p-adiques* (registered source
`renard-2026-representations-groupes-reductifs-padiques`), VI.4.3 "Structure de A",
printed pp.154–155 / PDF pp.160–161. The declarations are internal helpers. They
verify, for `End(ind_H^G ρ)`, the hypothesis `IsRankOneGrading` of the published
abstract module `Langlands.Algebra.RankOneGradedAlgebra`.

## Setting

G is a topological group, H a subgroup with `hH : IsOpen H`, and ρ a smooth complex
representation of H. `inducedRep H ρ` is the published compact induction
`ind_H^G ρ`, and `endValue H ρ hH α g` is the endomorphism w ↦ α(f_w)(g) of ρ,
where f_w is the published `unitFunction` (supported on H, f_w(h) = ρ(h) w).
`α * β` in `End (inducedRep H ρ)` is the composite α ∘ β.

## Linear facts (no further hypotheses)

- `endValue_add`, `endValue_smul`, `endValue_zero`, `endValueLinear` (α ↦ φ_α(g)
  as a ℂ-linear map) and `endValue_sum`: the map α ↦ φ_α(g) is linear. All hold by
  `rfl`, since the linear structure on endomorphisms is pointwise.
- `endValue_one_one`: φ_1(1) = id, by the published `eval_unitFunction_one`.
- `endValue_one_of_not_mem`: φ_1(g) = 0 for g ∉ H, since f_w vanishes outside H
  (published `eval_unitFunction`).
- `endValue_conj`: if k = g₀ h g₀⁻¹ with h, k ∈ H, then
  φ_α(g₀) ρ(h) = ρ(k) φ_α(g₀). This is the bi-invariance of the published
  `endValue_mul_right` and `endValue_mul_left`, since g₀ h = k g₀.

## Irreducible ρ and normal H

- `bijective_endValue`: a nonzero value φ_α(g₀) is bijective. Injectivity is the
  published `injective_of_twisted` with the conjugation h ↦ g₀ h g₀⁻¹ of H. The
  range is invariant under ρ: ρ(k) φ_α(g₀)(u) = φ_α(g₀)(ρ(g₀⁻¹ k g₀) u) by
  `endValue_conj`, and it contains a nonzero vector, so it is all of ρ
  (published `mem_of_isIrreducible`).
- `nontrivial_end`: `End (inducedRep H ρ)` is nontrivial, since φ_1(1) = id and
  φ_0(1) = 0 differ on a nonzero vector.

## The grading

Let ι be an additive commutative group.

**Definition (internal).** `IsDegree H p` for p : G → ι says that
p(x y) = p(x) + p(y) for all x, y and that p(g) = 0 if and only if g ∈ H. In the
VI.4.4 application p is the composite of G(F) → G(F) ⧸ ⁰G with an isomorphism
onto a lattice; any such p identifies its image p(G) ⊆ ι with G ⧸ H. Its lemmas
`map_one`, `map_inv`, `map_mem`, `inv_mul_mem` (p g = p g₀ implies
g₀⁻¹ g ∈ H) and `map_bi` (p(h g h') = p(g) for h, h' ∈ H) are immediate.

**Definition (internal).** `component H ρ hH p a` is the subspace of
endomorphisms α with φ_α(g) = 0 whenever p(g) ≠ a; `mem_component_iff` unfolds
it. For H = ⁰G this is Renard's piece of functions supported in ⁰G x with
p(x) = a, transported along the Hecke equivalence of VI.4.2.

Results, for `hp : IsDegree H p`:

- `one_mem_component`: 1 has degree 0, by `endValue_one_of_not_mem`.
- `eq_of_mem_component`: two elements of the piece of degree a that agree at one
  point g₀ of degree a are equal. For p(g) = a write g = g₀ k with k ∈ H and use
  `endValue_mul_right`; elsewhere both vanish. Equality then follows from the
  published `end_ext`.

From here on H is normal and ρ irreducible.

- `mul_mem_component`: the piece of degree a times the piece of degree b lies in
  the piece of degree a + b. By the published `heckeEquiv_mul`, φ_{α β}(x) is the
  finite sum over q ∈ G ⧸ H of φ_α(q.out) φ_β(q.out⁻¹ x). If p(x) ≠ a + b, each
  term has p(q.out) ≠ a or p(q.out⁻¹ x) ≠ b, so it vanishes.
- `projFunction_mem`, `proj`, `endValue_proj`, `proj_mem`: the function equal to
  φ_α on the points of degree a and to zero elsewhere lies in the published
  `heckeSubmodule` (bi-invariance because p is constant on double cosets H g H,
  finiteness because its support is contained in that of φ_α). Its endomorphism
  under the published `endOfHecke` is `proj a α`, of degree a.
- `exists_finset_degrees`: the values of p at the points where φ_α ≠ 0 form a
  finite set, the image of the finite support of φ_α in G ⧸ H (published
  `endValue_finite`). `sum_proj`: α is the sum of its `proj a α` over such a set.
- `iSupIndep_component`, `iSup_component`, `isInternal_component`: the pieces are
  independent (an element of the piece of degree a that vanishes at every point
  of degree a is zero) and span (`sum_proj`), so `End (inducedRep H ρ)` is their
  internal direct sum (Mathlib's `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`).
- `gradedAlgebra` (an `abbrev`, used with `letI`): the resulting Mathlib
  `GradedAlgebra (component H ρ hH p)`, with the decomposition chosen from
  `isInternal_component`. `endValue_decompose`: the homogeneous component of
  degree a of α is `proj a α`, in the form of its values.
- `inverseFunction_mem`, `exists_mul_eq_one`, `isUnit_of_mem_component`: a nonzero
  α of degree a is a unit. Choose g₀ with φ_α(g₀) ≠ 0; then p(g₀) = a, and
  φ_α(g₀) has an inverse T by `bijective_endValue`, with
  ρ(g₀⁻¹ h g₀) T = T ρ(h) for h ∈ H. The function x ↦ ρ(x g₀) T on H g₀⁻¹,
  extended by zero, lies in the Hecke space; its endomorphism β has degree −a.
  Then α β has degree 0, and its value at 1 is a single term of the convolution
  sum, φ_α(g₀) T = id, so α β = 1 by `eq_of_mem_component`. Applying this to β
  gives a right inverse γ of β, and γ = α β γ = α, so α is a unit.
- `rank_component_le_one`: if `Module.rank ℂ ρ ≤ ℵ₀`, every piece has rank at most
  one. Given α₀ ≠ 0 of degree a with φ_{α₀}(g₀) ≠ 0 and β of degree a, the map
  φ_{α₀}(g₀)⁻¹ φ_β(g₀) commutes with ρ (by `endValue_conj` for both), so it is a
  scalar c by the published countable-dimensional Schur lemma
  `countableDimensionalSchur`. Then β and c α₀ agree at g₀, so β = c α₀ by
  `eq_of_mem_component`.
- `isRankOneGrading`: under the same countability hypothesis, the grading
  satisfies the published `RankOneGraded.IsRankOneGrading`.

## Relation to the source

Renard (VI.4.3) grades A = H(G, ρ), restricted to the stabilizer N of ρ, by
⁰G\N, shows that each piece F_x(ρ) ≅ Hom_{⁰G}(ρ^x, ρ) has dimension at most one by
Schur's lemma, and that nonzero homogeneous elements are invertible. Here the
grading is by all of G ⧸ H through p; the pieces of degrees outside the image of
the stabilizer are simply zero, so no stabilizer is introduced. The inverse of a
homogeneous element is written down explicitly, and Schur's lemma is used in its
countable-dimensional form, which is why `rank_component_le_one` assumes
`Module.rank ℂ ρ ≤ ℵ₀`.
