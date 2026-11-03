# Graded matrix coefficients of a graded bialgebra over a field

Author: Worker 1419 designed and implemented this module and wrote this note, as part of
task `90ffbd89-a3dd-4baa-84ba-332896bbbd17` (split unipotence from the absence of zero Lie
weights). Let `k` be a field, `A` a commutative `k`-bialgebra and `𝒜 : ℤ → Submodule k A` a
grading (`[GradedAlgebra 𝒜]`) with `h𝒜 : IsGradedBialgebra 𝒜` (Library,
`Langlands.Algebra.GradedHopf.Basic`). The module produces square matrices `a` of
homogeneous elements of `A` such that

- `IsCorep k a`: `Δ(aᵢⱼ) = ∑ₗ aᵢₗ ⊗ aₗⱼ` and `ε(aᵢⱼ) = δᵢⱼ`;
- `IsGraded 𝒜 w a`: `aᵢⱼ ∈ 𝒜 (w j - w i)` for some weights `w`;

and whose entries span a given finite set of homogeneous elements
(`exists_corep`) or generate `A` when `A` is of finite type (`exists_corep_adjoin_eq_top`).
The predicates `IsCorep` and `IsGraded` come from the companion module
`Langlands.Algebra.GradedHopf.Triangular` (same author). Everything here is in namespace
`Langlands.Algebra.GradedHopf.GradedComodule`.

## Provenance

This is internal infrastructure for the proof of
`RelativeRoot.TorusActionSplitUnipotenceStatement`. It is a graded version of the Library's
`Langlands.GroupScheme.Comodule.exists_matrix` (module
`Langlands.GroupScheme.ComoduleMatrixCoefficients`, which follows J. S. Milne, *Algebraic
Groups* (2017), Proposition 4.7, Corollary 4.8 and Theorem 4.9). That module puts every
finite set inside a finite-dimensional subcomodule and reads off matrix coefficients from a
basis. Here the subcomodule is also closed under the degree projections, and the basis
consists of homogeneous elements. No source states the graded version, so no source is cited
for it. The proof reuses the Library's comodule operators `Comodule.rightOp`,
`Comodule.leftOp`, `Comodule.orbit` and `Comodule.IsStable`.

## Coalgebra axioms

`coassoc k A`, `rightCounit k A` and `leftCounit k A` restate coassociativity and the two
counit laws of the coalgebra `A` in the Library's forms `Comodule.Coassoc`,
`Comodule.RightCounit` and `Comodule.LeftCounit` (from Mathlib's `Coalgebra.coassoc`,
`Coalgebra.lTensor_counit_comul` and `Coalgebra.rTensor_counit_comul`).

## Degrees and contractions

`tensorGrade 𝒜 𝒜 d` is the Library submodule of `A ⊗ A` of total degree `d` and
`gradeProj 𝒜 e` the projection of `A` to degree `e`.

- `gradeProj_rid_lTensor`: for `x ∈ tensorGrade 𝒜 𝒜 d`, a functional `m : A →ₗ[k] k` and
  `e : ℤ`, projecting the right contraction `rid ((id ⊗ m) x)` to degree `e` gives the right
  contraction by `m ∘ gradeProj 𝒜 (d - e)`. On a pure tensor `a ⊗ b` with `a ∈ 𝒜 i`,
  `b ∈ 𝒜 j`, `i + j = d`, both sides are `m(b) a` if `i = e` and `0` otherwise. The general
  case is span induction.
- `lid_rTensor_mem`: for `x ∈ tensorGrade 𝒜 𝒜 d`, a functional `l` and `e : ℤ`, the left
  contraction `lid ((l ∘ gradeProj 𝒜 e ⊗ id) x)` lies in `𝒜 (d - e)`.

## Graded subcomodules

- `IsGradedSubspace 𝒜 V` for `V : Submodule k A`: `gradeProj 𝒜 e v ∈ V` for every `e` and
  `v ∈ V`.
- `IsGradedSubspace.sup`: the sum of two such subspaces is one.
- `orbit_isGradedSubspace h𝒜 hx`: for `x ∈ 𝒜 d`, the span `Comodule.orbit Δ x` of all right
  contractions of `Δ x` is closed under the degree projections. Since `Δ x` has total
  degree `d` (`h𝒜.comul_mem`), `gradeProj_rid_lTensor` shows that the projection of a
  right contraction of `Δ x` is again one.
- `exists_stable h𝒜 s hs`: every finite set `s` of homogeneous elements lies in a
  finite-dimensional subspace `V` that is `Comodule.IsStable` (a subcomodule) and
  `IsGradedSubspace 𝒜`. Induction on `s`. The orbit of a new element `x` is finite-dimensional
  (`Comodule.orbit_finiteDimensional`), stable (`Comodule.orbit_isStable`), closed under the
  projections, and contains `x` (`Comodule.mem_orbit`).
- `exists_homogeneous_basis V hV`: a finite-dimensional `V` closed under the projections has a
  basis `e : Module.Basis (Fin n) k V` with `(e i : A) ∈ 𝒜 (w i)` for weights
  `w : Fin n → ℤ`. The homogeneous elements of `V` span `V`, since each `v ∈ V` is the sum of
  its components (`sum_gradeProj`), which lie in `V`. Mathlib's `exists_linearIndependent`
  extracts a basis from this spanning set.
- `coord_gradeProj hV e he i v hv`: the `i`-th coordinate of `gradeProj 𝒜 (w i) v` in the
  homogeneous basis `e` equals the `i`-th coordinate of `v`. Both functionals agree on the
  basis vectors, which `gradeProj 𝒜 (w i)` keeps or kills according to their weight.

## Matrix coefficients

`exists_corep h𝒜 s hs`: for a finite set `s` of homogeneous elements there are `n`,
`w : Fin n → ℤ` and `a : Matrix (Fin n) (Fin n) A` with `Triangular.IsCorep k a`,
`Triangular.IsGraded 𝒜 w a`, and every `x ∈ s` in the `k`-span of the entries of `a`.

Proof. Take `V` from `exists_stable` and a homogeneous basis `e` with weights `w` from
`exists_homogeneous_basis`. Extend each coordinate functional `e.coord i` to a functional
`μᵢ` on `A` (`LinearMap.exists_extend`) and set `λᵢ = μᵢ ∘ gradeProj 𝒜 (w i)`. On `V`,
`λᵢ` is still the `i`-th coordinate (`coord_gradeProj`), so `λᵢ (e j) = δᵢⱼ`. Stability of
`V` and `Comodule.tensor_ext_of_rid` give the coaction formula
`Δ v = ∑ᵢ eᵢ ⊗ leftOp Δ λᵢ v` for `v ∈ V`. Set `aᵢⱼ = leftOp Δ λᵢ (eⱼ)`.

- `IsCorep`: the formula `Δ(aᵢⱼ) = ∑ₗ aᵢₗ ⊗ aₗⱼ` follows from `Comodule.comul_leftOp` and
  the coaction formula for `eⱼ`. Also `ε(aᵢⱼ) = λᵢ(eⱼ) = δᵢⱼ` by the right counit law.
- `IsGraded`: `aᵢⱼ ∈ 𝒜 (w j - w i)` by `lid_rTensor_mem`, since `Δ eⱼ` has total degree
  `w j`.
- Span: by the left counit law and the coaction formula, `eⱼ = ∑ᵢ ε(eᵢ) aᵢⱼ`, and every
  `x ∈ s ⊆ V` is a combination of the `eⱼ`.

`exists_corep_adjoin_eq_top h𝒜` (with `[Algebra.FiniteType k A]`): the same conclusion,
except that the entries of `a` generate `A` as a `k`-algebra
(`Algebra.adjoin k (Set.range fun p => a p.1 p.2) = ⊤`). Apply `exists_corep` to the
homogeneous components of a finite generating set. Each generator is the sum of its
components, which lie in the span of the entries.
