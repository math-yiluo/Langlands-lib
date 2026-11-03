# Graded bialgebras

Author: Worker 1389 designed and implemented this module and wrote this note, as
part of task `90ffbd89-a3dd-4baa-84ba-332896bbbd17` (split unipotence from the
absence of zero Lie weights). No other worker's draft was reused. The module builds on
`Langlands.Algebra.GradedHopf.TensorGrading` (same author), whose degree projections
`gradeProj` and `tensorProj` and total-degree submodules `tensorGrade` it uses.

The module `Langlands/Algebra/GradedHopf/Basic.lean` sets up a grading of a commutative
bialgebra by an additive commutative group `ι` (for the intended application `ι = ℤ`,
coming from a cocharacter of a split torus acting on a group). Throughout, `k` is a
commutative ring, `A` a commutative `k`-algebra and `𝒜 : ι → Submodule k A` a grading in
the sense of Mathlib's `GradedAlgebra 𝒜`.

## Graded algebra facts

- `one_mem_zero`, `algebraMap_mem_zero`: `1` and the scalars lie in degree `0`.
- `gradeProj_mul_of_left_mem` / `gradeProj_mul_of_right_mem`: if `a ∈ 𝒜 i` then
  `gradeProj 𝒜 n (a * b) = a * gradeProj 𝒜 (n - i) b`, and symmetrically
  (from Mathlib's `coe_decompose_mul_add_of_left_mem`).
- `gradeProj_algebraMap`: the components of a scalar.
- `gradeProj_mem_of_isHomogeneous`: a homogeneous ideal (Mathlib's
  `Ideal.IsHomogeneous`) contains the components of its elements.

## The definition

For a `Bialgebra k A` structure (whose underlying algebra structure is the one used by
`𝒜`), `IsGradedBialgebra 𝒜` is the proposition with two fields:

- `comul_mem`: for every `n` and `a ∈ 𝒜 n`, `comul a ∈ tensorGrade 𝒜 𝒜 n`, i.e. the
  comultiplication carries degree `n` into the part of total degree `n` of `A ⊗ A`;
- `counit_eq_zero`: for every `n ≠ 0` and `a ∈ 𝒜 n`, `counit a = 0`.

This is the usual notion of a graded bialgebra in which comultiplication and counit are
graded maps (`k` sitting in degree `0`); provenance: internal. It is the structure a
split torus with character group `ι` acting by bialgebra (group) automorphisms
produces on its weight grading: comultiplication is equivariant for the diagonal
action on `A ⊗ A` and the counit is equivariant for the trivial action on `k`, i.e.
`A` is a bialgebra object in the category of torus representations. (The coaction map
`A → A ⊗ k[ι]` itself is in general *not* a map of ordinary `k`-bialgebras; for
example the scaling coaction `x ↦ x ⊗ t` on `k[x]` with `x` primitive is not.) The
module does not formalize this connection; it only states the grading conditions.

## Consequences

For `h𝒜 : IsGradedBialgebra 𝒜`:

- `comul_comp_gradeProj` / `comul_gradeProj`:
  `comul (gradeProj 𝒜 n a) = tensorProj 𝒜 𝒜 n (comul a)`;
- `counit_gradeProj`: `counit (gradeProj 𝒜 n a)` is `counit a` if `n = 0` and `0`
  otherwise, with the specialisations `counit_gradeProj_zero` and `counit_gradeProj_ne`;
- `gradeProj_mem_ker_counit`: the augmentation ideal contains the components of its
  elements;
- `isPrimitiveElem_gradeProj`: every homogeneous component of a primitive element
  (Mathlib's `Bialgebra.IsPrimitiveElem k f`: `counit f = 0` and
  `comul f = 1 ⊗ₜ f + f ⊗ₜ 1`) is primitive. The proof applies `comul_gradeProj` and
  `tensorProj_tmul_of_mem_left/right` with `1 ∈ 𝒜 0`.

The proofs reduce to homogeneous elements by `decompose_lhom_ext` or
`Decomposition.inductionOn`.
