# The Casimir element of a weight-graded Lie algebra of endomorphisms

Module `Langlands.LinearAlgebra.FreudenthalCasimirAlgebra`, namespace
`Langlands.LinearAlgebra.FreudenthalCasimir`.

This module is the first half of the proof of `FreudenthalCasimirCoreStatement`
(the second half is `Langlands.LinearAlgebra.FreudenthalCasimirCore`). Under the
first twelve hypotheses of that statement it shows that the trace form of `U`
is nondegenerate on `g`. It then builds a pair of dual families of `g`: torus
elements and their duals, and root vectors `e_i`, `f_i`. Finally it shows that
the Casimir element they define commutes with `g` and preserves every weight
space. The mathematics is Humphreys, *Introduction to Lie Algebras and
Representation Theory*, GTM 9, §6.2 (Casimir element of a nondegenerate trace
form) and §22.3. The form here is the trace form of the representation `U`
restricted to `g`, not the Killing form. The bracket on `Module.End k U` is the
commutator (`LieRing.ofAssociativeRing`, a local instance). Notation
`WeightGraded.shift W χ` and `WeightGraded.IsScalarOn` is from
`Langlands.LinearAlgebra.WeightGradedEndomorphisms`. `GramDual.gram` and
`GramDual.form` are from `Langlands.LinearAlgebra.GramDualForm`.

## Dual expansions (section `Dual`)

`eq_sum_trace_mul_smul`, `eq_sum_trace_mul_smul'`. Let `g` be a subspace of
`Module.End k U`. Let `b, d : κ → Module.End k U` be finite families with
`trace (b_a d_c) = δ_{ac}`. Assume the trace form is nondegenerate on `g`: if
`x ∈ g` and `trace (x z) = 0` for all `z ∈ g`, then `x = 0`.

- If `g ⊆ span d` and all `b_a ∈ g`, then every `v ∈ g` equals
  `∑_a trace (v d_a) b_a`.
- If `g ⊆ span b` and all `d_a ∈ g`, then every `v ∈ g` equals
  `∑_a trace (b_a v) d_a`.

Proof. The difference `w` lies in `g` and has zero trace against every `d_c`
(respectively `b_c`). So it has zero trace against their span, which contains
`g`. Nondegeneracy then gives `w = 0`.

`mul_mem_shift'`: a version of `WeightGraded.mul_mem_shift` whose degree is
given by an equation `χ + χ' = ψ`.

## Hypotheses

`Hyp P W g root` is a structure (a `Prop`) with fields `indep`, `iSup_eq_top`,
`le_iSup`, `exists_torus`, `zero_le_span`, `eq_bot`, `finrank_root`,
`faithful`, `root_ne_zero`, `root_injective`, `exists_neg`, `nilpotent_ideal`.
They are hypotheses 1–12 of `FreudenthalCasimirCoreStatement`, in the same
order and with the same wording.

Further definitions:

- `mult W ν = dim W ν`;
- `ck k P yb μ j = ⟨μ, y_j⟩ ∈ k`, for the basis `y_j = yb j` of `Y`;
- `Mk` is the image in `k` of the rational Gram matrix
  `GramDual.gram P yb (mult W)`, and `Mik` the image of its inverse;
- `coord_cast`: the image in `k` of the rational coordinates
  `GramDual.coord P yb μ j` is `ck k P yb μ j`.

## Results under `h : Hyp P W g root`

Let `k` have characteristic zero and `U` be finite-dimensional.

### The Gram matrix

- `finite_mult`: the support of `mult W` is finite, because the `W ν` are
  independent in a finite-dimensional space.
- `faithful_mult`: every nonzero `y` pairs nontrivially with some `ν` with
  `mult W ν ≠ 0`.
- `Mk_mul_Mik`, `Mik_mul_Mk`: `Mk · Mik = Mik · Mk = 1`. These are the images
  of `M M⁻¹ = M⁻¹ M = 1` over `ℚ`. That identity holds because the rational
  Gram matrix has unit determinant (`GramDual.isUnit_det_gram`, which uses
  `finite_mult` and `faithful_mult`).
- `Mk_apply`: `Mk j l = ∑_ν mult W ν · ⟨ν, y_j⟩ ⟨ν, y_l⟩`, the sum over the
  support of `mult W`.
- `Mk_symm`, `Mik_symm`: both matrices are symmetric. For `Mik`, this is
  because the inverse of the symmetric matrix `gram` is symmetric.
- `form_cast`: the image of `GramDual.form P yb (mult W) μ ν` in `k` is
  `ck μ ⬝ (Mik · ck ν)`.

### Torus elements

- `tor y` is a chosen element of `g` acting on each `W μ` by `⟨μ, y⟩`
  (hypothesis 4). `tor_mem`, `tor_isScalarOn` record this.
- `eq_of_isScalarOn`: two endomorphisms that act on each `W μ` by the same
  scalar are equal, since the `W μ` span `U`.
- `t j = tor (y_j)`. `τ a = ∑_j a_j t_j`, for `a : ι → k`. The dual torus
  elements are `td l = τ (Mik l ·)`, that is `t^l = ∑_j (M⁻¹)_{lj} t_j`.
- `t_mem`, `τ_mem`, `td_mem`: they lie in `g`.
- `isScalarOn_t`, `isScalarOn_τ`: `τ a` acts on `W μ` by `a ⬝ ck μ`.
- `τ_mem_shift`, `t_mem_shift`, `td_mem_shift`: they have degree `0`.
- `τ_single`: `τ (Pi.single j 1) = t j`.
- `sum_smul_td`: `∑_l c_l t^l = τ (c ᵥ* Mik)`.
- `exists_eq_τ`: every element of `g ⊓ shift W 0` equals `τ a` for some `a`.
  By hypothesis 5 it lies in the span of the elements acting by cocharacters.
  By induction on that span, it acts on each `W μ` by `a ⬝ ck μ` for some `a`.
  For a single cocharacter `y`, `a_j` is the `j`-th coordinate of `y` in the
  basis `yb`. So it equals `τ a` by `eq_of_isScalarOn`.

### Traces of torus elements

- `trace_mul_of_isScalarOn`: if `x` and `z` act on each `W ν` by `φ ν` and
  `ψ ν`, then `trace (x z) = ∑_ν mult W ν · φ ν ψ ν`, summed over the support
  of `mult W`.
- `trace_τ_mul_τ`: `trace (τ a · τ b) = a ⬝ (Mk b)`.
- `trace_t_mul_τ`: `trace (t_j · τ b) = (Mk b)_j`.
- `trace_τ_mul_td`: `trace (τ a · t^l) = a_l`. This uses
  `Mk · (Mik l ·) = e_l`, which follows from `Mk_mul_Mik` and `Mik_symm`.
- `trace_t_mul_td`: `trace (t_j t^l) = δ_{jl}`.
- `τ_eq_of_Mk_mulVec`: if `Mk a = b` then `a = Mik b`.

### Nondegeneracy of the trace form

Assume moreover that `X` is torsion-free.

- `trace_mul_eq_zero_of_mem_shift`: if `a` has degree `χ`, `z` has degree
  `ψ` and `χ + ψ ≠ 0`, then `trace (a z) = 0`. This is
  `WeightGraded.trace_eq_zero_of_mem_shift`.
- `trace_mul_eq_zero_of_homog`: if `a` has degree `χ` and has zero trace
  against `g ⊓ shift W (-χ)`, then it has zero trace against all of `g`. The
  proof decomposes `z ∈ g` by hypothesis 3 and uses the previous item.
- `eq_zero_of_trace_mul_eq_zero`: if `x ∈ g` and `trace (x z) = 0` for all
  `z ∈ g`, then `x = 0`.

  Proof. First, every such `x` is nilpotent. Write `x = ∑_χ x_χ` with
  `x_χ ∈ g ⊓ shift W χ` (hypothesis 3). Each `x_χ` again has zero trace
  against `g`, since only the `-χ` component of `z` contributes. The
  component `x_0` equals `τ a`, and `Mk a = 0` because
  `(Mk a)_l = trace (t_l x_0) = 0`. So `a = 0` and `x_0 = 0`. For `χ ≠ 0`,
  `x_χ` is nilpotent (`WeightGraded.isNilpotent_of_mem_shift`; `X` is
  torsion-free). The `x_χ` lie in the radical of the trace form, so they
  commute pairwise (`TraceFormCasimir.commute_of_trace_mul_eq_zero`, Cartan's
  criterion with hypothesis 12). A sum of pairwise commuting nilpotents is
  nilpotent. Now let `R` be the orthogonal complement of `g` for Mathlib's
  invariant trace form `LieModule.traceForm k g U`
  (`LieAlgebra.InvariantForm.orthogonal`). It is a Lie ideal of `g` whose
  elements are all nilpotent, so `R = 0` by hypothesis 12. Since `x ∈ R`,
  `x = 0`.

### Root vectors

- `exists_root_vectors`: for each `i` there are `e ∈ g ⊓ shift W (root i)` and
  `f ∈ g ⊓ shift W (-root i)` with `trace (e f) = 1`. Every element of the
  first space is a multiple of `e`, and every element of the second is a
  multiple of `f`.

  Proof. Take `e` spanning the line `g ⊓ shift W (root i)` (hypothesis 7). If
  `trace (e f) = 0` for every `f` of degree `-root i`, then
  `trace_mul_eq_zero_of_homog` and nondegeneracy give `e = 0`. So some `f₀`
  has `trace (e f₀) ≠ 0`; rescale it to get `f`. The space of degree
  `-root i` is also a line, because `-root i = root i'` (hypothesis 11). It
  contains the nonzero `f`, so `f` spans it.
- `e i`, `f i` are the chosen vectors. `e_mem`, `f_mem`, `trace_e_mul_f`,
  `eq_smul_e`, `eq_smul_f` record their properties.

### Dual families and the Casimir element

- `bfam = Sum.elim t e` and `dfam = Sum.elim td f`, indexed by `ι ⊕ J`.
  `bfam_mem` and `dfam_mem` say they lie in `g`.
- `trace_bfam_mul_dfam`: `trace (bfam a · dfam c) = δ_{ac}`. The torus–torus
  case is `trace_t_mul_td`. The mixed cases and `e_i f_{i'}` with `i ≠ i'`
  vanish by degree, using `root_ne_zero` and `root_injective`. The case
  `e_i f_i` is `trace_e_mul_f`.
- `le_span_bfam`, `le_span_dfam`: `g` is contained in the span of each
  family. Decompose by hypothesis 3. Degree `0` gives a `τ a`, which is a
  combination of the `t_j`, and also equals `∑_l (Mk a)_l t^l`. A root degree
  gives a multiple of `e_i`, or of `f_{i'}` with `root i' = -root i`. Every
  other degree is zero (hypothesis 6).
- `casimir = ∑_a bfam a · dfam a`. `casimir_eq` rewrites it as
  `∑_j t_j t^j + ∑_i e_i f_i`.
- `commute_casimir`: every `x ∈ g` commutes with the Casimir element. This is
  `TraceFormCasimir.commute_sum_mul` applied to the trace form. Its two
  expansion hypotheses are `eq_sum_trace_mul_smul` and
  `eq_sum_trace_mul_smul'` with the duality, span and nondegeneracy results
  above. The commutators with `x` lie in `g` because `g` is a Lie subalgebra.
- `casimir_mem_shift`: the Casimir element has degree `0`, i.e. it preserves
  every `W μ`.
- `casimir_mem_of_stable`: it preserves every `g`-stable subspace `V`.
