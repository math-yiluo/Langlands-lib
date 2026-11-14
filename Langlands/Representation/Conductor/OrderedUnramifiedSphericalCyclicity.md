# Spherical cyclicity of norm-ordered unramified principal series: proof

Author: Worker 392.

This pair proves the published proposition
`Langlands.Conductor.OrderedUnramifiedSphericalCyclicityStatement.{uF}` from
[`OrderedUnramifiedWhittakerStatement`](OrderedUnramifiedWhittakerStatement.md),
at the arbitrary field universe `uF`. The closing theorem is

- `Langlands.Conductor.orderedUnramifiedSphericalCyclicity :
  OrderedUnramifiedSphericalCyclicityStatement.{uF}`.

The statement is the cyclicity assertion of Jacquet 2012, Lemma 1. Let `F` be any
nonarchimedean local field, of any characteristic, with uniformizer `ϖ` and residue
cardinality `q`. Let `z : Fin (n + 1) → ℂˣ` have weakly increasing norms; equal
norms, repeated parameters and reducible principal series are allowed. Then every
subrepresentation of the Library's normalized unramified principal series
`principalSeries hϖ n hq z` that contains `sphericalSection hϖ n hq z` is `⊤`. The
proof adds no hypotheses. Its only axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Route

The proof is elementary. It uses no intertwining operators, Jacquet modules,
Langlands quotients or Haar measures, only finite sums of translates, by induction on
the rank. The helper modules are in `Langlands/Representation/Conductor/SphericalCyclicity/`:

| Module | Content |
| --- | --- |
| [`LinearAlgebra`](SphericalCyclicity/LinearAlgebra.md) | A subspace of `ℂ^r` containing `(1, …, 1)` and stable under the upper-triangular `cellMatrix` is everything, for weakly increasing `‖z_i‖` and `q ≥ 2`. |
| [`Blocks`](SphericalCyclicity/Blocks.md) | `(1, m)` block matrices, `diag(α, h)` and lower unipotents `L(y)`. |
| [`Cells`](SphericalCyclicity/Cells.md) | The big cell: `D = low x` is invertible and `D⁻¹ colT x` is small. |
| [`Parahoric`](SphericalCyclicity/Parahoric.md) | The parahoric `J = K ∩ t' K t'⁻¹` and its right action on the cell. |
| [`Extension`](SphericalCyclicity/Extension.md) | The extension-by-zero map `extend` from rank `n + 1` with parameters `z ∘ succ` to rank `n + 2`. |
| [`Lattice`](SphericalCyclicity/Lattice.md) | `extend (ρ'(h) ψ)` is a finite combination of translates of `extend ψ`, so `pullback S = extend⁻¹(S)` is a subrepresentation. |
| [`Cellular`](SphericalCyclicity/Cellular.md) | **Step C**: a subrepresentation containing every `extend ψ` is everything. |
| [`Counting`](SphericalCyclicity/Counting.md) | Counting residue tuples by their last nonzero entry. |
| [`Weyl`](SphericalCyclicity/Weyl.md) | Parahoric-invariant vectors are determined by their values at the permutation matrices `w_j`. |
| [`Hecke`](SphericalCyclicity/Hecke.md) | **Step A**: a subrepresentation containing the spherical section contains `extend` of the smaller spherical section. |

## This module

Namespace `Langlands.Conductor.SphericalCyclicity`:

- `mem_borel_zero`: every `x ∈ GL_1(F)` lies in `Borel 0`. The upper-triangularity
  condition `j < i` is vacuous on `Fin 1`.
- `eq_smul_sphericalSection_rank_one`: in rank one, every `f` equals
  `f(1) • sphericalSection`. For each `x`, covariance (`value_borel_mul` with `b = x`
  and `g = 1`) gives `f(x) = χ(x) f(1)` and `f₀(x) = χ(x) f₀(1) = χ(x)`
  (`sphericalSection_one`). Then `ext_value` applies.
- `eq_top_rank_one`: in rank one, a subrepresentation containing the spherical
  section contains every `f = f(1) • f₀`, so it is `⊤`
  (`Subrepresentation.toSubmodule_injective` and `Submodule.eq_top_iff'`).

Namespace `Langlands.Conductor`:

- `orderedUnramifiedSphericalCyclicity`. After introducing `F`, its instances, `ϖ`,
  `hϖ` and `n`, the proof is by induction on `n`, with `q`, `hq`, `z` and `S` still
  universally quantified.
  - `n = 0`: `eq_top_rank_one`.
  - `n + 1`: let `hmono` be the monotonicity of `‖z_i‖` and `S ∋ f₀`.
    1. `extend_sphericalSection_mem hϖ hmono S hS` (Step A) gives
       `extend (sphericalSection hϖ n hq (tailParam z)) ∈ S`, that is, the smaller
       spherical section lies in `pullback hϖ hq z S` (`mem_pullback`).
    2. `tailParam z = z ∘ Fin.succ` again has monotone norms, by
       `Fin.succ_le_succ_iff`. The induction hypothesis therefore gives
       `pullback hϖ hq z S = ⊤`.
    3. Every `extend ψ` therefore lies in `S`, and `eq_top_of_extend_mem` (Step C)
       gives `S = ⊤`.

The monotonicity hypothesis is used only in Step A, through
`eq_top_of_cellMatrix_stable`. There the extreme indices `i0 ≤ k1` of the support of
an eigenfunctional would force `‖z_(i0)‖ = q ‖z_(k1)‖`, which contradicts
`‖z_(i0)‖ ≤ ‖z_(k1)‖` and `q ≥ 2`.
