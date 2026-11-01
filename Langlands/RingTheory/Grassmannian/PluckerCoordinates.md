# Chartwise Plucker coordinates for quotient Grassmannians

This module constructs determinants in every algebraic chart of Mathlib's
quotient Grassmannian. Its exported theorem is
`Module.Grassmannian.exists_pluckerCoordinate_eq_det_and_bijective_iff_isUnit`.
The coordinates reconstruct quotient vectors, detect other charts by a unit
condition, commute with arbitrary algebra base change, and satisfy a
multiplicative change-of-chart formula.

All rings, modules and test algebras have universe zero. The base `R` is
any commutative ring, `M` is any `R`-module with an additive commutative
group, and `k : ℕ`. There is no finiteness, freeness, nontriviality or
positivity hypothesis. A family `x : Fin k → M` need not be independent
in `M`.

## Objects and exact conclusions

For a commutative `R`-algebra `A`, a point of
`Module.Grassmannian A (A ⊗[R] M) k` is a submodule whose quotient is
finite projective of constant stalk rank `k`. This is the quotient
Grassmannian convention. Write `q_N` for `N.toSubmodule.mkQ`.

The imported type `Module.Grassmannian.ChartLinear.Chart R x A` consists
of those points for which

\[
 c_{x,N}:A^k\longrightarrow (A\otimes_R M)/N,\qquad
 v\longmapsto\sum_i v_i q_N(1\otimes x_i)
\]

is bijective, where `A^k` is `Fin k → A`. Let `ψ_N(m)` be the unique
coordinate vector of `q_N(1 ⊗ m)` under this map. This is an `R`-linear
map, normalized by `ψ_N(x j) = Pi.single j 1`.

In the namespace `Module.Grassmannian.PluckerCoordinates`, `cmat x N y`
is the `k`-by-`k` matrix with entry `ψ_N(y j) i` in row `i`, column `j`.
The primary definition `plucker x N y` is its determinant. The exported
theorem supplies these scalars simultaneously as `P A x N y` for every
test algebra, chart, chart point and family `y : Fin k → M`. It proves
all six clauses:

1. For every `m : M`,
   \[
   \sum_i P_A(x,N,x[i\leftarrow m])q_N(1\otimes x_i)
     =q_N(1\otimes m).
   \]
   Here `x[i ← m]` is Lean's `Function.update x i m`.
2. The scalar for any family is determined by its single replacements:
   \[
   P_A(x,N,y)=
     \det\big(P_A(x,N,x[i\leftarrow y_j])\big)_{i,j}.
   \]
3. `P A x N x = 1`.
4. For every `φ : A →ₐ[R] B`, the actual Grassmannian base change
   `Module.Grassmannian.map φ N.1` remains in the `x` chart, and
   \[
   P_B(x,\operatorname{map}_{\varphi}N,y)
     =\varphi(P_A(x,N,y)).
   \]
   The conclusion explicitly supplies its chart-membership proof.
5. The family `y` gives a bijective quotient combination map
   `c_{y,N}` if and only if `P A x N y` is a unit of `A`.
6. If `y` gives such a bijective map, then for every family `z`,
   \[
   P_A(x,N,z)=P_A(x,N,y)\,P_A(y,N,z).
   \]
   The second factor uses the same Grassmannian point with the supplied
   `y`-chart proof.

These quantifiers allow `k = 0` and zero test rings; no extra
nontriviality assumption is used. The construction is conditional only
on membership in the displayed chart, which may itself be empty.

## Implemented proof

The module imports the published
`Langlands.RingTheory.Grassmannian.Charts` and Mathlib's matrix inverse
API. The abbreviation `ptx` is the concrete published
`ChartLinear.chartEquiv`, from chart points to the normalized linear
maps `HomX`. Its forward map applies the inverse of
`ChartLinear.coordEquiv x N` to `q_N(1 ⊗ m)`.

`sum_ptx_smul` is the inverse-equivalence identity for that coordinate
map; `ptx_x` is the normalization field of `HomX`. The proof of
`ptx_natural` uses `ChartLinear.map_mem_chart` and
`ChartLinear.chartEquiv_map`, taking the `m,i` coordinate of the latter.
Thus base change in this module is the existing Grassmannian base
change, with coordinates related by the actual algebra homomorphism.

The remaining construction follows the pinned original. The matrix
`cmat x N x` is the identity. Replacing `x i` by `m` replaces column `i`
of that identity matrix by `ψ_N(m)`. The determinant of this matrix is
its `i`th coordinate, proved using `Matrix.cramer_one`. These facts give
`plucker_update`, `plucker_self`, and the reconstruction and determinant
clauses of the exported theorem.

The lemma `family_eq` factors the `y` combination map as the `x`
combination map composed with multiplication by `cmat x N y`.
Bijectivity of the `x` map reduces the chart condition to bijectivity of
this matrix action. The forward implication uses
`Matrix.mulVec_surjective_iff_isUnit` and
`Matrix.isUnit_iff_isUnit_det`. The converse uses a matrix unit's inverse
explicitly to prove both injectivity and surjectivity. This proves
`bijective_iff_isUnit` over the stated arbitrary commutative ring.

For change of chart, expand each `z j` in the `y` quotient basis and
then each `y` vector in the `x` quotient basis. Injectivity of the `x`
combination map (`coeff_unique`) identifies their coordinates, proving
`cmat_mul`. Taking determinants proves `plucker_mul`. Finally,
`plucker_natural` applies coordinate naturality entrywise and
`AlgHom.map_det`; this proves the base-change clause.

## Source and adaptations

The registered original is
`anthropic-flt-complete-lean-source-6e837e75`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`. Its distribution SHA-256 is
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`.
The complete source files read and compared for this adaptation are:

- `P2M/Sol/S_Module_Grassmannian_exists_pluckerCoordinate_eq_det_and_bijective_iff_isUnit.lean`,
  lines 1–251, SHA-256
  `cc724574fb007203d87bcaac325b1e724ac479e82ba5563024a6187bda0cf77a`.
- `Theorems/Thm_Module_Grassmannian_exists_pluckerCoordinate_eq_det_and_bijective_iff_isUnit.lean`,
  lines 1–56, SHA-256
  `67507b9170deafe0be105cb7e0678e7d375a60aca7da2e484a7a9b34f2f9bcb1`.

The exported signature is byte-identical to the original wrapper. It
preserves the universe-zero quantifiers, quotient convention, arbitrary
base ring and module, actual base-change maps, and all six conclusions.

The original `GrassPlucker` namespace becomes the helper namespace above,
and the original `solution` is given its exported theorem name directly.
The aggregate `Mathlib`, generated theorem and `P2M.Util` imports are
replaced by the two focused imports. The generated `P2MW` namespace and
wrapper tactic are removed.

Instead of duplicating the original `Chart` and `HomX` abbreviations
and choosing an equivalence from its existential theorem `exists_pt`,
the port uses the already published types and concrete `chartEquiv`.
The proofs of reconstruction and naturality are the corresponding
published coordinate-equivalence arguments described above. This
changes the route to the coordinates without changing their defining
properties or any exported hypothesis or conclusion. From
`coeff_unique` onward the original proofs are retained, with the single
deprecated lemma `if_neg` replaced by `ite_eq_right` in `cmat_update`.

The Apache 2.0 source notices are retained in
[LICENSE](../../../licenses/Anthropic-FLT/LICENSE),
[NOTICE](../../../licenses/Anthropic-FLT/NOTICE) and
[ATTRIBUTION.md](../../../licenses/Anthropic-FLT/ATTRIBUTION.md).
These are the existing published copies from the pinned distribution;
its attribution table has no separate entry for this source module.

## Scope

These are chartwise scalar coordinates and their identities. The module
does not construct a representing Grassmannian scheme, a morphism to
projective space, or a projective embedding. Those require additional
gluing and geometric arguments. Within the host division-CM task, the
representing CM scheme, its admissibility, smoothness, projectivity and
the natural comparison with the exact normalized CM presheaf remain
separate obligations.
