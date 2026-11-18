# The scalar step for minor vectors of real standard modules without discrete series

Lean module: `Langlands.Representation.Archimedean.RealTiedMinorScalar`, namespace
`Langlands.Archimedean.RealTiedMinorScalar`. Author: Worker 379, for Task 7626
(`4fda7898-2fbf-4ad2-a6b5-48fb114ca3e0`), whose target is
`Langlands.Archimedean.RealTemperedScalarCommutantStatement`.

## Purpose and provenance

Let `ds` be a list of real blocks with no discrete-series block: each induction block has weight
`0`. Then the real standard module is a principal series. This module shows two things for an
endomorphism `E` of its `O(n)`-finite functions:

1. If `E` commutes with `O(n)`, it multiplies every minor vector `φ_{A,B}` by one common scalar.
   Here `A` is the set of odd positions.
2. Suppose every subspace that is stable under `O(n)` and the Lie algebra and contains all
   `φ_{A,B}` is the whole space. Then every simultaneous endomorphism is a scalar
   (`HasScalarCommutant`).

Step 1 is the lowest-`K`-type multiplicity-one computation for the `O(n)`-type
`Λ^{|A|} ℂ^n` spanned by the `φ_{A,B}`. The proof is elementary (Cauchy–Binet and sign
matrices) and uses no representation theory of `O(n)`. Step 2 is the usual argument: the
kernel of `E - c` is a submodule containing the `φ_{A,B}`. The module is internal
infrastructure for Task 7626 and makes no literature claim. The minor vectors and their
Cauchy–Binet law come from the Library module `JacquetMinorNonvanishing`
(`minorVector`, `minorVector_mem`, `minorVector_mul`, `minorVector_of_mem`).

## Notation

* `KF n ds` (Library, `RealTemperedCommutantReduction`): the `O(n)`-finite functions of
  `realStandardModule n ds`. `realStandardRep n ds k` is right translation by
  `k ∈ O(n) = Matrix.unitaryGroup (Fin n) ℝ`, and `realStandardLie n ds Z` is the right
  derivative along `Z ∈ ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`.
* `realPositionCharacter ds l` and `realPositionExponent ds l` (Library) are the character and
  exponent at position `l`. `minor M A B = det M_{A,B}` (Library `MatrixMinor`).
* `HasScalarCommutant n ds` (Library): every complex linear endomorphism of `KF n ds` that
  commutes with all `realStandardRep n ds k` and all `realStandardLie n ds Z` is `c • id` for
  some `c : ℂ`.

## Definitions

* `IsPrincipal ds`: for every position `p` and every `d` with `realInducedBlockAt ds p = some d`,
  `d.weight = 0`. So `ds` has no discrete-series block.
* `signSet n ds : Finset (Fin n)`: the positions `l` with `realPositionCharacter ds l (-1) = -1`.
* `vec hds B : KF n ds`: if `|B| = |signSet n ds|`, the minor vector
  `minorVector n (realPositionExponent ds) (signSet n ds) B`. This is the function of the
  principal series whose restriction to `O(n)` is `κ ↦ det κ_{A,B}`, with `A = signSet n ds`.
  Otherwise it is `0`.
* `minorElem hds = vec hds (signSet n ds)`, the vector `φ_{A,A}`.
* `flip j ∈ O(n)`: the diagonal matrix with `-1` at `j` and `1` elsewhere. `flipUnits j` is the
  same diagonal as units.

## Results

* `realStandardModule_eq`: if `IsPrincipal ds`, then `realStandardModule n ds` equals
  `principalSeries ℝ n (realPositionCharacter ds)`. The Fourier conditions concern only modes
  `|k| < |weight| = 0`, so they are vacuous.
* `sign_eq`: `realPositionCharacter ds l (-1)` is `-1` for `l ∈ signSet n ds` and `1` otherwise.
* `vec_coe`: the underlying function of `vec hds B` is the minor vector when `|B| = |A|`.
* `rep_vec` (Cauchy–Binet): `R(k) φ_{A,B} = Σ_{|C| = |A|} det k_{C,B} · φ_{A,C}`. This is
  `minorVector_mul` evaluated pointwise.
* `toUnits_flip`, `principalSeriesCharacter_flip`, `eval_rep_flip`: evaluation at `1` satisfies
  `ev₁(R(flip j) v) = ±ev₁(v)`. The sign is `-1` exactly when `j ∈ A`. The proof writes
  `flip j` as a diagonal element of the Borel subgroup and uses the principal-series law.
* `rep_flip_vec`: `R(flip j) φ_{A,C} = -φ_{A,C}` if `j ∈ C` and `φ_{A,C}` otherwise (diagonal
  minors in Cauchy–Binet).
* `functional_rep_vec` (multiplicity one): let `ψ` be a linear functional on `KF n ds` with
  `ψ(R(flip j) v) = ±ψ(v)`, using the same signs as `ev₁`. Then
  `ψ(R(k) φ_{A,B}) = det k_{A,B} · ψ(φ_{A,A})`. Proof: expand `R(k) φ_{A,B}` by `rep_vec`.
  For `C ≠ A` with `|C| = |A|` choose `j ∈ C \ A`. Then `rep_flip_vec` and the hypothesis on
  `ψ` give `ψ(φ_{A,C}) = -ψ(φ_{A,C})`, so `ψ(φ_{A,C}) = 0`.
* `exists_forall_vec_eq_smul` (scalar step): let `E` commute with every `R(k)`, `k ∈ O(n)`.
  Then there is `c` with `E φ_{A,B} = c φ_{A,B}` for all `B` with `|B| = |A|`. Proof: take
  `c = ev₁(E φ_{A,A})`. Both `ev₁ ∘ E` and `ev₁` satisfy the sign law. Applying
  `functional_rep_vec` to both, and using `ev₁(φ_{A,A}) = det 1 = 1`, gives
  `ev₁(R(k)(E φ_{A,B} - c φ_{A,B})) = 0` for every `k ∈ O(n)`. A function of the principal
  series that vanishes on `O(n)` is zero (Library `eq_zero_of_compact_eval`).
* `hasScalarCommutant_of_cyclic` (reduction): assume `IsPrincipal ds` and suppose every
  subspace `W` of `KF n ds` that is stable under all `R(k)` and all `realStandardLie n ds Z`
  and contains every `φ_{A,B}` (`|B| = |A|`) is `⊤`. Then `HasScalarCommutant n ds`. Proof:
  for `E` in the commutant, take `c` from the scalar step and apply the hypothesis to
  `W = ker(E - c • id)`.
