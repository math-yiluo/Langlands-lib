# Splitting the twisted matrix algebra of a unitary projective cocycle

Module `Langlands.LinearAlgebra.UnitaryTwistedDescent`, namespace
`Langlands.LinearAlgebra.UnitaryTwistedDescent`.

## Setting

`M/K` is a field extension, `m` a finite index type, and `x : Gal(M/K) → GL m M` a family of
invertible matrices. `H` is a subgroup of `Gal(M/K)`. Its elements are called inner and the
other automorphisms outer. Write `N^σ` for the entrywise image `N.map σ` and `Nᵀ` for the
transpose. The **twisted projective cocycle law** has two parts, used as hypotheses `hin` and
`hout`:

* `hin`: for `σ ∈ H` and every `τ` there is a unit `c ∈ Mˣ` with `x(στ) = c · x(σ) x(τ)^σ`;
* `hout`: for `σ ∉ H` and every `τ` there is a unit `c ∈ Mˣ` with
  `x(στ) = c · x(σ) ((x(τ)⁻¹)^σ)ᵀ`.

These are the relations satisfied by the matrix representatives of a Galois cocycle of an outer
form of `SL_m`. Inner automorphisms act by conjugation and outer ones by conjugation composed with
the inverse transpose, all up to scalars.

## Declarations

* `twistedAct H x σ N` (def). It is `x(σ) N^σ x(σ)⁻¹` for `σ ∈ H` and
  `x(σ) (N^σ)ᵀ x(σ)⁻¹` otherwise.
* Matrix identities: `map_map_mul`, `map_one_alg`, `map_one_aut`, `conj_eq_of_eq_smul`
  (conjugation by `c • A`, where `A A' = 1`, is `N ↦ A N A'`), `inner_mul_inv`, `outer_mul_inv`,
  `algebraMap_map`, `conj_algebraMap`, `conj_cancel`.
* `twistedAct_mul` (needs `H.index = 2`, `hin` and `hout`):
  `twistedAct (στ) N = twistedAct σ (twistedAct τ N)`. This uses `twistedAct_of_mem` and
  `twistedAct_of_not_mem`. `twistedAct_one`: the identity acts trivially.
* `twistedAct_algebraMap`: the action is `σ`-semilinear on the scalar matrices
  `algebraMap M _ l`. `twistedAct_add` gives additivity. `twistedAct_mul_of_not_mem`: an outer
  `σ` reverses products.
* `innerRingHom X σ` (def): the ring endomorphism `N ↦ X N^σ X⁻¹`, with `innerRingHom_apply`.
* `restrictScalars_mem`: an `F`-automorphism, viewed over `K`, lies in `F.fixingSubgroup`.
* `galoisAction F hH hin hout` (def). For an intermediate field `F` with
  `F.fixingSubgroup.index = 2` and `H = F.fixingSubgroup`, this is the
  `Langlands.CentralSimple.SemilinearGaloisAction F M (Matrix m m M)` in which `σ ∈ Gal(M/F)`
  acts by `innerRingHom (x σ) σ`. That is the restriction of `twistedAct` to `Gal(M/F)`.
* `twistedAct_of_mem_fixed`: elements of the fixed algebra `(galoisAction F hH hin hout).fixed`
  are fixed by `twistedAct σ` for every `σ ∈ F.fixingSubgroup`.
* `twistedAct_mem_fixed`: for every `r ∈ Gal(M/K)`, `twistedAct r` maps the fixed algebra into
  itself. The proof uses that `F.fixingSubgroup` is normal (index two).
* `outerInvolution F hH hin hout r` (def): the restriction of `twistedAct r` to the fixed algebra,
  with `coe_outerInvolution`.
* `isUnitaryInvolution_outerInvolution`. Assume `F/K` is normal and `r ∉ F.fixingSubgroup`.
  Then `outerInvolution F hH hin hout r` is a unitary involution
  (`Langlands.IsUnitaryInvolution`) relative to `r.restrictNormal F`. It is additive, reverses
  products, squares to the identity because `r² ∈ F.fixingSubgroup`, and acts on `F` through `r`.
* **`exists_conj_eq_scalar`** (main theorem). Assume:
  * `UnitaryInvolutionSplitting K`;
  * `M/K` is finite Galois;
  * `m` is nonempty;
  * `F` is an intermediate field with `Algebra.IsQuadraticExtension K F`;
  * `x` satisfies `hin` and `hout` for `H = F.fixingSubgroup`.

  Then there is `P : GL m M` such that for every `σ ∈ F.fixingSubgroup` there is `c : Mˣ` with
  `P⁻¹ * x σ * GeneralLinearGroup.map σ.toRingHom P = GeneralLinearGroup.scalar m c`.

## Proof of the main theorem

1. `F.fixingSubgroup.index = [F : K] = 2` (`IntermediateField.finrank_eq_fixingSubgroup_index`).
   Hence some `r` lies outside `F.fixingSubgroup`, and `r.restrictNormal F ≠ 1`.
2. Let `ρ = galoisAction F …` and `B = ρ.fixed`, an `F`-subalgebra of `Matrix m m M`. By the
   Library's Galois descent (`SemilinearGaloisAction.descentEquiv`), `M ⊗_F B ≅ Matrix m m M`.
   Also `B` is finite-dimensional, simple and central over `F`
   (`finiteDimensional_fixed`, `isSimpleRing_fixed`, `isCentral_fixed`). `F/K` is separable
   because `M/K` is.
3. `outerInvolution … r` is a unitary involution of `B` relative to the nontrivial automorphism
   `r|_F` (step 1). `UnitaryInvolutionSplitting K` gives `B ≅ Matrix (Fin k) (Fin k) F` over `F`.
   Comparing dimensions over `M` gives `k = card m`, so `B ≅ Matrix m m F` after reindexing.
4. The images `E i j ∈ B ⊆ Matrix m m M` of the standard matrix units satisfy the matrix-unit
   relations, and `E p p ≠ 0`. `MatrixUnitConjugation.exists_mul_single_eq` gives `P : GL m M`
   with `P * single i j 1 = E i j * P`.
5. Let `σ ∈ F.fixingSubgroup`. Each `E i j` is fixed by `twistedAct σ`, so
   `x(σ) (E i j)^σ = E i j x(σ)`. Applying `σ` to step 4 gives
   `P^σ * single i j 1 = (E i j)^σ * P^σ`, because `single i j 1` has entries in `K`. Then
   `A = P⁻¹ x(σ) P^σ` commutes with every `single i j 1`. By
   `Matrix.mem_range_scalar_iff_commute_single'`, `A` is a scalar matrix `scalar m c`, and
   `c ≠ 0` because `A` is invertible.

## Role and provenance

Provenance: internal. This module produces the matrix `P` for the outer type A argument of Task
6356 (`OuterTypeAUnitarySplitPresentationStatement`). After the coordinate change by `P`, the
inner discrepancies are scalar. That is the input of the descent to the special unitary group of
a Hermitian form. The construction is the standard one: a twisted Galois descent of
`Matrix m m M` along `M/F` gives a central simple `F`-algebra, and the outer automorphisms induce
a unitary involution on it. This is the classical link between outer forms of `SL_m` and central
simple algebras with unitary involution. The Lean proof does not depend on a literature source.
If the algebra is split, its matrix units, transported back, give the trivializing matrix `P`. The Lean
statements are matrix-level and do not assert anything about group schemes.
