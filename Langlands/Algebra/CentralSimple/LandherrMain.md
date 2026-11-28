# Landherr's theorem for units of relative reduced norm one

Module: `Langlands.Algebra.CentralSimple.LandherrMain`.

Let `F` be a number field, `E/F` a separable quadratic extension with `d = skewSq F E`
(`E = F(√d)`, module `Langlands.Algebra.CentralSimple.LandherrQuadraticData`), `B` a
finite-dimensional central simple `E`-algebra which is an `F`-algebra through `E`, and
`τ : FirstKindInvolution F B` acting on `E` by the conjugation (`hτ`). `relNorm` is the
relative reduced norm (module `Langlands.Algebra.CentralSimple.LandherrNonsplitLocal`).

- `diagOne b = diag(b, 1)`; `matrixBaseMap_diagOne` computes its scalar extension.
- `coordPoint_algebraMap`: coordinates coming from `F` give the scalar extensions of the
  corresponding entries over `F`.
- `relNorm_one_tmul_eq_one`: if `relNorm F (1 ⊗ y) = 1`, then `relNorm k (1 ⊗ y) = 1` for every
  field `k` over `F` (`relNorm_naturality`).
- `exists_local_nbhd` applies over a complete nontrivially normed field `k` over `F` with the
  unitary splitting property and with `d` nonsquare in `k`. Let `y ∈ Bˣ` have relative
  reduced norm one and satisfy `1 ⊗ y = x τ_k(x)` for a unit `x` of `k ⊗_F B`.
  For all sufficiently large `L` there are neighbourhoods of
  coordinates on which `targetMap (diag(1 ⊗ y, 1)) (coordPoint c)` is a square in the
  `k`-subalgebra it generates (from `exists_target_list` and `exists_target_nbhd`).
- `globalTarget τ D g = t D ᵗτ(t)` with `t = listProd (List.ofFn g)` in `M₂(B)`.
- `exists_entries` takes a unit `y` of relative reduced norm one such that at every
  finite and infinite place `v` there is a unit `x_v` of `F_v ⊗_F B` with
  `1 ⊗ y = x_v τ_v(x_v)`. For any basis `β` of `B` over `F` and finite set `S` of
  finite places, the result gives a finite place `v₀ ∉ S` at which `d` is a square,
  a length `L` and entries `g : Fin L → B × B` whose coordinates in `β` are integral
  at every finite `v ∉ S ∪ {v₀}`. At each place of `S` and each infinite place,
  either `d` is a square in the completion or the scalar extension of
  `globalTarget τ (diag(y, 1)) g` is a square in the local algebra it generates.
- `exists_eq_mul_of_relNorm_eq_one`: if `y ∈ Bˣ` is `τ`-symmetric, of relative reduced norm
  one, and of the form `x_v τ_v(x_v)` with `x_v` a unit of `F_v ⊗_F B` at every finite and
  infinite place, then `y = x τ(x)` for a unit `x` of `B`.

## Proof of `exists_entries`

`exists_split_finitePlace` gives `v₀ ∉ S` with `d` a square in `F_{v₀}`. At every finite place
where `d` is not a square, give `F_v` the normed field structure
`Valued.toNontriviallyNormedField` (its topology is the valuation topology) and use
`finiteCompletion_unitaryInvolutionSplitting`. At infinite places use the absolute value and
`infiniteCompletion_unitaryInvolutionSplitting`. At a nonsplit place `exists_local_nbhd`
gives a sufficient length for the neighbourhood construction. At a split place take length
zero and the whole coordinate space. Let `L` be the sum of these lengths over `S` and the
infinite places. `exists_approx_coords` gives `x : Fin L × Fin 2 × ι → F` with all coordinates in
the local neighbourhoods at the places of `S` and at the infinite places and integral at
every other finite place except `v₀`. The entries are `g j = (Σᵢ x(j,0,i) βᵢ,
Σᵢ x(j,1,i) βᵢ)`; their scalar extensions have the coordinates `x`
(`coordPoint_algebraMap`), and `matrixBaseMap_targetMap` identifies the local matrices.

## Proof of `exists_eq_mul_of_relNorm_eq_one`

Let `βB`, `β₂` be bases of `B` and `M₂(B)`. Let `S` be the finite set
(`finite_setOf_not_basisIntAt`, `finite_setOf_not_forall_intAt`, `finite_setOf_not_intAt`,
`finite_setOf_valuation_ne_one`) of finite places where the required integrality or unit
conditions fail. Outside `S`, the structure constants of `β₂`, the coordinates of `1`,
the images of `βB` under `upperPart` and `lowerPart`, the matrices `diag(y, 1)` and
`diag(y⁻¹, 1)`, and the images of `β₂` under `ᵗτ` are integral, and `2` and `d` are units.
Take `v₀`, `g` from `exists_entries` and
put `t = listProd (List.ofFn g)` and `y' = t diag(y, 1) ᵗτ(t)`. Then `ᵗτ(y') = y'`, `y'` is a
unit of `M₂(B)` and hence of the commutative subalgebra `K = F[y']` (`isUnit_subalgebra`).

Apply `exists_sq_sub_mul_sq_of_local` (module
`Langlands.Algebra.CentralSimple.LandherrNormGlobal`) to `K`, `d` and `z = y'`:

- at `v ∈ S` and at infinite places, either `d` is a square or `exists_entries` and
  `exists_mul_self_eq_tmul` (module `Langlands.Algebra.CentralSimple.LandherrLocalTarget`)
  give a square root of `1 ⊗ y'` in `F_v ⊗_F K`;
- at a finite `v ∉ S` where `d` is not a square, `v ≠ v₀`; the entries of `g` are integral,
  so `t`, `t⁻¹` are integral (`intAt_listProd`), and so are
  `y' = t diag(y, 1) ᵗτ(t)` and `y'⁻¹ = ᵗτ(t⁻¹) diag(y⁻¹, 1) t⁻¹` (`intAt_mul`, `intAt_map`).
  By `exists_monic_of_intAt`, `y'` and `y'⁻¹` are roots of monic polynomials with
  `v`-integral coefficients, and `2`, `d` are `v`-units.

This gives `X, Y ∈ K` with `X² - d Y² = y'`, and `mul_matrix_eq_of_norm` (module
`Langlands.Algebra.CentralSimple.LandherrFinish`) gives `Z₀ = X + r Y` with
`Z₀ ᵗτ(Z₀) = y'`. Then `Z = t⁻¹ Z₀` satisfies `Z ᵗτ(Z) = diag(y, 1)`, and
`exists_eq_mul_of_diag_unit` gives the unit `x`.

## Provenance

This is the case of reduced norm one of Landherr's theorem: Lemma 1 of §5.5 in Kneser,
*Lectures on Galois Cohomology of Classical Groups* (1969), printed p. 71 (PDF p. 77), proved
on printed pp. 71–76 (PDF pp. 77–82); compare Platonov and Rapinchuk, *Algebraic Groups and
Number Theory* (1994), §6.7, Theorem 6.27, printed p. 359 (PDF p. 369). Kneser moves `y` by
an element `t` of reduced norm one, chosen by strong approximation to be close to the
inverses of local solutions of reduced norm one at finitely many places and integral
elsewhere, so that `t y τ(t)` is locally a norm from the commutative algebra it generates
over `E` at every place (it is close to `1`, or integral at an unramified place, or the place
splits), and then globally by the Hasse principle. The implementation here follows the same
three local cases, but replaces strong approximation in the group of elements of reduced
norm one by additive strong approximation of the entries of elementary `2 × 2` matrices over
`B`, whose products reach every local target at the nonsplit places, and descends from
`M₂(B)` to `B` by cancellation of a unit summand.
