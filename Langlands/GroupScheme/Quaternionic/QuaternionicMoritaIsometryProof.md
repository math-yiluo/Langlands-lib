# Proof of the quaternionic Morita isometry comparison

Author: Worker 74.

Module `Langlands.GroupScheme.Quaternionic.QuaternionicMoritaIsometryProof`, namespace
`Langlands.GroupScheme.Quaternionic`. The theorem
`Langlands.GroupScheme.Quaternionic.quaternionicMoritaIsometry` proves exactly
`Langlands.GroupScheme.Quaternionic.QuaternionicMoritaIsometryStatement.{u}` at an arbitrary
universe `u`. Every hypothesis of the published statement is kept and none is added. There is
no restriction on the characteristic of `K`; characteristic 2 is included. The result is the
isometry-group part of J. Tits, *Formes quadratiques, groupes orthogonaux et algèbres de
Clifford*, Invent. Math. 5 (1968), §3, Proposition 6 (printed p. 30 / PDF p. 13), for
`E = M_m(D)` (`tits-1968-formes-quadratiques-clifford`). Tits states it with "Il est clair
que". The Lean proof follows the route in the statement's Markdown and the task context: split
`D`, transport the isometry condition through the matrix chart, and compare the functors of
points.

The isomorphism is one of actual group schemes over `Spec (AlgebraicClosure K)`. It is built
from an identification of the groups of points over every scheme `T` over `Spec L`, natural in
`T`, and not from rational points alone.

## Notation

`L` is a field with `[Algebra K L]` and `e : L ⊗[K] D ≃ₐ[L] M_2(L)` is a splitting chart.
Only the final theorem takes `L = AlgebraicClosure K`. The Library supplies the chart
`matrixChartR e R : R ⊗[K] M_m(D) ≃+* Matrix (Fin m × Fin 2) (Fin m × Fin 2) R` for every
`K`-algebra `R` that is also an `L`-algebra with `IsScalarTower K L R` (module
`Quaternionic.SplittingMatrix`), and the block involution matrix
`S = σ.blockInvolutionMatrix e` with inverse `σ.blockInvolutionMatrixInv e`.
`matrixChartR_baseChange` says that the chart turns the conjugate transpose `x ↦ ᵗx^σ` into
`X ↦ S Xᵀ S⁻¹`. `transpose_blockInvolutionMatrix` says that `S` is symmetric when
`dim D^σ = 3`, in every characteristic.

## Step 1: points of `O(q)` (section `FirstKindInvolution.Points`)

- `IsometryCut.map_mem_baseChange`: a `K`-algebra map `φ : R → S` sends `R ⊗ M` into `S ⊗ M`.
- `IsometryCut.isometrySubgroupMap` and `coe_isometrySubgroupMap`: the induced homomorphism
  of isometry subgroups `isometrySubgroup hM Q R →* isometrySubgroup hM Q S`, given by
  `φ ⊗ id` on the underlying units. It is well defined because `φ ⊗ id` commutes with the
  defect `u ↦ u Q τ(u) - Q` (`IsometryCut.map_defect`).
- `FirstKindInvolution.isStable_quadraticKernel`: Tits's subspace `{x - ᵗx^σ}` of `M_n(D')` is
  stable under `y ↦ u y ᵗu^σ`. It is `IsometryCut.isStable_alternatingSubspace`, restated
  with the type `quadraticKernel` so that later rewrites are type-correct.
- `FirstKindInvolution.isometryUnits σ' Q R` (an abbreviation): the subgroup of units `u` of
  `R ⊗[F] M_n(D')` with `u Q ᵗu^σ - Q ∈ R ⊗ {x - ᵗx^σ}`.
- `isometryPointsHom`, `isometryPointsHom_apply`, `isometryPointsHom_bijective`,
  `isometryPointsEquiv` and `isometryPointsEquiv_apply`: for a representative `Q` of `q`,
  the points of `σ'.isometryGroup q` over `T` are the isometry units over `Γ(T, ⊤)`. A point
  is sent to the unit of its image under the closed immersion `σ'.isometryGroupι q`
  (`FiniteAlgebraUnits.pointsEquiv`). It lands in `isometryUnits` by
  `mem_range_isometryGroupι_iff`. Injectivity uses that the closed immersion is a
  monomorphism. Surjectivity uses `mem_range_isometryGroupι_iff` in the other direction.
  `Q` may be any representative of `q`, not only `Quotient.out q`. Below, this is applied to
  the scalar form represented by the split Gram matrix itself.
- `isometryPointsEquiv_naturality`: for `a : T' ⟶ T` the identification commutes with
  `isometrySubgroupMap` along the induced map `Γ(T, ⊤) → Γ(T', ⊤)`
  (`FiniteAlgebraUnits.pointsEquiv_naturality`).

## Step 2: transport through the matrix chart (namespace `MoritaIsometry`)

Abstract matrix algebra (section `Abstract`). Let `Φ : A ≃+* M_κ(R)`, `τ : A → A` and
`S, S'` be matrices with `S S' = S' S = 1`, `Sᵀ = S` and `Φ(τ a) = S Φ(a)ᵀ S'`.

- `transpose_eq_of_mul_eq_one`: then `S'ᵀ = S'`.
- `exists_sub_eq_iff`: `x = a - τ a` for some `a` exactly when `Φ(x) S = Y - Yᵀ` for some
  matrix `Y`. In one direction take `Y = Φ(a) S`; in the other take `a = Φ⁻¹(Y S')`.
- `map_defect_mul`: `Φ(y H τ(y) - H) S = g C gᵀ - C` with `g = Φ(y)` and `C = Φ(H) S`.
- `exists_sub_eq_defect_iff`: the combination of the two. The defect `y H τ(y) - H` lies in
  `{a - τ a}` exactly when `g C gᵀ - C` has the form `Y - Yᵀ`.
- `subgroupEquivOfIff`: a group isomorphism that carries one subgroup exactly onto another
  restricts to an isomorphism of the subgroups.

Scalar side (section `ScalarSide`), for the identity involution `scalar L` of `L`:

- `scalarChart L N R := (matrixEquivTensor (Fin N) L R).symm : R ⊗[L] M_N(L) ≃ M_N(R)`.
  `scalarChart_baseChange` says it turns the base-changed involution into the transpose, and
  `scalarChart_naturality` says it commutes with maps of `L`-algebras.
- `mem_scalar_isometryUnits_iff`: a unit `y` lies in `(scalar L).isometryUnits C R` exactly
  when `g C gᵀ - C = Y - Yᵀ` for some `Y`, where `g = scalarChart y`. This is
  `exists_sub_eq_defect_iff` with `S = S' = 1`, after
  `IsometryCut.alternatingSubspace_baseChange`.

Quaternionic side (section `QuaternionicSide`):

- `blockIndex m : Fin m × Fin 2 ≃ Fin (2 * m)`, and
  `chartN e m R : R ⊗[K] M_m(D) ≃+* M_{2m}(R)` is `matrixChartR e R` followed by reindexing
  along `blockIndex m`. `chartN_apply`, `chartN_one_tmul` and `chartN_naturality` (for
  `L`-algebra maps `f`, used through `f.restrictScalars K`) are its basic properties.
- `invMatrix e σ m` and `invMatrixInv e σ m` are `S` and `S⁻¹` reindexed along `blockIndex m`.
  `invMatrix_mul_inv` and `invMatrix_inv_mul` say they are inverse, and `transpose_invMatrix`
  says `S` is symmetric when `dim D^σ = 3`. `chartN_baseChange` is
  `Φ(ᵗx^σ) = S Φ(x)ᵀ S⁻¹` over every `R`.
- `gramN e σ m Q₀ := chartN e m L (1 ⊗ Q₀) * invMatrix e σ m`, the split Gram matrix
  `C = Φ(Q₀) S` over `L`.
- `mem_isometryUnits_iff`: a unit `y` of `R ⊗[K] M_m(D)` lies in `σ.isometryUnits Q₀ R`
  exactly when `g C gᵀ - C = Y - Yᵀ` for some `Y`, with `g = chartN e m R y` and `C`
  mapped to `R`. This is `exists_sub_eq_defect_iff` with `Φ = chartN e m R`, the symmetric
  matrix `S` and `chartN_baseChange`, followed by `chartN_one_tmul`.
- `theta e m R := chartN e m R` followed by `matrixEquivTensor`, a ring isomorphism
  `R ⊗[K] M_m(D) ≅ R ⊗[L] M_{2m}(L)`. `scalarChart_theta` says `scalarChart ∘ theta = chartN`.
- `isometryUnitsEquiv e σ m R hσ Q₀ : σ.isometryUnits Q₀ R ≃* (scalar L).isometryUnits C R`
  is `theta` on units, restricted with `subgroupEquivOfIff`. Both membership conditions are
  the same matrix condition on `g = chartN e m R y`, by `mem_isometryUnits_iff`,
  `mem_scalar_isometryUnits_iff` and `scalarChart_theta`. `coe_isometryUnitsEquiv` records
  its value, and `isometryUnitsEquiv_naturality` says it commutes with the maps
  `isometrySubgroupMap` induced by an `L`-algebra map `f : R → R'` (on the `K`-side through
  `f.restrictScalars K`). The proof applies the injective `scalarChart` and uses
  `scalarChart_naturality` and `chartN_naturality`.

## Step 3: the group-scheme isomorphism (section `Assembly`)

The `K`-algebra of sections `restrictedSections K L T` of a scheme `T` over `Spec L`, with
its `L`-algebra structure and scalar tower, comes from `Quaternionic.SymplecticReductive`.

- `splitModel e σ m Q₀ T` is `(scalar L).isometryUnits C Γ(T, ⊤)`, the common model for the
  points over `T`.
- `basePointsEquiv` identifies the points of
  `(GroupScheme.baseChange (scalarBaseMap K L)).obj (σ.isometryGroup q)` over `T` with the
  model. It is the composite of `GroupScheme.baseChangePointsEquiv` (points of the base
  change over `T` are points of `O(q)` over `T` viewed over `Spec K`), `isometryPointsEquiv`
  for `q` and `Q₀`, and `isometryUnitsEquiv` with `R = restrictedSections K L T`.
- `basePointsEquiv_naturality`: the composite is natural in `T`. This combines
  `GroupScheme.baseChangePointsEquiv_naturality`, `isometryPointsEquiv_naturality` and
  `isometryUnitsEquiv_naturality`, the last applied to the `L`-algebra map of sections
  induced by `a : T' ⟶ T`.
- `splitIso` is `isoOfPointModels` (module `Langlands.GroupScheme.Torus.Split`) applied to
  this model, with restriction maps `isometrySubgroupMap`, `basePointsEquiv` on one side and
  `(scalar L).isometryPointsEquiv` for the representative `C` of `[C]` on the other. It is an
  isomorphism of group schemes over `Spec L`:

  `(GroupScheme.baseChange (scalarBaseMap K L)).obj (σ.isometryGroup q) ≅
  (scalar L).isometryGroup [C]`.

## Step 4: nondegeneracy (section `Nondegenerate`)

- `gramN_add_transpose`: `C + Cᵀ = Φ(1 ⊗ (Q₀ + ᵗQ₀^σ)) S`. Indeed, `chartN_baseChange` over
  `R = L` gives `Φ(ᵗQ₀^σ) = S Φ(Q₀)ᵀ S⁻¹`, so `Φ(ᵗQ₀^σ) S = S Φ(Q₀)ᵀ = Cᵀ` because `S` is
  symmetric.
- `isNondegenerateQuadratic_gramN`: if `q = [Q₀]` is nondegenerate then so is `[C]`. The
  polar matrix of `[C]` is `C + Cᵀ` (`scalar_polar_mk`). The polar matrix `Q₀ + ᵗQ₀^σ` of `q`
  (`polar_mk`) is a unit, its images under `x ↦ 1 ⊗ x` and the ring isomorphism `Φ` are
  units, and `S` is a unit with inverse `invMatrixInv e σ m`.

## Step 5: the final theorem

`quaternionicMoritaIsometry` introduces the data of the statement. Since `D` is central and
simple (a division ring), `CentralSimple.exists_matrix_chart` gives `n` and a chart
`AlgebraicClosure K ⊗[K] D ≃ₐ M_n(AlgebraicClosure K)`. `CentralSimple.finrank_eq_matrix_size`
and `finrank K D = 4` give `n * n = 4`, so `n = 2` (`Nat.mul_self_inj`). The representative
is `Q₀ = Quotient.out q` (`Quotient.out_eq`). The witness is `Q = [gramN e σ m Q₀]`, which is
nondegenerate by Step 4. The isomorphism is `splitIso`, since `toAlgebraicClosure K` is by
definition `scalarBaseMap K (AlgebraicClosure K)`.

The proof does not use `LocalSpinRankOneStatement`, `LocalSpinKneserTitsStatement` or any
statement whose planned proof consumes them.
