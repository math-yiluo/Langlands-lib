# The diagonal split torus of `SL_m(D)` (lower bound)

Lean module: `Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankLower`.

This module proves the lower half of the split-rank formula
`splitRank (normOne K (Matrix (Fin m) (Fin m) D)) = m - 1`
(`Langlands.GroupScheme.CentralSimpleUnits.MatrixNormOneSplitRankStatement`):

```
theorem Langlands.GroupScheme.CentralSimpleUnits.sub_one_le_splitRank_normOne
    (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
    [FiniteDimensional K D] [Algebra.IsCentral K D] (m : ℕ) [NeZero m] :
    ((m - 1 : ℕ) : ℕ∞) ≤ splitRank (normOne K (Matrix (Fin m) (Fin m) D))
```

The field `K` is arbitrary (any characteristic). `D` is any finite-dimensional central
division algebra, including `D = K`. `m = 1` is allowed. The group is the Library's actual
reduced-norm-one group `normOne` from `Langlands.GroupScheme.CentralSimpleNormOne`, and
`splitRank` is the Library's supremum of `Nat.card I` over closed split tori
`splitTorus (Spec K) I ⟶ G` (`Langlands.GroupScheme.Rational.SplitTorus`).

## Provenance

The torus is the standard diagonal maximal split torus of `SL_m(D)`. Tits, *Classification
of algebraic semisimple groups* (1966), Table II, type `¹A_n`, gives relative rank `r` for
the representative `SL_{r+1}(D)`. This module proves only the inequality
`m - 1 ≤ splitRank`, and does so directly from the Library definitions. All declarations are
internal auxiliary constructions for that proof.

## Mathematical argument

Write `m = n + 1` and `A = M_{n+1}(D)`. For a commutative `K`-algebra `R` and
`t = (t_1, …, t_n) ∈ (Rˣ)ⁿ`, the torus sends `t` to the diagonal matrix
`diag((t_1 ⋯ t_n)⁻¹, t_1, …, t_n)`, read in `R ⊗_K A`.

1. **Diagonal elements.** `diagRingHom K D R : (J → R) →+* R ⊗[K] Matrix J J D` sends `x` to
   the preimage, under the Library's comparison
   `FiniteAlgebraUnits.MatrixPoints.coefficientEquiv : R ⊗ M_J(D) ≃ₐ M_J(R ⊗ D)`, of the
   diagonal matrix with entries `x i ⊗ 1`. It is a ring homomorphism by construction.
   It commutes with every coefficient-algebra map (`diagRingHom_map`, from
   `coefficientEquiv_naturality`). It is injective (`diagRingHom_injective`), because
   `r ↦ r ⊗ 1 : R → R ⊗_K D` is injective: `R` is flat over the field `K`, and
   `K → D` is injective. `diagUnit` is the corresponding unit for a family of units.

2. **Reduced norm one.** The reduced norm `Nrd` (`Langlands.CentralSimple.reducedNorm`) is
   multiplicative with values in the commutative ring `R`. So `Nrd (Y X Z) = Nrd X` whenever
   `Y Z = 1` (`reducedNorm_conj`). Let `σ` be a permutation and `P_σ` its permutation matrix
   (`σ.toPEquiv.toMatrix`). Then `P_σ · diag(x) · P_{σ⁻¹} = diag(x ∘ σ)` and
   `P_σ P_{σ⁻¹} = 1`. Transported through `coefficientEquiv`, this gives
   `Nrd (diag (x ∘ σ)) = Nrd (diag x)` (`reducedNorm_diagRingHom_perm`). Hence the monoid
   homomorphism `diagNorm : x ↦ Nrd (diag x)` satisfies
   `diagNorm (mulSingle i r) = diagNorm (mulSingle j r)`, using the transposition
   `swap i j` (`diagNorm_mulSingle`). Writing `x = ∏_k mulSingle k (x k)` gives
   `diagNorm x = diagNorm (mulSingle i₀ (∏_k x k))` (`diagNorm_eq_mulSingle_prod`). In
   particular, `Nrd (diag x) = 1` whenever `∏_k x k = 1`
   (`reducedNorm_diagRingHom_eq_one`). No splitting field and no formula for the reduced
   norm of a diagonal element are needed.

3. **Coefficient points.** `cocharVector n R t = Fin.cons (∏_j t_j)⁻¹ t` has product one
   (`prod_cocharVector`) and is natural in `R` (`cocharVector_map`). So `diagUnits` is a group
   homomorphism `(Rˣ)ⁿ → (R ⊗ A)ˣ`, and its values lie in `reducedNormOne K A R`
   (`diagUnits_mem`). `torusUnits` is the corestriction. It is injective, because the
   entries at positions `j + 1` recover `t_j` (`torusUnits_injective`). It is natural for
   coefficient-algebra maps (`torusUnits_map`).

4. **The scheme morphism.** `torusPoints` transports `torusUnits` through
   `splitTorus.pointsEquiv` and the Library's point comparison `normOnePointsEquiv`.
   `normOnePointsEquiv_naturality` and `splitTorus.pointsEquiv_naturality` give its
   naturality (`torusPoints_naturality`). Then `homOfPoints` yields the actual group-scheme
   morphism
   `torusHom K D n : splitTorus (Spec K) (ULift (Fin n)) ⟶ normOne K (Matrix (Fin (n+1)) (Fin (n+1)) D)`.
   Injectivity of `torusUnits` on every test makes `torusHom.hom.hom` a monomorphism
   (`mono_torusHom`).

5. **Closedness.** A split torus is a torus (`IsSplitTorus.isTorus`, `isSplitTorus_splitTorus`)
   and is affine (`isAffineHom_splitTorus`). `normOne` is affine and locally of finite type
   (Library instances). So the Library theorem `IsTorus.isClosedSubgroup_of_mono` makes
   `torusHom` a closed subgroup (`isClosedSubgroup_torusHom`).

6. **Conclusion.** `card_le_splitRank (ULift (Fin n)) (torusHom K D n) _` gives
   `n ≤ splitRank`, and `Nat.card (ULift (Fin n)) = n = (n + 1) - 1`. The theorem
   `sub_one_le_splitRank_normOne` first writes `m = n + 1`, using `NeZero m`.

For `m = 1` the index type is empty: the torus is the trivial split torus and the bound is
`0 ≤ splitRank`.
