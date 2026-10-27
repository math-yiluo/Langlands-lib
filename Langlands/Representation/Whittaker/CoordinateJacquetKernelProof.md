# Proof of uniform Whittaker vanishing on a coordinate Jacquet kernel

Worker 264 proves the published closed proposition
`Langlands.Whittaker.CoordinateJacquetKernelStatement.{uF,uV}` from
`Langlands.Representation.Whittaker.CoordinateJacquetKernelStatement`:

```lean
theorem Langlands.Whittaker.coordinateJacquetKernelStatement :
    CoordinateJacquetKernelStatement.{uF, uV}
```

The module adds no definitions to the statement's data and changes no imported
file. Its helper declarations live in the namespace
`Langlands.Whittaker.CoordinateJacquetKernel`.

## Exact target

The target quantifies over every prime `p`, every `F : PadicField.{uF} p`,
every `T : F.TopologicalData` with `T.topology` installed, every `n : ℕ`
(including `0`), every complex module `V : Type uV`, every representation
`ρ` of `GeneralLinear (n + 1) F.Carrier` on `V`, and every raw additive
character `ψ : AddChar F.Carrier ℂ` that is continuous and of unit norm. The
trivial character is included. `ρ` is assumed smooth. `ℓ : Module.Dual ℂ V` is
any algebraic functional with

```lean
∀ g, (∀ j k, k < j → g.val j k = 0) ∧ (∀ j, g.val j j = 1) →
  ∀ w, ℓ (ρ g w) = (∏ j : Fin n, ψ (g.val j.castSucc j.succ)) * ℓ w
```

The zero functional is included. For every `i : Fin n` and every `v` with
`(twoBlock (n + 1) i.val _).jacquetMk ρ v = 0`, one `ε > 0` is chosen first.
Then for every `a : Fin (n + 1) → F.Carrierˣ`,
`T.normalizedAbs ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier) < ε`
implies `ℓ (ρ (torus a) v) = 0`, where `torus a` is the diagonal matrix with
entries `a j`. Only the selected adjacent ratio is bounded. The other ratios
and the common scalar are unrestricted. For `n = 0` there is no `i`.

The proof never uses the smoothness hypothesis: it is introduced as
`_hsmooth` and ignored.

## Proof outline

1. **A character is trivial near zero (`exists_pos_forall_addChar_eq_one`).**
   Let `ψ` be a continuous complex additive character of unit norm. Then some
   `ε > 0` gives `ψ x = 1` whenever `T.normalizedAbs x < ε`. If `ψ = 1`,
   take `ε = 1`. Otherwise package `ψ` with the Library's
   `UnitaryAdditiveCharacter.ofComplex`. Then `T.exists_additiveTrivialAt` gives
   an integer `n` with `ψ` trivial on `T.additiveLattice n`. Let
   `y = T.uniformizer ^ (-n)` and take `ε = T.normalizedAbs y`. `y` is nonzero
   because `T.ord_uniformizer` and `T.ord_zero` rule out `T.uniformizer = 0`,
   so `ε` is positive by `T.normalizedAbs_pos`.

   Now suppose `T.normalizedAbs x < ε`. By `T.normalizedAbs_mul`,
   `T.normalizedAbs x = T.normalizedAbs (x / y) * ε`, so
   `T.normalizedAbs (x / y) < 1`. Then `T.normalizedAbs_le_one_iff_mem_integers`
   gives `x / y ∈ T.Integers`. `T.mem_additiveLattice_iff_div_mem_integers`
   turns this into `x ∈ T.additiveLattice n`, so `ψ x = 1`. This is how the
   conductor's valuation-lattice triviality becomes a positive
   normalized-absolute-value threshold.

2. **Scaling the input (`exists_pos_forall_addChar_mul_eq_one`).** Fix
   `c : F.Carrier`. Then some `δ > 0` gives `ψ (r * c) = 1` whenever
   `T.normalizedAbs r < δ`. If `c = 0`, use `ψ 0 = 1` with `δ = 1`. Otherwise
   take `δ = ε / T.normalizedAbs c` and use multiplicativity of
   `T.normalizedAbs`.

3. **Diagonal conjugation (`torus`, `torus_val`, `torus_conj_apply`).** The
   abbreviation `torus` is literally the statement's homomorphism. Its matrix
   is `Matrix.diagonal fun j => (a j : K)` by `rfl`. Multiplying by diagonal
   matrices on both sides gives the `(j, k)` entry of `torus a * g * (torus a)⁻¹`
   as `a j * g j k * (a k)⁻¹` (`Matrix.mul_diagonal`, `Matrix.diagonal_mul`).

4. **The threshold submodule (`HasThreshold`, `thresholdSubmodule`).** Fix
   `ρ`, `ℓ` and `i`. Say `v` *has a threshold* if some `ε > 0` gives
   `ℓ (ρ (torus a) v) = 0` for every `a` with selected ratio below `ε`. This is
   exactly the statement's conclusion for one `v`. These vectors form a
   submodule. `0` has the threshold `1`. A sum takes the minimum of its two
   thresholds. A scalar multiple keeps its threshold, because `ℓ ∘ ρ (torus a)`
   is linear.

5. **One generating relation (`hasThreshold_relation`).** Let `u` lie in the
   unipotent radical of `twoBlock (n + 1) i.val _`, let `w : V`, and let
   `t = torus a`. The Library's `splitUnipotent_of_mem_twoBlock` says the
   entries of `u` agree with the identity outside the block `p ≤ i < q`. So
   by step 3, `t * u * t⁻¹` has zeros below the diagonal and ones on it.
   Equivariance therefore applies to it. In the product
   `∏ j, ψ ((t * u * t⁻¹) j.castSucc j.succ)`, every factor with `j ≠ i` has
   indices outside the block. Its entry is an identity off-diagonal entry, zero,
   so the factor is `ψ 0 = 1` (`Finset.prod_eq_single`). The remaining factor is
   `ψ ((a i.castSucc / a i.succ) * u i.castSucc i.succ)`. From
   `ρ t (ρ u w) = ρ (t * u * t⁻¹) (ρ t w)` and linearity,

   ```text
   ℓ (ρ t (ρ u w - w))
     = ψ ((a_i / a_(i+1)) * u_(i,i+1)) * ℓ (ρ t w) - ℓ (ρ t w)
   ```

   Step 2 with `c = u i.castSucc i.succ` gives `δ > 0`, chosen before `a`. If
   the selected ratio has normalized absolute value below `δ`, the character
   value is `1` and the difference is zero. So `ρ u w - w` has a threshold.

6. **The whole kernel (`hasThreshold_of_jacquetMk_eq_zero`).** Let
   `B = twoBlock (n + 1) i.val _`. If `B.jacquetMk ρ v = 0`, then applying
   `B.jacquetModuleEquiv` (`B.jacquetModuleEquiv_mk`) and `Jacquet.mk_eq_zero`
   puts `v` in `Jacquet.relations ρ (B.unipotentSubgroup F.Carrier)`. By
   definition this is the span of the vectors `ρ u w - w`. By step 5 every
   generator lies in `thresholdSubmodule`, so `Submodule.span_le` puts the
   whole span there. This is the finite span induction with thresholds
   combined by minima.

7. **Main theorem.** `coordinateJacquetKernelStatement` introduces the
   statement's binders. The `let`-bound `unipotent`, `θ`, `torus` and `B` are
   unfolded definitionally. It then applies step 6.

## Provenance

This is the direct relation-generator route given in the task and in the
statement's Markdown. The statement is an internal derived isolation and
strengthening of the Jacquet-kernel step in Jacquet, Piatetski-Shapiro and
Shalika, *Automorphic forms on GL(3) I* (Ann. of Math. 1979), Proposition (2.2).
In that proof (printed pp. 182-183), `𝒲_i` is the span of the vectors
`ρ(u)W - W` with `u` in the unipotent radical `V_i` of the parabolic of type
`(i, r - i)`. The paper says their restrictions to the torus vanish when the
`i`-th coordinate is small enough, and gives no further argument. This module
proves a formal analogue of that step in the stronger form of the published
statement: an arbitrary algebraic equivariant functional, the full diagonal
torus, and a raw character that may be trivial. It does not formalize
Proposition (2.2), Lemma (2.2.1), or Remark (2.2.5).
