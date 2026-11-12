# Reduction of the plane-model comparison to affine curve algebras

Lean module: `Langlands.AlgebraicGeometry.LangWeil.FamilyCurvePlaneReduction`, namespace
`Langlands.AlgebraicGeometry.LangWeil.CurvePlane`.

Author: Worker 189. This module is part of the proof of
`Langlands.AlgebraicGeometry.LangWeil.FamilyCurvePlaneComparisonStatement` (Task 5581). Its
main theorem `familyCurvePlaneComparison_of_core` proves that statement from the affine core
`AffineCurvePlaneComparison` (module `AffineCurvePlaneComparison`, Worker 191). Provenance:
derived. The route (Noetherian induction on the base, a dense open of each fibre, and
exceptional loci of dimension zero) is the one described in the target's Markdown, after
Tao, *The Lang–Weil bound* (2012; registered source `tao-2012-lang-weil-bound`), Section 2.
The lemmas here are internal steps and are not cited theorems.

Notation: `S₀` is an affine open of `S`, `A = Γ(S, S₀)`, `Y : Over S`; charts, `testObj` and
`testMap` are those of the Library module `Langlands.AlgebraicGeometry.AffineChartPoints`
(see `CurvePlaneCharts.md`).

## Ring lemmas

- `nilradical_isPrime_of_ringEquiv`: a ring isomorphism `T ≃ T'` carries a prime nilradical
  of `T'` back to `T`, since the nilradical of `T` is the preimage of that of `T'`.
- `nilradical_isPrime_cancelBaseChange`: hence primality of the nilradical passes from
  `A ⊗[R] B` to `A ⊗[S] (S ⊗[R] B)` (`Algebra.TensorProduct.cancelBaseChange`).

## The bound `PointBound`

`PointBound hS₀ Y B κ`, for a field `κ` with an `A`-algebra structure, says: if `κ` is finite
with `B < #κ`, there is `P ∈ κ[X 0, X 1]`, irreducible over `AlgebraicClosure κ`, with each
degree between `1` and `B`, whose zero count in `κ²` differs from `#(testObj hS₀ κ ⟶ Y)` by at
most `B`. It is a local auxiliary definition with exactly the conclusion of the target
statement, written for points over the `S`-point `Spec κ → S₀ → S`. `PointBound.mono`: it is
monotone in `B`.

## Charts and the fibre over a prime

For a prime `p` of `A`, write `s_p` for the point of `S` given by `p`.

- `chart_apply_eq_iff`: a point `w` of `Spec c.Ring` maps to `s_p` iff `w` contracts to `p`
  (the map `Spec A → S` is injective).
- `exists_fiber_prime`, `nontrivial_fiber_of_mem`: a point of `c.U` over `s_p` comes from a
  prime of the fibre ring `p.Fiber c.Ring = p.ResidueField ⊗[A] c.Ring`
  (`PrimeSpectrum.preimageEquivFiber`), which is therefore nontrivial.
- `exists_basicOpen_le_fiber_krullDimLE_zero`: assume `Y.hom` locally of finite type and
  geometrically irreducible, with fibres of pure dimension one, and let `c₁` be a chart meeting
  the fibre over `s_p`. For every chart `c` there is `h ∈ c.Ring` with `D(h) ⊆ c₁.U` and
  `p.ResidueField ⊗[A] (c.Ring ⧸ (h))` of dimension `≤ 0`. *Proof.* If `c` meets the fibre
  over `s_p`: the fibre is irreducible (geometric irreducibility), so the nonempty opens `c.U`
  and `c₁.U` of it meet at a point `z`, and a principal open `D(h)` of `c.U` contains `z` and
  lies in `c.U ∩ c₁.U` (`IsAffineOpen.exists_basicOpen_le`). The fibre ring of `c` over `p`
  has prime nilradical (`chart_nilradical_isPrime`) and pure dimension one
  (`chart_hasPureRingDimension_fiber`), so it has dimension one; `1 ⊗ h` is not nilpotent
  (it lies outside the prime of the fibre ring corresponding to `z`). Then
  `fiber_quotient_krullDimLE_zero` (module `CurvePlaneZeroDimensional`) gives dimension `≤ 0`
  for the quotient. If `c` does not meet the fibre, take `h = 0` (`D(0) = ∅`); the fibre ring
  is trivial, as any of its primes would give a point of `c.U` over `s_p`, and
  `fiber_krullDimLE_zero_of_subsingleton` applies.

## Applying the core near a prime

Fix a chart `c₁` whose fibre ring over `p` is nontrivial. With `A' = A ⧸ p` (a Noetherian
domain if `A` is Noetherian), `R' = A' ⊗[A] c₁.Ring` and `K = p.ResidueField` (the fraction
field of `A'`):

- `core_nilradical_isPrime`: the nilradical of `AlgebraicClosure K ⊗[A'] R'` is prime. The
  ring `AlgebraicClosure K ⊗[A] c₁.Ring` is nontrivial (it is a base change of the nontrivial
  `K`-algebra `K ⊗[A] c₁.Ring` along the field extension, by
  `Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_right`, and
  `cancelBaseChange`), so `chart_nilradical_isPrime` applies to it; transport along
  `cancelBaseChange`.
- `core_ringKrullDim_eq_one`: `K ⊗[A'] R' ≅ K ⊗[A] c₁.Ring` has Krull dimension one
  (`chart_nilradical_isPrime` with `L = K`, `chart_hasPureRingDimension_fiber`,
  `ringKrullDim_eq_of_hasPureRingDimension`).
- `exists_chart_core_bound`: the core applied to `A'`, `R'`, `K` (with `c₁.Ring` of finite
  type over `A` by `chart_finiteType`) gives `a₀ ∉ p` and `B₀` such that for every finite field
  `κ` killing `p`, with `a₀ ≠ 0` in `κ` and `B₀ < #κ`, some plane polynomial `F` satisfies the
  required conditions with `|#(c₁.Ring →ₐ[A] κ) - #zeros(F)| ≤ B₀`. Here `κ` becomes an
  `A'`-algebra through `Ideal.Quotient.lift`, a nonzero element of `A'` is lifted to `a₀ ∈ A`,
  and `A'`-algebra maps `R' → κ` correspond to `A`-algebra maps `c₁.Ring → κ`
  (`Algebra.TensorProduct.liftEquivRight`).

## The local step `exists_prime_bound`

Assume `Y.hom` is locally of finite type, quasi-compact and geometrically irreducible with
fibres of pure dimension one, `A` is Noetherian and the core holds. For every prime `p` of `A`
there are `a ∉ p` and `B` with `PointBound hS₀ Y B κ` for every field `κ` killing `p` with
`a ≠ 0` in `κ`. *Proof.*

1. `Y.hom` is surjective (geometrically irreducible morphisms are surjective in Mathlib), so a
   point `x₀` lies over `s_p`; an affine open `c₁` of `Y.hom⁻¹(S₀)` containing `x₀` is a chart
   meeting the fibre, so its fibre ring over `p` is nontrivial.
2. `Y.hom⁻¹(S₀)` is quasi-compact, so it is covered by finitely many charts `c i`
   (`isCompact_iff_finite_and_eq_biUnion_affineOpens`).
3. For each `i`, `exists_basicOpen_le_fiber_krullDimLE_zero` gives `h i` with
   `D(h i) ⊆ c₁.U` and zero-dimensional fibre of `(c i).Ring ⧸ (h i)` over `p`; then
   `exists_card_algHom_le_of_fiber_krullDimLE_zero` (module `CurvePlaneZeroDimensional`) gives
   `a i ∉ p` and `N i` bounding `#((c i).Ring ⧸ (h i) →ₐ[A] κ)` for fields killing `p` with
   `a i ≠ 0`.
4. `exists_chart_core_bound` gives `a₀`, `B₀` for `c₁`.
5. Take `a = a₀ · Πᵢ a i` (not in `p` since `p` is prime) and `B = B₀ + Σᵢ N i`. For a finite
   field `κ` as above with `B < #κ`, take `F` from step 4; its degrees are at most `B`. By
   `card_points_bounds` (module `CurvePlaneCharts`),
   `#(c₁.Ring →ₐ κ) ≤ #(testObj hS₀ κ ⟶ Y) ≤ #(c₁.Ring →ₐ κ) + Σᵢ N i`, and the core bound
   `|#(c₁.Ring →ₐ κ) - #zeros(F)| ≤ B₀` gives `|#(testObj hS₀ κ ⟶ Y) - #zeros(F)| ≤ B`.

`exists_affine_bound`: for `A` Noetherian, one `B` gives `PointBound hS₀ Y B κ` for all
fields `κ` with an `A`-algebra structure, by `exists_uniform_of_forall_prime` (module
`CurvePlaneNoetherianInduction`) with `PointBound.mono` and `exists_prime_bound`.

## Gluing: `familyCurvePlaneComparison_of_core`

- `pointsEquiv`: for `f : X ⟶ S` and an `A`-algebra `κ`, morphisms `x : Spec κ ⟶ X` with
  `x ≫ f = testMap hS₀ κ` are the same as morphisms `testObj hS₀ κ ⟶ Over.mk f` over `S`.
- `exists_algebra_testMap`: a morphism `s : Spec κ ⟶ S` from the spectrum of a field with image
  in `S₀` equals `testMap hS₀ κ` for some `A`-algebra structure on `κ`: `s` factors through
  the open immersion `Spec A → S` (`IsOpenImmersion.lift`), and the factor is `Spec` of a ring
  map (`Spec.map_surjective`).

*Proof of the theorem.* Let `f : X ⟶ S` satisfy the hypotheses of the target statement. Since
`S` is locally of finite type over `Spec ℤ` (in the universe-lifted form `ULift ℤ`), `S` is
locally Noetherian, so `Γ(S, U)` is Noetherian for every affine open `U`
(`LocallyOfFiniteType.isLocallyNoetherian`, `IsLocallyNoetherian.component_noetherian`).
`exists_affine_bound` applied to `Y = Over.mk f` gives a bound `B_U` for each affine open `U`.
`S` is compact, so finitely many affine opens `U ∈ t` cover it; take
`B = Σ_{U ∈ t} B_U + 1 > 0`. For a finite field `κ` and `s : Spec κ ⟶ S` with `B < #κ`: the
one point of `Spec κ` maps into some `U ∈ t`, so `s = testMap U κ` for an algebra structure
(`exists_algebra_testMap`). `PointBound U (Over.mk f) B_U κ` gives `p` with degrees and
discrepancy at most `B_U ≤ B`, and `pointsEquiv` identifies the counted points with
`{x // x ≫ f = s}`.

The proof does not use the hypothesis `FamilyPointUpperBoundStatement` of the target: the
exceptional loci are bounded algebraically by `exists_card_algHom_le_of_fiber_krullDimLE_zero`.
