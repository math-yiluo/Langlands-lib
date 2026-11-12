import Langlands.Shimura.Unitary.HarrisLevelFreeSmall
import Langlands.Shimura.Unitary.PositiveArithmeticFinite

/-!
# Harris's (4.5) for compact levels of a definite group

For an involution `σ` whose real scalar extension is positive, rational points whose diagonal
image lies in a conjugate of a compact level have finite order
(`AlgebraInvolution.isOfFinOrder_of_conj_mem`). So the hypothesis `RationalFiniteOrder` of
`HarrisLevelFreeSmall` holds for every compact level, and Harris's (4.5) follows from the
torsion-freeness of the away level at one place.

* `RationalFiniteOrder.of_isPositive`: compact levels satisfy `RationalFiniteOrder`.
* `isCompact_splitLevel`, `isCompact_pairLevel`: the levels `e⁻¹ (U × L)` and `K_ℓ × C_p` are
  compact when their factors are.
* `levelTorsionFreeAt_splitLevel`: an away level inside a torsion-free subgroup of `σ(ℚ_v)` is
  torsion-free at `v`.
* `DividingLevelFree.of_isPositive`, `HarrisDividingLevelFree.of_isPositive`: (4.5) for compact
  factors and an away level torsion-free at one place.
-/

noncomputable section

open Langlands.Global
open scoped NumberField

set_option autoImplicit false

universe v

namespace Langlands.Shimura.DefiniteForms

variable {A : Type v} [Ring A] [Algebra ℚ A] {σ : AlgebraInvolution ℚ A} [Module.Finite ℚ A]

/-- For an involution whose real scalar extension is positive, every compact level satisfies
`RationalFiniteOrder`. -/
theorem RationalFiniteOrder.of_isPositive (hpos : (σ.baseChange ℝ).IsPositive)
    {K : Subgroup σ.FiniteAdelicPoints} (hK : IsCompact (K : Set σ.FiniteAdelicPoints)) :
    RationalFiniteOrder σ K :=
  fun g γ hγ => σ.isOfFinOrder_of_conj_mem hpos hK g γ hγ

variable {n : ℕ} {hn : n ≠ 0}

/-- The level `e⁻¹ (U × L)` is compact when `U` and `L` are. -/
theorem isCompact_splitLevel {U : Subgroup (σ.DividingPoints n)}
    {L : Subgroup (σ.PrimeToPoints n)} (hU : IsCompact (U : Set (σ.DividingPoints n)))
    (hL : IsCompact (L : Set (σ.PrimeToPoints n))) :
    IsCompact (splitLevel σ n hn U L : Set σ.FiniteAdelicPoints) := by
  have h : (splitLevel σ n hn U L : Set σ.FiniteAdelicPoints) =
      (σ.finiteAdelicPointsSplit n hn).toHomeomorph ⁻¹' ((U : Set _) ×ˢ (L : Set _)) := rfl
  rw [h, Homeomorph.isCompact_preimage]
  exact hU.prod hL

/-- If the away level `L` lies in a subgroup `W` of `σ(ℚ_v)` without nontrivial elements of finite
order, at a place `v` not dividing `n`, then `e⁻¹ (1 × L)` is torsion-free at `v`. -/
theorem levelTorsionFreeAt_splitLevel (v : PrimeToFinitePlace n)
    {W : Subgroup (σ.Points (FiniteCompletion ℚ v.1))} (hW : ∀ w ∈ W, IsOfFinOrder w → w = 1)
    {L : Subgroup (σ.PrimeToPoints n)} (hL : L ≤ W.comap (primeToLocalMap σ n v)) :
    LevelTorsionFreeAt σ v.1 (splitLevel σ n hn ⊥ L) := by
  intro k hk hfin
  rw [← primeToLocalMap_finiteAdelicPointsSplit σ hn v k] at hfin ⊢
  exact hW _ (hL (mem_splitLevel.1 hk).2) hfin

/-- Harris's (4.5) for compact factors of a definite group: if `σ ⊗ ℝ` is positive, `U` and `L`
are compact, and `e⁻¹ (1 × L)` is torsion-free at a place `v` not dividing `n`, then `U` acts
without fixed points on `GJ(ℚ) \ GJ(A_f) / e⁻¹ (1 × L)`. -/
theorem DividingLevelFree.of_isPositive (hpos : (σ.baseChange ℝ).IsPositive)
    {U : Subgroup (σ.DividingPoints n)} {L : Subgroup (σ.PrimeToPoints n)}
    (hU : IsCompact (U : Set (σ.DividingPoints n))) (hL : IsCompact (L : Set (σ.PrimeToPoints n)))
    (v : PrimeToFinitePlace n) (htf : LevelTorsionFreeAt σ v.1 (splitLevel σ n hn ⊥ L)) :
    DividingLevelFree σ n hn U L :=
  DividingLevelFree.of_levelTorsionFreeAt
    (RationalFiniteOrder.of_isPositive hpos (isCompact_splitLevel hU hL)) v htf

section Pair

variable {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hℓp : ℓ ≠ p)
  {vℓ : {v : FinitePlace ℚ // (ℓ : 𝓞 ℚ) ∈ v.asIdeal}}
  {vp : {v : FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal}}

include hℓ hp hℓp in
/-- For distinct primes `ℓ` and `p`, Harris's `K_ℓ × C_p` is compact when `K_ℓ` and `C_p` are. -/
theorem isCompact_pairLevel {Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1))}
    {Cp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))}
    (hKℓ : IsCompact (Kℓ : Set (σ.Points (FiniteCompletion ℚ vℓ.1))))
    (hCp : IsCompact (Cp : Set (σ.Points (FiniteCompletion ℚ vp.1)))) :
    IsCompact (pairLevel σ (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Cp :
      Set (σ.DividingPoints (ℓ * p))) := by
  rw [pairLevel_eq_comap σ hℓ hp hℓp vℓ vp]
  have h : (((Kℓ.prod Cp).comap (pairPointsEquiv σ hℓ hp hℓp vℓ vp).toMonoidHom :
      Subgroup (σ.DividingPoints (ℓ * p))) : Set (σ.DividingPoints (ℓ * p))) =
      (pairPointsEquiv σ hℓ hp hℓp vℓ vp).toHomeomorph ⁻¹' ((Kℓ : Set _) ×ˢ (Cp : Set _)) := rfl
  rw [h, Homeomorph.isCompact_preimage]
  exact hKℓ.prod hCp

include hℓ hp hℓp in
/-- Harris's (4.5) for a definite group (1999, p.310): for distinct primes `ℓ` and `p`, if
`σ ⊗ ℝ` is positive, `K_ℓ`, `C_p` and `K^{ℓ,p}` are compact, and `K^{ℓ,p}` is torsion-free at a
place `v` over a prime other than `ℓ` and `p`, then `K_ℓ × C_p` acts without fixed points on
`GJ(ℚ) \ GJ(A_f) / K^{ℓ,p}`. -/
theorem HarrisDividingLevelFree.of_isPositive (hn : ℓ * p ≠ 0)
    (hpos : (σ.baseChange ℝ).IsPositive)
    {Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1))}
    {Cp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))} {L : Subgroup (σ.PrimeToPoints (ℓ * p))}
    (hKℓ : IsCompact (Kℓ : Set (σ.Points (FiniteCompletion ℚ vℓ.1))))
    (hCp : IsCompact (Cp : Set (σ.Points (FiniteCompletion ℚ vp.1))))
    (hL : IsCompact (L : Set (σ.PrimeToPoints (ℓ * p))))
    (v : FinitePlace ℚ) (hvℓ : (ℓ : 𝓞 ℚ) ∉ v.asIdeal) (hvp : (p : 𝓞 ℚ) ∉ v.asIdeal)
    (htf : LevelTorsionFreeAt σ v (splitLevel σ (ℓ * p) hn ⊥ L)) :
    HarrisDividingLevelFree σ (ℓ * p) hn (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Cp L :=
  HarrisDividingLevelFree.of_levelTorsionFreeAt hn _ _
    (RationalFiniteOrder.of_isPositive hpos
      (isCompact_splitLevel (isCompact_pairLevel hℓ hp hℓp hKℓ hCp) hL))
    v hvℓ hvp htf

end Pair

end Langlands.Shimura.DefiniteForms
