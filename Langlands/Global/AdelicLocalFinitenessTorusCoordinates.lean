import Langlands.Global.AdelicNormOneRootBox
import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Global.PositiveRealTorusLog
import Langlands.Global.SimpleRootBoxCompact
import Langlands.GroupScheme.Rational.RelativeWeylFaithfulness
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Translation coordinates for the local-finiteness system -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory Module Set TensorProduct
open scoped Classical CategoryTheory.MonObj NNReal

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus Langlands.LinearAlgebra.RationalSpan

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local notation "Δ" => simpleRelativeRoots i ν
local notation "V" => RealCharacterDual F T.toGrp
local notation "H" => realCharacterDualMap F T.toGrp G i

/-- The actual log of the simple root along its supplied positive translation. -/
def localFinitenessRootStep (t : Δ → AdelicGroupPoints F T.toGrp) (α : Δ) : ℝ :=
  characterLog F T.toGrp (t α) α.val

/-- The supplied maximal-parabolic and central translations give unit vectors
in joint root and ambient-centre logarithmic coordinates. -/
def LocalFinitenessTorusCoordinatesStatement : Prop :=
  IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i ν →
  ∀ {Ua : Δ → GroupScheme (Spec (CommRingCat.of F))}
    (u : ∀ α, Ua α ⟶ G) (t : Δ → AdelicGroupPoints F T.toGrp)
    {r : ℕ} (z : Fin r → AdelicGroupPoints F T.toGrp),
    IsLocalFinitenessGroupData i ν u t z →
    ∃ e : V ≃L[ℝ] ((Δ → ℝ) × (Fin r → ℝ)),
      (∀ ℓ α, (e ℓ).1 α = ℓ α.val / localFinitenessRootStep i ν t α) ∧
      (∀ ℓ, (e ℓ).2 = 0 ↔ H ℓ = 0) ∧
      (∀ α, 0 < localFinitenessRootStep i ν t α ∧
        e (characterLog F T.toGrp (t α)) = (Pi.single α 1, 0)) ∧
      (∀ j, e (characterLog F T.toGrp (z j)) = (0, Pi.single j 1))

theorem localFinitenessTorusCoordinates : LocalFinitenessTorusCoordinatesStatement i ν := by
  classical
  intro hG hi hν Ua u t r z hData
  obtain ⟨-, -, hOther, hPositive, hTOne, -, hZRoot, hZLin, hZSpan⟩ := hData
  let : Smooth G.X.hom := hG.smooth
  let hfin := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  let : Fintype Δ := hfin.fintype
  let step := localFinitenessRootStep i ν t
  have hPos (α : Δ) : 0 < step α := by
    obtain ⟨x, hx, hxx⟩ := hPositive α
    change 0 < characterLog F T.toGrp (t α) α.val
    rw [characterLog_eq_log_characterValue, ← hxx, PositiveRealIdeles.absoluteValue_full,
      Units.val_pow_eq_pow_val, NNReal.coe_pow, Real.log_pow]
    exact mul_pos (Nat.cast_pos.mpr Module.finrank_pos) (Real.log_pos (by exact_mod_cast hx))
  have hLog_zero {s : AdelicGroupPoints F T.toGrp} {χ : characterLattice T}
      (hs : Lie.characterValue χ s = 1) : characterLog F T.toGrp s χ = 0 := by
    rw [characterLog_eq_log_characterValue, hs, map_one, Units.val_one, NNReal.coe_one, Real.log_one]
  let b := Basis.mk hZLin (ge_of_eq hZSpan)
  let root : V →ₗ[ℝ] Δ → ℝ := LinearMap.pi fun α => (step α)⁻¹ • dualEval F T.toGrp α.val
  let cent : V →ₗ[ℝ] Fin r → ℝ := b.equivFun.toLinearMap.comp H
  let f := root.prod cent
  have hRoot (ℓ : V) (α : Δ) : (f ℓ).1 α = ℓ α.val / step α := by
    change (step α)⁻¹ * ℓ α.val = _
    rw [div_eq_mul_inv, mul_comm]
  have hCent (ℓ : V) : (f ℓ).2 = 0 ↔ H ℓ = 0 := by
    change b.equivFun (H ℓ) = 0 ↔ H ℓ = 0
    exact map_eq_zero_iff _ b.equivFun.injective
  have hT (α : Δ) : f (characterLog F T.toGrp (t α)) = (Pi.single α 1, 0) := by
    refine Prod.ext (funext fun β => ?_) ((hCent _).2 ((characterLog_map F T.toGrp G i (t α)).symm.trans (hTOne α)))
    change (f (characterLog F T.toGrp (t α))).1 β = (Pi.single α 1 : Δ → ℝ) β
    rw [hRoot, Pi.single_apply]
    by_cases hβα : β = α
    · subst β
      rw [ite_eq_left rfl]
      exact div_self ((hPos α).ne')
    · rw [ite_eq_right hβα, hLog_zero (hOther α β hβα), zero_div]
  have hZ (j : Fin r) : f (characterLog F T.toGrp (z j)) = (0, Pi.single j 1) := by
    refine Prod.ext (funext fun β => ?_) (funext fun k => ?_)
    · change (f (characterLog F T.toGrp (z j))).1 β = 0
      rw [hRoot, hLog_zero (hZRoot j β), zero_div]
    · change b.equivFun (H (characterLog F T.toGrp (z j))) k = (Pi.single j 1 : Fin r → ℝ) k
      rw [← characterLog_map]
      rw [← show b j = characterLog F G (map F T.toGrp G i (z j)) from Basis.mk_apply _ _ _,
        Basis.equivFun_self, Pi.single_apply]
      simp [eq_comm]
  have hInj : Function.Injective f := by
    apply (LinearMap.ker_eq_bot.mp ?_)
    rw [Submodule.eq_bot_iff]
    intro ℓ hℓ
    have h₀ : f ℓ = 0 := LinearMap.mem_ker.mp hℓ
    have hR (α : Δ) : ℓ α.val = 0 := by
      have h := congrFun (congrArg Prod.fst h₀) α
      rw [hRoot] at h
      exact (div_eq_zero_iff.mp h).resolve_right (hPos α).ne'
    have hG₀ : H ℓ = 0 := (hCent ℓ).mp (congrArg Prod.snd h₀)
    have hUnion := simpleRelativeRoots_restrictedCharacters_ratSpan_eq_top F G T i ν hG hi hν
    apply AddMonoidHom.ext
    intro χ
    obtain ⟨C, _, hχC⟩ := exists_abs_le_of_toRat_mem_ratSpan
      (c := χ) (hUnion ▸ Submodule.mem_top)
    have hb := hχC ℓ 0 (fun ψ hψ => by
      rcases hψ with hψ | ⟨ξ, rfl⟩
      · rw [hR ⟨ψ, hψ⟩, abs_zero]
      · have h := DFunLike.congr_fun hG₀ ξ
        change ℓ (torusCharacterRestrict i ξ) = 0 at h
        rw [h, abs_zero])
    rw [mul_zero] at hb
    exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
  have hSurj : Function.Surjective f := by
    rintro ⟨x, y⟩
    refine ⟨(∑ α : Δ, x α • characterLog F T.toGrp (t α)) +
      ∑ j : Fin r, y j • characterLog F T.toGrp (z j), ?_⟩
    simp only [map_add, map_sum, map_smul, hT, hZ]
    refine Prod.ext (funext fun α => ?_) (funext fun j => ?_)
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  let : FiniteDimensional ℝ V := FiniteDimensional.of_injective f hInj
  let e := (LinearEquiv.ofBijective f ⟨hInj, hSurj⟩).toContinuousLinearEquiv
  exact ⟨e, hRoot, hCent, fun α => ⟨hPos α, hT α⟩, hZ⟩

end Langlands.Global
