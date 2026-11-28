import Langlands.Global.RankinSelberg.RealUniformWhittakerDual
import Langlands.Global.RankinSelberg.RealWhittakerUniformGrowth
import Langlands.Representation.Archimedean.RealStandardHermitianDual
import Langlands.Representation.Archimedean.TransposePairingProof

/-! # Weyl inverse transpose on real block Whittaker models -/

noncomputable section

open Langlands.Archimedean Langlands.Automorphic Langlands.KFiniteDual
open Langlands.LocalFactor.Archimedean Langlands.GeneralLinear
open scoped TensorProduct Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open RealLocalJacquet (dualBlock realRank_map_dualBlock)

attribute [local instance 100] LieRing.ofAssociativeRing

variable (r : ℕ) (ds : List RealBlock)

local notation "n" => r + 1
local notation "es" => ds.map dualBlock
local notation "V" => realStandardKFinite n ds
local notation "W" => realStandardKFinite n es
local notation "ρ" => realStandardRep n ds
local notation "π" => realStandardLie n ds
local notation "θ" => complexifiedMatrixLieIota ℝ n
local notation "K" => Matrix.unitaryGroup (Fin n) ℝ
local notation "𝔤" => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ

/-- The dual inducing blocks give the inverse-transpose twist of the prescribed
irreducible real standard module. -/
def RealStandardBlockTransposeEquivStatement : Prop :=
  realRank ds = n → IsIrreducibleGKModule ρ π →
    ∃ E : W ≃ₗ[ℂ] V,
      (∀ (k : K) (f : W), E (realStandardRep n es k f) = ρ k (E f)) ∧
      ∀ (X : 𝔤) (f : W), E (realStandardLie n es X f) = π (θ X) (E f)

set_option maxHeartbeats 1000000 in
theorem realStandardBlockTransposeEquiv : RealStandardBlockTransposeEquivStatement r ds := by
  intro hr hi
  let hg := isRealGKModule_realStandardModule n ds
  let hadm := realStandardAdmissible n ds
  obtain ⟨B, ⟨hBK, hBL⟩, hB₀⟩ := realTransposePairing r V ρ π hg hi hadm
  let σ := kDualRep ρ
  let τ := RealContragredient.dualLie hg
  have hK (k : K) (f : V) : B.flip (ρ k f) = (ρ).dual k (B.flip f) := by
    ext w
    change B w (ρ k f) = B (ρ k⁻¹ w) f
    have h := hBK k (ρ k⁻¹ w) f
    rwa [compactIota_real, Representation.self_inv_apply] at h
  let B₁ := B.flip.intertwiningMap_of_isIntertwiningMap _ _ hK
  let A : V →ₗ[ℂ] kDual ρ := B.flip.codRestrict _ fun f =>
    FiniteVectors.IsFiniteVector.map B₁ (hg.1 f)
  have hAK (k : K) (f : V) : A (ρ k f) = σ k (A f) := Subtype.ext (hK k f)
  have hAL (X : 𝔤) (f : V) : A (π X f) = τ (θ X) (A f) := by
    apply Subtype.ext
    ext w
    change B w (π X f) = ((τ (θ X) (A f) : kDual ρ) : Module.Dual ℂ V) w
    rw [RealContragredient.dualLie_apply_apply]
    have h := hBL (θ X) w f
    rw [complexifiedMatrixLieIota_involutive] at h
    exact eq_neg_of_add_eq_zero_right h
  have hA₀ : A ≠ 0 := by
    intro h
    apply hB₀
    ext w f
    exact congrArg (fun v : kDual ρ => (v : Module.Dual ℂ V) w) (LinearMap.congr_fun h f)
  have hKer := hi.2 (LinearMap.ker A)
    (fun k f hf => by
      rw [LinearMap.mem_ker] at hf ⊢
      rw [hAK, hf, map_zero])
    (fun X f hf => by
      rw [LinearMap.mem_ker] at hf ⊢
      rw [hAL, hf, map_zero])
  have hInj : Function.Injective A := by
    rcases hKer with h | h
    · exact LinearMap.ker_eq_bot.mp h
    · exact (hA₀ (LinearMap.ker_eq_top.mp h)).elim
  have hDual := RealContragredient.isIrreducible_kDual hg hi hadm
  have hRange := hDual.2 (LinearMap.range A)
    (fun k _ ⟨f, hf⟩ => ⟨ρ k f, by rw [hAK, hf]⟩)
    (fun X _ ⟨f, hf⟩ => ⟨π (θ X) f, by rw [hAL, complexifiedMatrixLieIota_involutive, hf]⟩)
  have hSurj : Function.Surjective A := by
    rcases hRange with h | h
    · exact (hA₀ (LinearMap.range_eq_bot.mp h)).elim
    · exact LinearMap.range_eq_top.mp h
  let F := LinearEquiv.ofBijective A ⟨hInj, hSurj⟩
  obtain ⟨D, hD⟩ := exists_realStandardDualFiniteDualEquiv hr hi
  refine ⟨D.trans F.symm, ?_, ?_⟩
  · intro k f
    apply F.injective
    change F (F.symm (D (realStandardRep n es k f))) = A (ρ k (F.symm (D f)))
    rw [F.apply_symm_apply, hAK, show A (F.symm (D f)) = D f from F.apply_symm_apply (D f)]
    exact hD.map_realStandardRep k f
  · intro X f
    apply F.injective
    change F (F.symm (D (realStandardLie n es X f))) = A (π (θ X) (F.symm (D f)))
    rw [F.apply_symm_apply, hAL, complexifiedMatrixLieIota_involutive,
      show A (F.symm (D f)) = D f from F.apply_symm_apply (D f)]
    exact hD.map_realStandardLie X f

private theorem dualBlock_involutive : Function.Involutive dualBlock := by
  intro d
  cases d <;> simp [dualBlock, RealCharacterData.inverse_inverse, ComplexCharacterData.inverse_inverse]

private theorem map_dualBlock_map_dualBlock :
    (ds.map dualBlock).map dualBlock = ds := by
  rw [List.map_map, show dualBlock ∘ dualBlock = id from funext dualBlock_involutive, List.map_id]

private theorem dualFunction_twice (w : Langlands.GeneralLinear n ℝ → ℂ) :
    ArchimedeanLocal.dualFunction n (ArchimedeanLocal.dualFunction n w) = w := by
  funext g
  exact congrArg w (weylInverseTranspose_involutive n ℝ g)

/-- Inverse transpose with the long Weyl element identifies the exact compact-finite
Whittaker models of a rank-correct irreducible real standard module and of its dual blocks.
The dual standard module is irreducible and the additive character changes sign. -/
def RealBlockWhittakerDualStatement : Prop :=
  realRank ds = n → IsIrreducibleGKModule ρ π →
    IsIrreducibleGKModule (realStandardRep n es) (realStandardLie n es) ∧
    ∀ (a : ℝˣ) (w : Langlands.GeneralLinear n ℝ → ℂ),
      ArchimedeanLocal.dualFunction n w ∈ realWhittakerModel r es (-a) ↔ w ∈ realWhittakerModel r ds a

set_option maxHeartbeats 900000 in
theorem realBlockWhittakerDual : RealBlockWhittakerDualStatement r ds := by
  intro hr hi
  obtain ⟨E, hK, hL⟩ := realStandardBlockTransposeEquiv r ds hr hi
  have he : realRank es = n := (realRank_map_dualBlock ds).trans hr
  have hj : IsIrreducibleGKModule (realStandardRep n es) (realStandardLie n es) := by
    let : Nontrivial V := hi.1
    refine ⟨E.surjective.nontrivial, fun U hUK hUL => ?_⟩
    let T := E.toLinearMap
    have hEq := hi.2 (U.map T)
      (fun k _ ⟨u, hu, h⟩ => ⟨_, hUK k u hu, by
        change E u = _ at h
        change E (realStandardRep n es k u) = _
        rw [hK, h]⟩)
      (fun X _ ⟨u, hu, h⟩ => ⟨_, hUL (θ X) u hu, by
        change E u = _ at h
        change E (realStandardLie n es (θ X) u) = _
        rw [hL, complexifiedMatrixLieIota_involutive, h]⟩)
    have hMap := Submodule.map_injective_of_injective (show Function.Injective T from E.injective)
    rcases hEq with h | h
    · exact Or.inl (hMap (h.trans (by rw [Submodule.map_bot])))
    · exact Or.inr (hMap (h.trans (by rw [Submodule.map_top, LinearMap.range_eq_top.mpr E.surjective])))
  refine ⟨hj, fun a w => ⟨?_, ?_⟩⟩
  · intro hw
    obtain ⟨F, hFK, hFL⟩ := realStandardBlockTransposeEquiv r es he hj
    have h := RealUniformWhittakerDual.dualFunction_mem_of_equiv F hFK
      (fun X f => hFL (1 ⊗ₜ[ℝ] X) f) (-a) ((realWhittakerModels_eq r es he (-a)) ▸ hw)
    rw [dualFunction_twice r, map_dualBlock_map_dualBlock, neg_neg, ← realWhittakerModels_eq r ds hr a] at h
    exact h
  · intro hw
    rw [realWhittakerModels_eq r es he (-a)]
    exact RealUniformWhittakerDual.dualFunction_mem_of_equiv E hK (fun X f => hL (1 ⊗ₜ[ℝ] X) f)
      a ((realWhittakerModels_eq r ds hr a) ▸ hw)

end Langlands.Global.RankinSelbergGlobal
