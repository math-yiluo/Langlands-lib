import Langlands.Automorphic.CuspidalAdmissible.Finiteness
import Langlands.Automorphic.CuspidalAdmissible.Split
import Langlands.Automorphic.GeneralLinearParabolicCuspidalEquivalence
import Langlands.Automorphic.GroupSchemeQuotientL2
import Langlands.Global.AdeleQuotientCompactProof
import Langlands.Global.AdelicGLDeterminantNormOne
import Langlands.Global.HeckeDeterminantLocalConstancy

/-! # Small right translates of deep unipotent orbits in the adelic quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set Filter Topology
open scoped CategoryTheory.MonObj Topology
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme

namespace Langlands.Automorphic.GroupSchemeFunctions

open OperatorRealization CuspidalL2

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

set_option hygiene false in
local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local instance : IsAffine (GLG).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance : Smooth (GLG).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive GLG)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ GLG)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)

local notation "A" => AdelicGroupPoints F GLG
local notation "Γ" => positiveRationalSubgroup F GLG T i
local notation "Q" => PositiveRationalQuotient F GLG T i

private theorem norm_le_of_matrixConstantTerm_zero [CompactSpace (AdeleQuotient F)]
    (f : Langlands.Automorphic.ContinuousRationalFunctions F n) (hf : IsCuspidal F n f)
    {a b : ℕ} (h : a + b = n) (ha : 0 < a) (hb : 0 < b) (g : AdelicGL F n) (M : ℝ)
    (hM : ∀ Y : Matrix (Fin a) (Fin b) (Adeles F),
      ‖ContinuousRationalFunctions.evaluate F n f g -
        ContinuousRationalFunctions.evaluate F n f (Langlands.GeneralLinear.blockUnipotent h Y * g)‖ ≤ M) :
    ‖ContinuousRationalFunctions.evaluate F n f g‖ ≤ M := by
  let μU := matrixQuotientHaar F a b
  have hz := hf a b h ha hb g
  have hint := integrable_constantTermIntegrand h f g
  have h₁ : ContinuousRationalFunctions.evaluate F n f g =
      ∫ Y, (ContinuousRationalFunctions.evaluate F n f g - Langlands.Automorphic.constantTermIntegrand F n h f g Y) ∂μU := by
    rw [integral_sub (integrable_const _) hint, integral_const]
    unfold Langlands.Automorphic.constantTerm at hz
    rw [hz]
    simp
  rw [h₁]
  exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun Y =>
    hM (matrixLift Y))).trans_eq (by simp [μU])

include hi I e hc in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3300000 in
/-- For a fixed identity neighborhood, outside one compact part of the positive rational
quotient the value of a cuspidal continuous function is bounded by its oscillation under
right translates in that neighborhood. -/
theorem exists_compact_cuspDisplacementCover (hn : 0 < n) (U : Set A)
    (hU : U ∈ 𝓝 (1 : A)) :
    ∃ D : Set Q, IsCompact D ∧
      ∀ ψ : C(Q, ℂ), positiveQuotientContinuousPullback F GLG T i ψ ∈
        normalizedParabolicCuspidalSubrepresentation F GLG hPD hG →
      ∀ q ∉ D, ∀ M : ℝ,
        (∀ a ∈ U, ‖ψ q - ψ (LeftCosetSpace.rightTranslate Γ a q)‖ ≤ M) → ‖ψ q‖ ≤ M := by
  let m := GeneralLinearGroupPoints.adelicHomeomorph F n
  let j (z : InfiniteAdelicGL F n × FiniteAdelicGL F n) := m.symm (AdelicGL.pair F n z.1 z.2)
  have hj : Continuous j := m.symm.continuous.comp (AdelicGL.continuous_pair F n)
  have hj₁ : j (1, 1) = 1 := by
    change m.symm (AdelicGL.pair F n 1 1) = 1
    rw [pair_eq_ofInfinite_mul_ofFinite, map_one, map_one, one_mul, map_one]
  have hpre : j ⁻¹' U ∈ 𝓝 ((1 : InfiniteAdelicGL F n), (1 : FiniteAdelicGL F n)) :=
    hj.continuousAt.preimage_mem_nhds (hj₁.symm ▸ hU)
  obtain ⟨Uinf, hUinf, Uf, hUf, hprod⟩ := mem_nhds_prod_iff.mp hpre
  obtain ⟨Uinf', hUinf'sub, hUinf'open, hUinf'₁⟩ := mem_nhds_iff.mp hUinf
  let : NonarchimedeanGroup (FiniteAdelicGL F n) := finiteAdelicGL_nonarchimedeanGroup F n
  obtain ⟨L, hL⟩ := NonarchimedeanGroup.is_nonarchimedean Uf hUf
  have hnear (u : InfiniteAdelicGL F n) (hu : u ∈ Uinf')
      (l : FiniteAdelicGL F n) (hl : l ∈ L.toSubgroup) : m.symm (AdelicGL.pair F n u l) ∈ U := by
    change j (u, l) ∈ U
    exact hprod (Set.mk_mem_prod (hUinf'sub hu) (hL hl))
  obtain ⟨Ω, hΩ, hcover⟩ := exists_cusp_cover F n hn L.toSubgroup L.isOpen hUinf'open hUinf'₁
  have hDg : 0 < (Module.finrank ℚ F : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let d : ℝ := (Module.finrank ℚ F : ℝ) * n
  have hd : 0 < d := mul_pos hDg hnR
  let c (g : AdelicGL F n) : ℝ := -Real.log (absDet F n g) / d
  have hc' : Continuous c := ((continuous_absDet F n).log fun g => (absDet_pos F n g).ne').neg.div_const d
  have hcentral : Continuous (centralTorus F n) :=
    (AdelicGL.ofInfinite F n).continuous.comp ((continuous_torInf F n).comp
      (continuous_pi fun _ => continuous_id))
  let p (g : AdelicGL F n) : Q := LeftCosetSpace.mk Γ (m.symm (g * centralTorus F n (c g)))
  have hp : Continuous p := (LeftCosetSpace.continuous_mk Γ).comp
    (m.symm.continuous.comp (continuous_id.mul (hcentral.comp hc')))
  refine ⟨p '' Ω, hΩ.image hp, ?_⟩
  intro ψ hψ q hq M hosc
  let : CompactSpace (AdeleQuotient F) := compactSpace_adeleQuotient F
  let f := continuousGeneralLinearEquiv F n (positiveQuotientContinuousPullback F GLG T i ψ)
  have hfc : IsCuspidal F n f := (mem_normalizedGeneralLinearParabolicCuspidal_iff F n hPD hG _).mp hψ
  have hfval (g : AdelicGL F n) : ContinuousRationalFunctions.evaluate F n f g =
      ψ (LeftCosetSpace.mk Γ (m.symm g)) := rfl
  obtain ⟨p₁, hp₁⟩ := (positiveQuotientHomeomorph F GLG T i hi I e hc).surjective q
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (rationalNormOneSubgroup F GLG) p₁
  have hqeq : LeftCosetSpace.mk Γ x.val = q := by
    simpa only [positiveQuotientHomeomorph_mk] using hp₁
  obtain ⟨rationalShift, t, z, ht, hz⟩ := hcover (m x.val)
  have hγ (δ : RationalGL F n) (g : AdelicGL F n) :
      LeftCosetSpace.mk Γ (m.symm (AdelicGL.rational F n δ * g)) = LeftCosetSpace.mk Γ (m.symm g) := by
    rw [map_mul]
    have hδ : m.symm (AdelicGL.rational F n δ) ∈ Γ := by
      let r := (GeneralLinearGroupPoints.rationalEquiv F n).symm δ
      apply rationalSubgroup_le_positiveRationalSubgroup F GLG T i
      refine ⟨r, m.injective ?_⟩
      rw [GeneralLinearGroupPoints.adelicHomeomorph_rational]
      exact ((GeneralLinearGroupPoints.rationalEquiv F n).apply_symm_apply δ).symm ▸
        (m.apply_symm_apply (AdelicGL.rational F n δ)).symm
    exact LeftCosetSpace.mk_subgroup_mul Γ ⟨_, hδ⟩ _
  let z' := z * centralTorus F n t
  have hz'q : LeftCosetSpace.mk Γ (m.symm z') = q := by
    rw [show z' = _ from ht.symm, hγ, m.symm_apply_apply, hqeq]
  rcases hz with hzΩ | ⟨a, ha, hdeep⟩
  · have hx : absDet F n (m x.val) = 1 := by
      have hx' := (GeneralLinearGroupPoints.mem_normOneSubgroup_iff_determinantNorm F n x.val).mp x.property
      change AdelicBlockDeterminantCharacter.determinantNorm F n (m x.val) = 1 at hx'
      rw [CuspidalAdmissible.absDet_eq_determinantNorm, hx']
      rfl
    have hz₁ : absDet F n (z * centralTorus F n t) = 1 := by
      rw [← ht, absDet_rational_mul, hx]
    have hl := congrArg Real.log hz₁
    rw [absDet_mul, Real.log_mul (absDet_pos F n z).ne' (absDet_pos F n _).ne',
      absDet_centralTorus, Real.log_pow, Real.log_exp, Real.log_one] at hl
    have ht' : t = c z := by
      apply (eq_div_iff hd.ne').2
      rw [mul_comm t d]
      change (Module.finrank ℚ F : ℝ) * (n : ℝ) * t = -Real.log (absDet F n z)
      rw [mul_assoc]
      linarith only [hl]
    apply False.elim (hq ⟨z, hzΩ, ?_⟩)
    change LeftCosetSpace.mk Γ (m.symm (z * centralTorus F n t)) = q at hz'q
    simpa only [p, ht'] using hz'q
  · have hsum : a.val + (n - a.val) = n := Nat.add_sub_cancel' a.isLt.le
    have hb : 0 < n - a.val := Nat.sub_pos_of_lt a.isLt
    rw [← hz'q, ← hfval]
    apply norm_le_of_matrixConstantTerm_zero F n f hfc hsum ha hb z' M
    intro Y
    obtain ⟨δ, u, l, hu, hl, heq⟩ := hdeep Y
    have haU := hnear u hu l hl
    have hy : Langlands.GeneralLinear.blockUnipotent hsum Y * z' =
        AdelicGL.rational F n δ * (z' * AdelicGL.pair F n u l) := by
      change _ * (z * centralTorus F n t) = _ * ((z * centralTorus F n t) * _)
      rw [← mul_assoc, heq, pair_eq_ofInfinite_mul_ofFinite]
      have hcomm := centralTorus_commute F n t (AdelicGL.ofInfinite F n u * AdelicGL.ofFinite F n l)
      simpa only [mul_assoc] using congrArg (fun h => AdelicGL.rational F n δ * (z * h)) hcomm.symm
    simp only [hy, hfval]
    rw [hγ]
    simp only [map_mul]
    have hq' : LeftCosetSpace.mk Γ (m.symm z' * m.symm (AdelicGL.pair F n u l)) =
        LeftCosetSpace.rightTranslate Γ (m.symm (AdelicGL.pair F n u l)) q := by
      rw [← hz'q]
      rfl
    rw [hq', hz'q]
    exact hosc _ haU


end Langlands.Automorphic.GroupSchemeFunctions
