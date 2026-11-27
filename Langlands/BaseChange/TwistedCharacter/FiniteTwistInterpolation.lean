import Mathlib.LinearAlgebra.Dual.Lemmas
import Langlands.BaseChange.TwistedCharacter.TwistRegularity
import Langlands.HarmonicAnalysis.GroupAction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitPolynomialOperator
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceFamilyScalar

/-! # Interpolation on finitely many character-twist families -/

noncomputable section
open scoped Classical

namespace Langlands.BaseChange

open HarmonicAnalysis HarishChandraSchwartz

universe uG uL uI

private theorem exists_eval_eq_on_finite_family
    {V : Type*} [AddCommGroup V] [Module ℂ V] {I : Type*} [Finite I]
    (d : I → Module.Dual ℂ V) (ℓ : Module.Dual ℂ (Module.Dual ℂ V)) :
    ∃ v, ∀ i, d i v = ℓ (d i) := by
  let S := Submodule.span ℂ (Set.range d)
  let : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range d)
  have he : Function.Surjective S.subtype.flip :=
    (LinearMap.flip_surjective_iff₁ (B := S.subtype)).mpr S.injective_subtype
  obtain ⟨v, hv⟩ := he (ℓ.comp S.subtype)
  exact ⟨v, fun i => LinearMap.congr_fun hv
    ⟨d i, Submodule.subset_span (Set.mem_range_self i)⟩⟩

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {L : Type uL} [CommGroup L] (p : G →* L) (hp : IsLocallyConstant p)

/-- Evaluation at a degree is a character of the parameter group. -/
def twistParameterEvaluation (a : L) : (L →* ℂˣ) →* ℂˣ where
  toFun χ := χ a
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem twistParameterEvaluation_apply (a : L) (χ : L →* ℂˣ) :
    twistParameterEvaluation a χ = χ a := rfl

include hp in
omit [IsTopologicalGroup G] in
private theorem open_ker_gradeCharacter (χ : L →* ℂˣ) :
    IsOpen ((χ.comp p).ker : Set G) :=
  (hp.comp χ).isOpen_fiber 1

local notation "mulTest[" χ "]" =>
  characterMultiplyTest (MonoidHom.comp χ p) (open_ker_gradeCharacter p hp χ)
local notation "twistD[" χ "]" =>
  characterTwistDistribution (MonoidHom.comp χ p) (open_ker_gradeCharacter p hp χ)

private theorem twistD_mul (χ η : L →* ℂˣ) (d : Distribution G) :
    twistD[χ] (twistD[η] d) = twistD[χ * η] d := by
  ext f
  change d (mulTest[η] (mulTest[χ] f)) = d (mulTest[χ * η] f)
  apply congrArg (d : SchwartzBruhat G → ℂ)
  apply Subtype.ext
  funext g
  simp only [characterMultiplyTest_apply, MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul]
  rw [← mul_assoc, mul_comm (η (p g) : ℂ)]

private def restrictDegree (a : L) (f : SchwartzBruhat G) : SchwartzBruhat G :=
  Distribution.multiplyTest
    ⟨fun g => if p g = a then 1 else 0, hp.comp (fun b : L => if b = a then 1 else 0)⟩ f

omit [IsTopologicalGroup G] in
private theorem restrictDegree_apply (a : L) (f : SchwartzBruhat G) (g : G) :
    restrictDegree p hp a f g = if p g = a then f g else 0 := by
  classical
  change (if p g = a then (1 : ℂ) else 0) * f g = _
  split_ifs <;> simp

private def testEvaluation (g : G) : Module.Dual ℂ (SchwartzBruhat G) :=
  (LinearMap.proj g).comp (schwartzBruhatSubmodule G).subtype

variable (C : Subgroup G)

include hp in
private theorem exists_exact_degree_test
    {I : Type uI} (d : I → Distribution G)
    (hC : ∀ i z, z ∈ C → ∀ f, d i (GroupAction.leftTests z f) = d i f)
    (a : L) (f : SchwartzBruhat G)
    (hf : ∀ g, f g ≠ 0 → (p g : L ⧸ C.map p) = (a : L ⧸ C.map p)) :
    ∃ f' : SchwartzBruhat G, (∀ g, f' g ≠ 0 → p g = a) ∧ ∀ i, d i f' = d i f := by
  classical
  let : CompactSpace (tsupport (f : G → ℂ)) :=
    isCompact_iff_compactSpace.mp f.hasCompactSupport
  have ht := (hp.comp_continuous
    (continuous_subtype_val : Continuous (Subtype.val : tsupport (f : G → ℂ) → G))).range_finite
  let s := ht.toFinset.filter (fun b : L => (b : L ⧸ C.map p) = (a : L ⧸ C.map p))
  have hsplit : ∑ b : s, restrictDegree p hp b.1 f = f := by
    apply Subtype.ext
    funext g
    change testEvaluation g (∑ b : s, restrictDegree p hp b.1 f) = f g
    rw [map_sum]
    change ∑ b : s, restrictDegree p hp b.1 f g = f g
    simp only [restrictDegree_apply]
    by_cases hg : f g = 0
    · simp [hg]
    · have hm : p g ∈ s := Finset.mem_filter.mpr
        ⟨ht.mem_toFinset.mpr ⟨⟨g, subset_tsupport _ hg⟩, rfl⟩, hf g hg⟩
      let b₀ : s := ⟨p g, hm⟩
      rw [Finset.sum_eq_single b₀]
      · simp [b₀]
      · intro b _ hne
        rw [ite_eq_right (fun he => hne (Subtype.ext he.symm))]
      · simp
  have hshift (b : s) : ∃ z ∈ C, p z = a * b.1⁻¹ := by
    have he : (b.1 : L ⧸ C.map p) = (a : L ⧸ C.map p) :=
      (Finset.mem_filter.mp b.2).2
    have hm : a * b.1⁻¹ ∈ C.map p := by
      apply (QuotientGroup.eq_one_iff _).mp
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, he, mul_inv_cancel]
    exact hm
  choose z hz hpz using hshift
  let f' := ∑ b : s, GroupAction.leftTests (z b) (restrictDegree p hp b.1 f)
  refine ⟨f', ?_, fun i => ?_⟩
  · intro g hg
    by_contra hne
    apply hg
    change testEvaluation g f' = 0
    rw [show f' = ∑ b : s, GroupAction.leftTests (z b) (restrictDegree p hp b.1 f) from rfl,
      map_sum]
    apply Finset.sum_eq_zero
    intro b _
    change GroupAction.leftTests (z b) (restrictDegree p hp b.1 f) g = 0
    rw [GroupAction.leftTests_apply, restrictDegree_apply]
    apply ite_eq_right
    intro h
    rw [map_mul, map_inv, hpz] at h
    exact hne (by calc
      p g = (a * b.1⁻¹) * ((a * b.1⁻¹)⁻¹ * p g) := (mul_inv_cancel_left _ _).symm
      _ = (a * b.1⁻¹) * b.1 := by rw [h]
      _ = a := inv_mul_cancel_right _ _)
  · change d i (∑ b : s, GroupAction.leftTests (z b) (restrictDegree p hp b.1 f)) = _
    rw [map_sum]
    calc
      _ = ∑ b : s, d i (restrictDegree p hp b.1 f) :=
        Finset.sum_congr rfl (fun b _ => hC i (z b) (hz b) _)
      _ = d i f := by rw [← map_sum, hsplit]

private theorem degree_twist_eq_smul (a : L) (f : SchwartzBruhat G)
    (hf : ∀ g, f g ≠ 0 → p g = a) (χ : L →* ℂˣ) :
    mulTest[χ] f = (χ a : ℂ) • f := by
  apply Subtype.ext
  funext g
  change (χ (p g) : ℂ) * f g = (χ a : ℂ) * f g
  by_cases hg : f g = 0
  · simp [hg]
  · rw [hf g hg]

private theorem exists_test_for_coefficient [Finite (L ⧸ C.map p)]
    {I : Type uI} [Finite I] (d : I → Distribution G)
    (hC : ∀ i z, z ∈ C → ∀ f, d i (GroupAction.leftTests z f) = d i f)
    (a : L) (c : I → ℂ) (Φ : Module.Dual ℂ (Distribution G))
    (hΦ : ∀ i (η : AddChar (Additive (L ⧸ C.map p)) ℂ),
      Φ (twistD[quotientCharacter (C.map p) η] (d i)) =
        c i * (quotientCharacter (C.map p) η a : ℂ)) :
    ∃ f : SchwartzBruhat G, (∀ g, f g ≠ 0 → p g = a) ∧ ∀ i, d i f = c i := by
  classical
  let Q := L ⧸ C.map p
  let : Fintype Q := Fintype.ofFinite Q
  let χ := quotientCharacter (C.map p)
  let n : ℂ := Fintype.card (Additive Q)
  have hn : n ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  obtain ⟨f, hf⟩ := exists_eval_eq_on_finite_family
    (fun j : I × AddChar (Additive Q) ℂ => twistD[χ j.2] (d j.1)) Φ
  let φ := n⁻¹ • ∑ η : AddChar (Additive Q) ℂ, ((χ η a : ℂ)⁻¹) • mulTest[χ η] f
  have hφval (i : I) : d i φ = c i := by
    simp only [φ, map_smul, map_sum, smul_eq_mul]
    have he (η : AddChar (Additive Q) ℂ) :
        (χ η a : ℂ)⁻¹ * d i (mulTest[χ η] f) = c i := by
      have hval : d i (mulTest[χ η] f) = c i * (χ η a : ℂ) := (hf (i, η)).trans (hΦ i η)
      rw [hval, mul_left_comm, inv_mul_cancel₀ (Units.ne_zero _), mul_one]
    simp_rw [he]
    rw [Finset.sum_const, Finset.card_univ, AddChar.card_eq, nsmul_eq_mul]
    change n⁻¹ * (n * c i) = c i
    rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  have hφsupport (g : G) (hg : φ g ≠ 0) : (p g : Q) = (a : Q) := by
    by_contra hga
    apply hg
    change testEvaluation g φ = 0
    simp only [φ, map_smul, map_sum, smul_eq_mul]
    change n⁻¹ * ∑ η : AddChar (Additive Q) ℂ,
      ((χ η a : ℂ)⁻¹) * mulTest[χ η] f g = 0
    have he (η : AddChar (Additive Q) ℂ) :
        (χ η a : ℂ)⁻¹ * mulTest[χ η] f g =
          η (Additive.ofMul (p g : Q) - Additive.ofMul (a : Q)) * f g := by
      rw [characterMultiplyTest_apply, MonoidHom.comp_apply, ← mul_assoc, mul_comm ((χ η a : ℂ)⁻¹)]
      simp only [χ, quotientCharacter_apply, AddChar.map_sub_eq_div, div_eq_mul_inv]
    simp_rw [he, ← Finset.sum_mul]
    have hneq : Additive.ofMul (p g : Q) - Additive.ofMul (a : Q) ≠ 0 :=
      sub_ne_zero.mpr hga
    simp [AddChar.sum_apply_eq_ite, hneq]
  obtain ⟨φ', hs, he⟩ := exists_exact_degree_test p hp C d hC a φ hφsupport
  exact ⟨φ', hs, fun i => (he i).trans (hφval i)⟩

/-- A functional with finite character expansions on finitely many twist families
can be evaluated there by one test. The degree map has a finite quotient by the
degrees of the translations preserving the base distributions. -/
def FiniteTwistFamilyInterpolationStatement : Prop :=
  Finite (L ⧸ C.map p) → Function.Injective (twistParameterEvaluation (L := L)) →
    ∀ (I : Type uI) [Finite I] (d : I → Distribution G) (Φ : Module.Dual ℂ (Distribution G))
      (P : I → L →₀ ℂ),
      (∀ i z, z ∈ C → ∀ f, d i (GroupAction.leftTests z f) = d i f) →
      (∀ i χ, Φ (twistD[χ] (d i)) = finsuppCharacterSum (P i) χ) →
      ∃ f : SchwartzBruhat G, ∀ i χ, twistD[χ] (d i) f = Φ (twistD[χ] (d i))

set_option maxHeartbeats 800000 in
/-- Extract one coefficient at a time and move its test to the corresponding degree. -/
theorem finiteTwistFamilyInterpolation :
    FiniteTwistFamilyInterpolationStatement.{uG,uL,uI} p hp C := by
  classical
  intro hF hSep I _ d Φ P hC hP
  let : Fintype I := Fintype.ofFinite I
  let s : Finset L := Finset.univ.biUnion (fun i => (P i).support)
  have hps (i : I) : (P i).support ⊆ s :=
    Finset.subset_biUnion_of_mem (fun i => (P i).support) (Finset.mem_univ i)
  have hEval (i : I) (χ : L →* ℂˣ) :
      Φ (twistD[χ] (d i)) = ∑ b ∈ s, P i b * (χ b : ℂ) := by
    rw [hP, finsuppCharacterSum, Finsupp.sum]
    exact Finset.sum_subset (hps i) (fun b _ hb => by simp [Finsupp.notMem_support_iff.mp hb])
  have hchoose (a : s) :
      ∃ f : SchwartzBruhat G, (∀ g, f g ≠ 0 → p g = (a : L)) ∧ ∀ i, d i f = P i a := by
    obtain ⟨v, hv⟩ := exists_finsuppCharacterSum_eq (s.image twistParameterEvaluation)
      (fun ev => if ev = twistParameterEvaluation a.1 then 1 else 0)
    have hv' (b : L) (hb : b ∈ s) :
        ∑ χ ∈ v.support, v χ * (χ b : ℂ) = if b = a.1 then 1 else 0 := by
      simpa only [finsuppCharacterSum, Finsupp.sum, hSep.eq_iff, twistParameterEvaluation_apply] using hv
        (twistParameterEvaluation b) (Finset.mem_image_of_mem _ hb)
    let Φ' := ∑ χ ∈ v.support, v χ • Φ.comp (twistD[χ])
    have hΦ' (i : I) (η : L →* ℂˣ) :
        Φ' (twistD[η] (d i)) = P i a * (η a : ℂ) := by
      have he : Φ' (twistD[η] (d i)) =
          ∑ χ ∈ v.support, v χ * Φ (twistD[χ * η] (d i)) := by
        simp only [Φ', LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro χ _
        rw [twistD_mul p hp]
      rw [he]
      simp_rw [hEval, MonoidHom.mul_apply, Units.val_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      calc
        _ = ∑ b ∈ s, (P i b * (η b : ℂ)) * ∑ χ ∈ v.support, v χ * (χ b : ℂ) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun χ _ => by ring)
        _ = _ := by
          rw [Finset.sum_eq_single a.1]
          · rw [hv' _ a.2, ite_eq_left rfl, mul_one]
          · intro b hb hne
            simp [hv' b hb, hne]
          · exact fun h => (h a.2).elim
    exact exists_test_for_coefficient p hp C d hC a.1 (fun i => P i a) Φ'
      (fun i η => hΦ' i (quotientCharacter (C.map p) η))
  choose f hf hd using hchoose
  refine ⟨∑ a : s, f a, fun i χ => ?_⟩
  change d i (mulTest[χ] (∑ a : s, f a)) = Φ (twistD[χ] (d i))
  simp only [map_sum, hEval]
  simp_rw [degree_twist_eq_smul p hp _ _ (hf _) χ, map_smul, hd, smul_eq_mul]
  calc
    _ = ∑ a : s, P i a * (χ a : ℂ) := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    _ = _ := Finset.sum_coe_sort s (fun b => P i b * (χ b : ℂ))

end Langlands.BaseChange
