import Langlands.Global.IdeleAbsoluteValue
import Langlands.Global.IntegralFiniteAdeles
import Langlands.ClassField.Global.IntegralIdeleClassQuotientFinite
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone

/-!
# Compactness of the norm-one idele class group

For a number field `F`, the norm-one ideles `I¹` form the kernel of the normalized idelic
absolute value. This module proves that `I¹ / F^×` is compact, constructs a compact set of
norm-one ideles meeting every principal coset of `I¹`, and deduces that the kernel of the
absolute value on the actual idele class group is compact. See the paired Markdown.
-/

noncomputable section

universe u

namespace Langlands.Global.NormOneIdeleClass

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  NumberField.Units.dirichletUnitTheorem Module
open Langlands.Global Langlands.ClassField.Global
open scoped NNReal RestrictedProduct

variable (F : Type u) [Field F] [NumberField F]

/-- The norm-one ideles `I¹`: the kernel of the normalized idelic absolute value. -/
abbrev normOneIdeles : Subgroup (Ideles F) :=
  (IdeleAbsoluteValue.full F).toMonoidHom.ker

/-- The principal ideles, as a subgroup of the norm-one ideles. -/
abbrev normOnePrincipal : Subgroup (normOneIdeles F) :=
  (principalIdeles F).subgroupOf (normOneIdeles F)

/-- The quotient `I¹ / F^×` of the norm-one ideles by the principal ideles, with the quotient
topology of the subspace topology. -/
abbrev NormOneIdeleClasses := normOneIdeles F ⧸ normOnePrincipal F

/-- **Compactness of the norm-one idele class group.** For every number field `F`, the quotient
`I¹ / F^×` of the norm-one ideles by the principal ideles is compact. -/
def NormOneIdeleClassCompactStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F], CompactSpace (NormOneIdeleClasses F)

section Box

/-- Adeles whose archimedean coordinates have norm at most `R` and whose finite part is
integral at every finite place. -/
def adeleBox (R : ℝ) : Set (Adeles F) :=
  {a | (∀ w, ‖a.1 w‖ ≤ R) ∧ a.2 ∈ integralFiniteAdeles F}

/-- Ideles `x` such that both `x` and `x⁻¹` lie in `adeleBox F R`. -/
def ideleBox (R : ℝ) : Set (Ideles F) :=
  {x | (x : Adeles F) ∈ adeleBox F R ∧ ((x⁻¹ : Ideles F) : Adeles F) ∈ adeleBox F R}

omit [NumberField F] in
theorem isCompact_closedBall_infiniteCompletion (w : InfinitePlace F) (R : ℝ) :
    IsCompact (Metric.closedBall (0 : InfiniteCompletion F w) R) := by
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
  have h : Metric.closedBall (0 : InfiniteCompletion F w) R =
      InfinitePlace.Completion.extensionEmbedding w ⁻¹' Metric.closedBall 0 R := by
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_preimage]
    rw [hi.norm_map_of_map_zero (map_zero _)]
  rw [h]
  exact hi.isClosedEmbedding.isCompact_preimage (isCompact_closedBall 0 R)

theorem isCompact_adeleBox (R : ℝ) : IsCompact (adeleBox F R) := by
  have h1 : IsCompact (Set.univ.pi fun w : InfinitePlace F =>
      Metric.closedBall (0 : InfiniteCompletion F w) R) :=
    isCompact_univ_pi fun w => isCompact_closedBall_infiniteCompletion F w R
  have h2 := isCompact_integralFiniteAdeles F
  have h := h1.prod h2
  have he : adeleBox F R = (Set.univ.pi fun w : InfinitePlace F =>
      Metric.closedBall (0 : InfiniteCompletion F w) R) ×ˢ
        (integralFiniteAdeles F : Set (FiniteAdeles F)) := by
    ext a
    change _ ↔ (a.1 ∈ _ ∧ a.2 ∈ _)
    refine and_congr ⟨fun h w _ => ?_, fun h w => ?_⟩ Iff.rfl
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact h w
    · have hw := h w (Set.mem_univ w)
      rwa [Metric.mem_closedBall, dist_zero_right] at hw
  rw [he]
  exact h

theorem isCompact_ideleBox (R : ℝ) : IsCompact (ideleBox F R) := by
  have : T2Space (FiniteAdeles F) := inferInstanceAs
    (T2Space (Πʳ v : FinitePlace F, [FiniteCompletion F v, v.adicCompletionIntegers F]))
  have : T2Space (Adeles F) := inferInstanceAs (T2Space (InfiniteAdeles F × FiniteAdeles F))
  have hA := isCompact_adeleBox F R
  have h : IsCompact (adeleBox F R ×ˢ (MulOpposite.unop ⁻¹' adeleBox F R)) :=
    hA.prod (MulOpposite.opHomeomorph.isCompact_preimage.mp hA)
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage h

end Box

section Archimedean

variable {F}

omit [NumberField F] in
theorem normAtPlace_ringEquiv_mixedSpace (y : InfiniteAdeles F) (w : InfinitePlace F) :
    normAtPlace w (InfiniteAdeleRing.ringEquiv_mixedSpace F y) = ‖y w‖ := by
  rcases w.isReal_or_isComplex with hw | hw
  · rw [normAtPlace_apply_of_isReal hw, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) _
  · rw [normAtPlace_apply_of_isComplex hw, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) _

theorem norm_ringEquiv_mixedSpace (y : InfiniteAdeles F) :
    mixedEmbedding.norm (InfiniteAdeleRing.ringEquiv_mixedSpace F y) =
      ∏ w, ‖y w‖ ^ w.mult := by
  rw [mixedEmbedding.norm_apply]
  simp_rw [normAtPlace_ringEquiv_mixedSpace]

omit [NumberField F] in
theorem unit_smul_ringEquiv_mixedSpace (ε : (𝓞 F)ˣ) (y : InfiniteAdeles F) :
    ε • InfiniteAdeleRing.ringEquiv_mixedSpace F y =
      InfiniteAdeleRing.ringEquiv_mixedSpace F
        (algebraMap F (InfiniteAdeles F) ((ε : 𝓞 F) : F) * y) := by
  rw [unitSMul_smul, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, map_mul]

variable (F)

/-- On the fundamental cone, every archimedean logarithmic norm is bounded by the logarithm
of the total norm plus a constant. -/
theorem exists_log_normAtPlace_bound :
    ∃ D : ℝ, ∀ z ∈ fundamentalCone F, ∀ w : InfinitePlace F,
      |Real.log (normAtPlace w z)| ≤ |Real.log (mixedEmbedding.norm z)| + D := by
  classical
  obtain ⟨D₀, hD₀⟩ := (ZSpan.fundamentalDomain_isBounded
    ((basisUnitLattice F).ofZLatticeBasis ℝ (unitLattice F))).exists_norm_le
  refine ⟨Fintype.card (InfinitePlace F) * |D₀|, fun z hz w => ?_⟩
  set d : ℝ := (finrank ℚ F : ℝ)
  have hd : 1 ≤ d := Nat.one_le_cast.mpr Module.finrank_pos
  have hd0 : d ≠ 0 := by linarith
  set N := mixedEmbedding.norm z
  -- the normalized logarithmic coordinates
  set f : InfinitePlace F → ℝ := fun v =>
    (v.mult : ℝ) * (Real.log (normAtPlace v z) - Real.log N * d⁻¹) with hf
  have hpos : ∀ v, 0 < normAtPlace v z := fun v => fundamentalCone.normAtPlace_pos_of_mem hz v
  have hsum : ∑ v, f v = 0 := by
    have hN : Real.log N = ∑ v, (v.mult : ℝ) * Real.log (normAtPlace v z) := by
      rw [show N = ∏ v, normAtPlace v z ^ v.mult from mixedEmbedding.norm_apply z,
        Real.log_prod (fun v _ => pow_ne_zero _ (hpos v).ne')]
      simp_rw [Real.log_pow]
    have hm : ∑ v : InfinitePlace F, (v.mult : ℝ) = d := by
      rw [← Nat.cast_sum, InfinitePlace.sum_mult_eq]
    simp only [hf, mul_sub, Finset.sum_sub_distrib]
    rw [← hN, ← Finset.sum_mul, hm, mul_left_comm, mul_inv_cancel₀ hd0, mul_one, sub_self]
  have hle : ∀ v, v ≠ w₀ → |f v| ≤ |D₀| := by
    intro v hv
    have h1 : logMap z ⟨v, hv⟩ = f v := logMap_apply z ⟨v, hv⟩
    rw [← h1]
    exact ((norm_le_pi_norm (logMap z) ⟨v, hv⟩).trans (hD₀ _ hz.1)).trans (le_abs_self _)
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace F) := by
    exact_mod_cast Fintype.card_pos
  have hfw : |f w| ≤ Fintype.card (InfinitePlace F) * |D₀| := by
    by_cases hw : w = w₀
    · subst hw
      have h0 : f w₀ = -∑ v ∈ Finset.univ.erase w₀, f v := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w₀)] at hsum
        linarith
      rw [h0, abs_neg]
      calc |∑ v ∈ Finset.univ.erase w₀, f v| ≤ ∑ v ∈ Finset.univ.erase w₀, |f v| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ v ∈ Finset.univ.erase w₀, |D₀| :=
            Finset.sum_le_sum fun v hv => hle v (Finset.ne_of_mem_erase hv)
        _ ≤ ∑ _v : InfinitePlace F, |D₀| :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              fun _ _ _ => abs_nonneg _
        _ = Fintype.card (InfinitePlace F) * |D₀| := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    · exact (hle w hw).trans (le_mul_of_one_le_left (abs_nonneg _) hcard)
  have hmult : |Real.log (normAtPlace w z) - Real.log N * d⁻¹| ≤ |f w| := by
    have hm0 : (0 : ℝ) < (w.mult : ℝ) := by exact_mod_cast InfinitePlace.mult_pos
    show _ ≤ |(w.mult : ℝ) * (Real.log (normAtPlace w z) - Real.log N * d⁻¹)|
    rw [abs_mul, abs_of_pos hm0]
    exact le_mul_of_one_le_left (abs_nonneg _) InfinitePlace.one_le_mult
  have hNd : |Real.log N * d⁻¹| ≤ |Real.log N| := by
    rw [abs_mul, abs_inv, abs_of_pos (by linarith : (0 : ℝ) < d)]
    exact mul_le_of_le_one_right (abs_nonneg _) (inv_le_one_of_one_le₀ hd)
  calc |Real.log (normAtPlace w z)|
      = |(Real.log (normAtPlace w z) - Real.log N * d⁻¹) + Real.log N * d⁻¹| := by ring_nf
    _ ≤ |Real.log (normAtPlace w z) - Real.log N * d⁻¹| + |Real.log N * d⁻¹| := abs_add_le _ _
    _ ≤ Fintype.card (InfinitePlace F) * |D₀| + |Real.log N| := add_le_add (hmult.trans hfw) hNd
    _ = |Real.log N| + Fintype.card (InfinitePlace F) * |D₀| := add_comm _ _

end Archimedean

section Integral

variable {F}

theorem norm_finite_eq_one_of_mem_integralIdeles {y : Ideles F} (hy : y ∈ integralIdeles F)
    (v : FinitePlace F) : ‖(y : Adeles F).2 v‖ = 1 :=
  (Valued.toNormedField.norm_eq_one_iff (Γ₀ := WithZero (Multiplicative ℤ))
    (x := (y : Adeles F).2 v)).mpr (hy v)

theorem full_eq_of_mem_integralIdeles {y : Ideles F} (hy : y ∈ integralIdeles F) :
    ((IdeleAbsoluteValue.full F y : ℝ≥0) : ℝ) = ∏ w, ‖(y : Adeles F).1 w‖ ^ w.mult := by
  rw [IdeleAbsoluteValue.coe_full]
  simp only [norm_finite_eq_one_of_mem_integralIdeles hy, finprod_one, mul_one]

theorem finite_mem_integralFiniteAdeles {y : Ideles F} (hy : y ∈ integralIdeles F) :
    (y : Adeles F).2 ∈ integralFiniteAdeles F := by
  rw [mem_integralFiniteAdeles]
  intro v
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (hy v).le

theorem inv_infinite_apply (y : Ideles F) (w : InfinitePlace F) :
    ((y⁻¹ : Ideles F) : Adeles F).1 w = ((y : Adeles F).1 w)⁻¹ := by
  have h := congrArg (fun a : Adeles F => a.1 w) (Units.inv_mul y)
  exact eq_inv_of_mul_eq_one_left h

end Integral

section Decomposition

/-- The quotient map from ideles to the finite group `C_F / C∞`. -/
def toIntegralQuotient : Ideles F →* IntegralIdeleClassQuotient F :=
  (QuotientGroup.mk' (integralIdeleClasses F)).comp (QuotientGroup.mk' (principalIdeles F))

theorem toIntegralQuotient_surjective : Function.Surjective (toIntegralQuotient F) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

/-- A chosen idele representing each class of `C_F / C∞`. -/
def representative (q : IntegralIdeleClassQuotient F) : Ideles F :=
  Function.surjInv (toIntegralQuotient_surjective F) q

theorem toIntegralQuotient_representative (q : IntegralIdeleClassQuotient F) :
    toIntegralQuotient F (representative F q) = q :=
  Function.surjInv_eq (toIntegralQuotient_surjective F) q

variable {F}

/-- Every idele is an integral idele times a principal idele times the chosen representative
of its class in `C_F / C∞`. -/
theorem exists_integral_mul_principal (x : Ideles F) :
    ∃ (u : Ideles F) (a : Fˣ), u ∈ integralIdeles F ∧
      x = u * diagonalUnits F a * representative F (toIntegralQuotient F x) := by
  set r := representative F (toIntegralQuotient F x)
  have hr : toIntegralQuotient F (x * r⁻¹) = 1 := by
    rw [map_mul, map_inv, toIntegralQuotient_representative, mul_inv_cancel]
  have hmem : (QuotientGroup.mk (x * r⁻¹) : IdeleClasses F) ∈ integralIdeleClasses F :=
    (QuotientGroup.eq_one_iff _).mp hr
  obtain ⟨u, hu, hux⟩ := (mem_integralIdeleClasses_iff _).mp hmem
  have hprin : u⁻¹ * (x * r⁻¹) ∈ principalIdeles F := QuotientGroup.eq.mp hux
  obtain ⟨a, ha⟩ := hprin
  refine ⟨u, a, hu, ?_⟩
  change diagonalUnits F a = u⁻¹ * (x * r⁻¹) at ha
  rw [ha]
  group

end Decomposition

section FundamentalSet

/-- There is a compact set of norm-one ideles meeting every principal coset of `I¹`. -/
theorem exists_isCompact_fundamentalSet :
    ∃ C : Set (Ideles F), IsCompact C ∧ C ⊆ normOneIdeles F ∧
      ∀ x ∈ normOneIdeles F, ∃ a : Fˣ, diagonalUnits F a * x ∈ C := by
  classical
  have : Finite (IntegralIdeleClassQuotient F) := integralIdeleClassQuotientFinite F
  obtain ⟨D, hD⟩ := exists_log_normAtPlace_bound F
  let R : IntegralIdeleClassQuotient F → ℝ := fun q =>
    Real.exp (|Real.log ((IdeleAbsoluteValue.full F (representative F q) : ℝ≥0) : ℝ)| + D)
  have hclosed : IsClosed (normOneIdeles F : Set (Ideles F)) :=
    isClosed_singleton.preimage (IdeleAbsoluteValue.full F).continuous
  refine ⟨(⋃ q, (fun y => y * representative F q) '' ideleBox F (R q)) ∩ normOneIdeles F,
    (isCompact_iUnion fun q => (isCompact_ideleBox F (R q)).image
      (continuous_id.mul continuous_const)).inter_right hclosed, Set.inter_subset_right, ?_⟩
  intro x hx
  obtain ⟨u, a, hu, hxu⟩ := exists_integral_mul_principal x
  set q := toIntegralQuotient F x
  set r := representative F q
  -- the archimedean part of `u` in the mixed space
  set z := InfiniteAdeleRing.ringEquiv_mixedSpace F (u : Adeles F).1
  have hz : mixedEmbedding.norm z ≠ 0 := by
    rw [norm_ringEquiv_mixedSpace]
    refine Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (norm_ne_zero_iff.mpr ?_)
    intro h0
    have h : ((u : Adeles F) * ((u⁻¹ : Ideles F) : Adeles F)).1 w = (1 : Adeles F).1 w :=
      congrArg (fun b : Adeles F => b.1 w) (Units.mul_inv u)
    rw [show ((u : Adeles F) * ((u⁻¹ : Ideles F) : Adeles F)).1 w =
      (u : Adeles F).1 w * ((u⁻¹ : Ideles F) : Adeles F).1 w from rfl, h0, zero_mul] at h
    exact zero_ne_one h
  obtain ⟨ε, hε⟩ := fundamentalCone.exists_unit_smul_mem hz
  set e : Fˣ := Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) ε
  set u' := diagonalUnits F e * u
  have hu' : u' ∈ integralIdeles F := by
    refine (integralIdeles F).mul_mem ?_ hu
    exact (ringIntegerUnitsToIntegralIdeles F ε).2
  have hεz : ε • z = InfiniteAdeleRing.ringEquiv_mixedSpace F (u' : Adeles F).1 := by
    rw [unit_smul_ringEquiv_mixedSpace]
    rfl
  -- the class relation
  have hxe : diagonalUnits F (e * a⁻¹) * x = u' * r := by
    rw [hxu, map_mul, map_inv]
    simp only [u']
    rw [mul_comm u (diagonalUnits F a)]
    group
  have hfull : IdeleAbsoluteValue.full F u' * IdeleAbsoluteValue.full F r = 1 := by
    rw [← map_mul, ← hxe, map_mul, IdeleAbsoluteValue.full_diagonalUnits, one_mul]
    exact hx
  have hlogN : |Real.log (mixedEmbedding.norm (ε • z))| =
      |Real.log ((IdeleAbsoluteValue.full F r : ℝ≥0) : ℝ)| := by
    rw [hεz, norm_ringEquiv_mixedSpace, ← full_eq_of_mem_integralIdeles hu']
    have h1 : ((IdeleAbsoluteValue.full F u' : ℝ≥0) : ℝ) =
        ((IdeleAbsoluteValue.full F r : ℝ≥0) : ℝ)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← NNReal.coe_mul, ← Units.val_mul, hfull, Units.val_one, NNReal.coe_one]
    rw [h1, Real.log_inv, abs_neg]
  have hbound : ∀ w, |Real.log ‖(u' : Adeles F).1 w‖| ≤ Real.log (R q) := by
    intro w
    rw [Real.log_exp, ← hlogN, ← normAtPlace_ringEquiv_mixedSpace, ← hεz]
    exact hD _ hε w
  have hpos : ∀ w, 0 < ‖(u' : Adeles F).1 w‖ := by
    intro w
    rw [← normAtPlace_ringEquiv_mixedSpace, ← hεz]
    exact fundamentalCone.normAtPlace_pos_of_mem hε w
  refine ⟨e * a⁻¹, ?_, ?_⟩
  · rw [hxe]
    refine Set.mem_iUnion.mpr ⟨q, u', ⟨⟨fun w => ?_, finite_mem_integralFiniteAdeles hu'⟩,
      ⟨fun w => ?_, finite_mem_integralFiniteAdeles ((integralIdeles F).inv_mem hu')⟩⟩, rfl⟩
    · rw [← Real.exp_log (hpos w)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans ((hbound w).trans (Real.log_exp _).le))
    · rw [inv_infinite_apply, norm_inv, ← Real.exp_log (hpos w), ← Real.exp_neg]
      exact Real.exp_le_exp.mpr ((neg_le_abs _).trans ((hbound w).trans (Real.log_exp _).le))
  · change IdeleAbsoluteValue.full F (diagonalUnits F (e * a⁻¹) * x) = 1
    rw [map_mul, IdeleAbsoluteValue.full_diagonalUnits, one_mul]
    exact hx

/-- The fundamental set gives compactness of `I¹ / F^×`. -/
theorem compactSpace_normOneIdeleClasses : CompactSpace (NormOneIdeleClasses F) := by
  obtain ⟨C, hC, hCsub, hcover⟩ := exists_isCompact_fundamentalSet F
  have hind : Topology.IsInducing ((↑) : normOneIdeles F → Ideles F) :=
    Topology.IsInducing.subtypeVal
  have hC' : IsCompact (((↑) : normOneIdeles F → Ideles F) ⁻¹' C) :=
    (hind.isCompact_preimage_iff (fun y hy => ⟨⟨y, hCsub hy⟩, rfl⟩)).mpr hC
  refine ⟨?_⟩
  have himage := hC'.image (QuotientGroup.continuous_mk (N := normOnePrincipal F))
  convert himage using 1
  refine (Set.eq_univ_of_forall fun c => ?_).symm
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨a, ha⟩ := hcover x x.2
  refine ⟨⟨diagonalUnits F a * x, (normOneIdeles F).mul_mem ?_ x.2⟩, ha, ?_⟩
  · change IdeleAbsoluteValue.full F (diagonalUnits F a) = 1
    exact IdeleAbsoluteValue.full_diagonalUnits F a
  · refine (QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr (MonoidHom.mem_range.mpr
      ⟨a, ?_⟩))).symm
    change diagonalUnits F a = (x : Ideles F)⁻¹ * (diagonalUnits F a * x)
    rw [← mul_assoc, inv_mul_cancel_comm]

/-- Proof of the statement for every number field. -/
theorem normOneIdeleClassCompact : NormOneIdeleClassCompactStatement.{u} := by
  intro F _ _
  exact compactSpace_normOneIdeleClasses F

/-- The kernel of the normalized absolute value on the actual idele class group is compact. -/
theorem isCompact_ker_ideleClass :
    IsCompact ((IdeleAbsoluteValue.ideleClass F).toMonoidHom.ker : Set (IdeleClasses F)) := by
  obtain ⟨C, hC, hCsub, hcover⟩ := exists_isCompact_fundamentalSet F
  convert hC.image (map_continuous (ideleClassMap F)) using 1
  ext c
  constructor
  · intro hc
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    have hx : x ∈ normOneIdeles F := hc
    obtain ⟨a, ha⟩ := hcover x hx
    refine ⟨diagonalUnits F a * x, ha, ?_⟩
    rw [map_mul, ideleClassMap_diagonalUnits]
    exact one_mul (ideleClassMap F x)
  · rintro ⟨y, hy, rfl⟩
    exact hCsub hy

end FundamentalSet

end Langlands.Global.NormOneIdeleClass
