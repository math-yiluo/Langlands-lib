import Langlands.Representation.Hecke.NormalQuotientModels
import Langlands.Representation.Hecke.CompactTensorGroupBalance

/-! # Balancing identities for the Hecke bimodule of a quotient map

Renard III.2.10, (III.2.10.1), printed pp.80–82 / PDF pp.86–88.
-/

noncomputable section

open MeasureTheory MulOpposite

namespace Langlands.Hecke.Homomorphism

open HarmonicAnalysis Langlands.Algebra

universe uG uH uV

section General

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [T2Space G] [LocallyCompactSpace G] in
/-- A normalized compact-open indicator has total mass one. -/
theorem integral_normalizedIndicator (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    (∫ x, HeckeAlgebra.normalizedIndicator μ K hK x ∂μ) = 1 := by
  change (∫ x, (μ.real (K : Set G) : ℂ)⁻¹ *
    (K : Set G).indicator (fun _ => (1 : ℂ)) x ∂μ) = 1
  rw [integral_const_mul, integral_indicator_const 1 K.isOpen.measurableSet]
  simpa only [Complex.real_smul, smul_eq_mul, mul_one] using
    inv_mul_cancel₀ (HeckeAlgebra.compactOpen_complex_mass_ne_zero μ K hK)

/-- The normalized indicator action is right invariant under its subgroup,
for an arbitrary (not necessarily unimodular) Haar measure. -/
theorem heckeAction_normalizedIndicator_translate (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    {k : G} (hk : k ∈ K) (v : V) :
    heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK) (ρ k v) =
      heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK) v := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro L
  rw [map_sub, sub_eq_zero]
  let e := HeckeAlgebra.normalizedIndicator μ K hK
  change L (integratedAction μ ρ hρ (HeckeAlgebra.toTestFunction μ e) (ρ k v)) =
    L (integratedAction μ ρ hρ (HeckeAlgebra.toTestFunction μ e) v)
  rw [integratedAction_dual, integratedAction_dual]
  let f : SchwartzBruhat G :=
    ⟨fun x => e x * L (ρ x v),
      e.locallyConstant.mul ((orbitMap_locallyConstant ρ (hρ v)).comp L),
      e.hasCompactSupport.mul_right⟩
  have hk1 : haarScale k = 1 := by
    simp [haarScale, Haar.modularCharacter_eq_one_of_mem_compactOpen K hK hk]
  calc
    (∫ x, (HeckeAlgebra.toTestFunction μ e) x * L (ρ x (ρ k v)) ∂μ) =
        ∫ x, f (x * k) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      change e x * L (ρ x (ρ k v)) = e (x * k) * L (ρ (x * k) v)
      rw [map_mul, Module.End.mul_apply,
        (HeckeAlgebra.normalizedIndicator_mem_biInvariant μ K hK).2 ⟨k, hk⟩ x]
    _ = ∫ x, f x ∂μ := by rw [integral_mul_right_test, hk1, one_mul]
    _ = _ := rfl

end General

section Comparison

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] [T2Space H]
  [NonarchimedeanGroup H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  (μG : Measure G) [μG.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]
  (φ : H →* G) (hφ : Continuous φ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [T2Space H] [LocallyCompactSpace H] in
/-- If `φ` maps the compact open subgroup `K` onto `KG`, the normalized indicator
of `K`, acting through `φ`, is the normalized indicator of `KG`. -/
theorem heckeAction_comp_normalizedIndicator (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup H) (hK : IsCompact (K : Set H))
    (KG : OpenSubgroup G) (hKG : IsCompact (KG : Set G))
    (hle : ∀ k ∈ K, φ k ∈ KG) (hmap : ∀ m ∈ KG, ∃ k ∈ K, φ k = m) (v : V) :
    heckeAction μH (ρ.comp φ) (isSmooth_comp φ hφ hρ)
        (HeckeAlgebra.normalizedIndicator μH K hK) v =
      heckeAction μG ρ hρ (HeckeAlgebra.normalizedIndicator μG KG hKG) v := by
  set A := heckeAction μH (ρ.comp φ) (isSmooth_comp φ hφ hρ)
    (HeckeAlgebra.normalizedIndicator μH K hK)
  set B := heckeAction μG ρ hρ (HeckeAlgebra.normalizedIndicator μG KG hKG)
  have h1 : B (A v) = A v := by
    apply heckeAction_normalizedIndicator_of_fixed
    intro m
    obtain ⟨k, hk, hkm⟩ := hmap m m.property
    have hfix := heckeAction_normalizedIndicator_mem μH (ρ.comp φ)
      (isSmooth_comp φ hφ hρ) K hK v ⟨k, hk⟩
    change ρ (φ k) (A v) = A v at hfix
    change ρ m (A v) = A v
    rw [← hkm]
    exact hfix
  have h2 : B (A v) = B v := by
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
    intro L
    rw [map_sub, sub_eq_zero]
    let e := HeckeAlgebra.normalizedIndicator μH K hK
    change (L ∘ₗ B) (integratedAction μH (ρ.comp φ) (isSmooth_comp φ hφ hρ)
      (HeckeAlgebra.toTestFunction μH e) v) = L (B v)
    rw [integratedAction_dual]
    calc
      (∫ k, (HeckeAlgebra.toTestFunction μH e) k * (L ∘ₗ B) ((ρ.comp φ) k v) ∂μH) =
          ∫ k, e k * L (B v) ∂μH := by
        apply integral_congr_ae
        filter_upwards [] with k
        change e k * L (B (ρ (φ k) v)) = e k * L (B v)
        by_cases hk : k ∈ K
        · rw [heckeAction_normalizedIndicator_translate μG ρ hρ KG hKG (hle k hk)]
        · simp [e, HeckeAlgebra.normalizedIndicator_apply, hk]
      _ = L (B v) := by
        rw [integral_mul_const, integral_normalizedIndicator, one_mul]
  rw [← h1, h2]

/-- The left Hecke regular action is convolution. -/
theorem heckeAction_leftTests_eq_mul (a T : HeckeAlgebra μG) :
    heckeAction μG (GroupAction.leftTests (G := G)) isSmooth_leftTests a T = a * T := by
  ext x
  exact leftModule_apply μG μG (MonoidHom.id G) continuous_id a T x

/-- Right translation of the first convolution factor is left translation of
the second, with the modular factor of `rightRepresentation`. -/
theorem rightRepresentation_mul (h : H) (S b : HeckeAlgebra μG) :
    rightRepresentation μG φ h⁻¹ S * b =
      S * (show HeckeAlgebra μG from GroupAction.leftTests (φ h) b) := by
  ext x
  set m := φ h
  let F : SchwartzBruhat G :=
    ⟨fun y => S y * b (m⁻¹ * (y⁻¹ * x)),
      S.locallyConstant.mul (b.locallyConstant.comp_continuous
        (continuous_const.mul (continuous_inv.mul continuous_const))),
      S.hasCompactSupport.mul_right⟩
  have hF := integral_mul_right_test μG F m⁻¹
  change (∫ y, F (y * m⁻¹) ∂μG) = haarScale m⁻¹ * ∫ y, F y ∂μG at hF
  rw [HeckeAlgebra.mul_apply, HeckeAlgebra.mul_apply]
  have hl : (∫ y, rightRepresentation μG φ h⁻¹ S y * b (y⁻¹ * x) ∂μG) =
      haarScale m * ∫ y, F (y * m⁻¹) ∂μG := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [rightRepresentation_apply]
    change haarScale (φ h⁻¹)⁻¹ * S (y * φ h⁻¹) * b (y⁻¹ * x) =
      haarScale m * (S (y * m⁻¹) * b (m⁻¹ * ((y * m⁻¹)⁻¹ * x)))
    simp only [m, map_inv, inv_inv, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  rw [hl, hF, ← mul_assoc, haarScale_mul_inverse, one_mul]
  rfl

/-- The specified right action, followed by any integrated action, is the
integrated action of the pulled-back representation. This is the source's
identity `T * a = T * φ_*(a)`, in integrated form. -/
theorem heckeAction_rightModule (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (a : HeckeAlgebra μH) (T : HeckeAlgebra μG) (v : V) :
    heckeAction μG ρ hρ (letI := rightModule μG μH φ hφ; op a • T) v =
      heckeAction μG ρ hρ T (heckeAction μH (ρ.comp φ) (isSmooth_comp φ hφ hρ) a v) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro L
  rw [map_sub, sub_eq_zero]
  set B := heckeAction μG ρ hρ T
  have hB (u : V) : L (B u) = ∫ y, T y * L (ρ y u) ∂μG :=
    integratedAction_dual μG ρ hρ (HeckeAlgebra.toTestFunction μG T) u L
  change L (integratedAction μG ρ hρ (HeckeAlgebra.toTestFunction μG
      (letI := rightModule μG μH φ hφ; op a • T)) v) =
    (L ∘ₗ B) (integratedAction μH (ρ.comp φ) (isSmooth_comp φ hφ hρ)
      (HeckeAlgebra.toTestFunction μH a) v)
  rw [integratedAction_dual, integratedAction_dual]
  have hinner (h : H) :
      (∫ x, haarScale (φ h) * a h * T (x * (φ h)⁻¹) * L (ρ x v) ∂μG) =
        a h * (L ∘ₗ B) ((ρ.comp φ) h v) := by
    set g := φ h
    let F : SchwartzBruhat G :=
      ⟨fun y => T y * L (ρ (y * g) v),
        T.locallyConstant.mul (((orbitMap_locallyConstant ρ (hρ v)).comp L).comp_continuous
          (continuous_id.mul continuous_const)),
        T.hasCompactSupport.mul_right⟩
    have hF := integral_mul_right_test μG F g⁻¹
    change (∫ y, F (y * g⁻¹) ∂μG) = haarScale g⁻¹ * ∫ y, F y ∂μG at hF
    have hrhs : (L ∘ₗ B) ((ρ.comp φ) h v) = ∫ y, F y ∂μG := by
      change L (B (ρ g v)) = _
      rw [hB]
      apply integral_congr_ae
      filter_upwards [] with y
      change T y * L (ρ y (ρ g v)) = T y * L (ρ (y * g) v)
      rw [map_mul, Module.End.mul_apply]
    have hl : (∫ x, haarScale g * a h * T (x * g⁻¹) * L (ρ x v) ∂μG) =
        haarScale g * a h * ∫ y, F (y * g⁻¹) ∂μG := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      change haarScale g * a h * T (x * g⁻¹) * L (ρ x v) =
        haarScale g * a h * (T (x * g⁻¹) * L (ρ (x * g⁻¹ * g) v))
      rw [inv_mul_cancel_right]
      ring
    rw [hl, hF, hrhs]
    have hg := haarScale_mul_inverse g
    calc
      haarScale g * a h * (haarScale g⁻¹ * ∫ y, F y ∂μG) =
          (haarScale g * haarScale g⁻¹) * (a h * ∫ y, F y ∂μG) := by ring
      _ = _ := by rw [hg, one_mul]
  calc
    (∫ x, (HeckeAlgebra.toTestFunction μG
        (letI := rightModule μG μH φ hφ; op a • T)) x * L (ρ x v) ∂μG) =
        ∫ x, ∫ h, haarScale (φ h) * a h * T (x * (φ h)⁻¹) * L (ρ x v) ∂μH ∂μG := by
      apply integral_congr_ae
      filter_upwards [] with x
      change (letI := rightModule μG μH φ hφ; (op a • T) x) * L (ρ x v) = _
      rw [rightModule_integral, ← integral_mul_const]
    _ = ∫ h, ∫ x, haarScale (φ h) * a h * T (x * (φ h)⁻¹) * L (ρ x v) ∂μG ∂μH := by
      apply integral_integral_swap_of_hasCompactSupport
      · exact ((((haarScale_locallyConstant.comp_continuous hφ).continuous.comp
          continuous_snd).mul (a.continuous.comp continuous_snd)).mul
          (T.continuous.comp (continuous_fst.mul (hφ.comp continuous_snd).inv))).mul
          (((orbitMap_locallyConstant ρ (hρ v)).comp L).continuous.comp continuous_fst)
      · apply HasCompactSupport.of_support_subset_isCompact
          (((TestFunction.isCompact_support (HeckeAlgebra.toTestFunction μG T)).prod
            (TestFunction.isCompact_support (HeckeAlgebra.toTestFunction μH a))).image
            ((continuous_fst.mul (hφ.comp continuous_snd)).prodMk continuous_snd))
        rintro ⟨x, h⟩ hp
        change haarScale (φ h) * a h * T (x * (φ h)⁻¹) * L (ρ x v) ≠ 0 at hp
        have h1 := (mul_ne_zero_iff.mp hp).1
        have h2 := mul_ne_zero_iff.mp h1
        have h3 := (mul_ne_zero_iff.mp h2.1).2
        refine ⟨(x * (φ h)⁻¹, h), ⟨h2.2, h3⟩, ?_⟩
        simp
    _ = ∫ h, (HeckeAlgebra.toTestFunction μH a) h * (L ∘ₗ B) ((ρ.comp φ) h v) ∂μH := by
      apply integral_congr_ae
      filter_upwards [] with h
      exact hinner h

end Comparison

section Quotient

variable {P : Type uH} [Group P] [TopologicalSpace P] [T2Space P]
  [NonarchimedeanGroup P] [LocallyCompactSpace P] [MeasurableSpace P] [BorelSpace P]
  (N : Subgroup P) [N.Normal] [IsClosed (N : Set P)]
  [MeasurableSpace (P ⧸ N)] [BorelSpace (P ⧸ N)]
  (μP : Measure P) [μP.IsHaarMeasure]
  (μM : Measure (P ⧸ N)) [μM.IsHaarMeasure]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [T2Space P] [NonarchimedeanGroup P] [LocallyCompactSpace P] [MeasurableSpace P]
  [BorelSpace P] [IsClosed (N : Set P)] [MeasurableSpace (P ⧸ N)] [BorelSpace (P ⧸ N)] in
/-- The quotient map, as a continuous homomorphism. -/
theorem continuous_quotientMk' : Continuous (QuotientGroup.mk' N) :=
  QuotientGroup.continuous_mk

omit [T2Space P] in
/-- The normalized indicator of `K`, acting through the quotient map, is the
normalized indicator of `KM = q(K)`. -/
theorem heckeAction_quotient_normalizedIndicator (ρ : Representation ℂ (P ⧸ N) V)
    (hρ : IsSmooth ρ) (K : OpenSubgroup P) (hK : IsCompact (K : Set P)) (v : V) :
    heckeAction μP (ρ.comp (QuotientGroup.mk' N))
        (isSmooth_comp _ (continuous_quotientMk' N) hρ)
        (HeckeAlgebra.normalizedIndicator μP K hK) v =
      heckeAction μM ρ hρ (HeckeAlgebra.normalizedIndicator μM (quotientOpenSubgroup N K)
        (isCompact_quotientOpenSubgroup N K hK)) v :=
  heckeAction_comp_normalizedIndicator μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
    ρ hρ K hK _ _ (fun k hk => Subgroup.mem_map_of_mem _ hk)
    (fun m hm => by
      obtain ⟨k, hk, hkm⟩ := Subgroup.mem_map.mp hm
      exact ⟨k, hk, hkm⟩) v

/-- The left `H(P)`-module structure on `H(M)`: `eK` acts as convolution by `eKM`. -/
theorem leftModule_normalizedIndicator (K : OpenSubgroup P) (hK : IsCompact (K : Set P))
    (f : HeckeAlgebra μM) :
    (letI := leftModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
     HeckeAlgebra.normalizedIndicator μP K hK • f) =
      HeckeAlgebra.normalizedIndicator μM (quotientOpenSubgroup N K)
        (isCompact_quotientOpenSubgroup N K hK) * f := by
  change heckeAction μP ((GroupAction.leftTests (G := P ⧸ N)).comp (QuotientGroup.mk' N))
    (isSmooth_comp _ (continuous_quotientMk' N) isSmooth_leftTests)
    (HeckeAlgebra.normalizedIndicator μP K hK) f = _
  exact (heckeAction_quotient_normalizedIndicator N μP μM _ isSmooth_leftTests K hK f).trans
    (heckeAction_leftTests_eq_mul μM _ f)

/-- The right `H(P)`-module structure on `H(M)`: `eK` acts as right convolution
by `eKM`. -/
theorem rightModule_normalizedIndicator (K : OpenSubgroup P) (hK : IsCompact (K : Set P))
    (T : HeckeAlgebra μM) :
    (letI := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
     op (HeckeAlgebra.normalizedIndicator μP K hK) • T) =
      T * HeckeAlgebra.normalizedIndicator μM (quotientOpenSubgroup N K)
        (isCompact_quotientOpenSubgroup N K hK) := by
  rw [rightModule_apply]
  rw [haarInversion_normalizedIndicator, leftModule_normalizedIndicator, haarInversion_mul,
    haarInversion_involution, haarInversion_normalizedIndicator]

/-- Renard (III.2.10.1): `T * a_{p,K} = T * a_{q(p),q(K)}`, where
`a_{p,K} = eK * l(p) eK` is the density of `eK * δp * eK`. -/
theorem rightModule_doubleCoset (K : OpenSubgroup P) (hK : IsCompact (K : Set P)) (p : P)
    (T : HeckeAlgebra μM) :
    (letI := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
     op (HeckeAlgebra.normalizedIndicator μP K hK *
        (show HeckeAlgebra μP from
          GroupAction.leftTests p (HeckeAlgebra.normalizedIndicator μP K hK))) • T) =
      T * (HeckeAlgebra.normalizedIndicator μM (quotientOpenSubgroup N K)
          (isCompact_quotientOpenSubgroup N K hK) *
        (show HeckeAlgebra μM from GroupAction.leftTests (QuotientGroup.mk' N p)
          (HeckeAlgebra.normalizedIndicator μM (quotientOpenSubgroup N K)
            (isCompact_quotientOpenSubgroup N K hK)))) := by
  let _ := rightModule μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N)
  set eP := HeckeAlgebra.normalizedIndicator μP K hK
  set eM := HeckeAlgebra.normalizedIndicator μM (quotientOpenSubgroup N K)
    (isCompact_quotientOpenSubgroup N K hK)
  have hl : (show HeckeAlgebra μP from GroupAction.leftTests p eP) =
      HeckeAlgebra.leftTranslated μP p eP := by
    ext x
    rfl
  rw [op_mul, mul_smul, rightModule_normalizedIndicator, hl,
    rightModule_leftTranslate μM μP (QuotientGroup.mk' N) (continuous_quotientMk' N),
    rightModule_normalizedIndicator,
    rightRepresentation_mul μM (QuotientGroup.mk' N), mul_assoc]

end Quotient

end Langlands.Hecke.Homomorphism
