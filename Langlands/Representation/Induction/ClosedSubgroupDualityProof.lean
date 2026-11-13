import Langlands.Representation.Induction.ClosedSubgroupDualityStatement
import Langlands.HarmonicAnalysis.RenardHomogeneousAveragingProof
import Langlands.Representation.Induction.CompactFixedVectorModel
import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Representation.Smooth.Contragredient.FixedExtension
import Langlands.Representation.Smooth.Contragredient.FixedLevelPairing

/-! # Renard III.2.7: duality for every closed subgroup -/

noncomputable section

open Classical
open scoped Pointwise NNReal

namespace Langlands.Induction

open HarmonicAnalysis.HomogeneousFunctions

namespace ClosedSubgroupDuality

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  (H : Subgroup G) (hH : IsClosed (H : Set G))
  (χ : H →* ℂˣ)
  (hχ : ∀ a : H, (χ a : ℂ) = ((relativeModular H hH a : ℝ) : ℂ))

theorem compact_cofinal (U : OpenSubgroup G) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ U := by
  obtain ⟨K, hKU, hK, -⟩ :=
    Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ U
  exact ⟨K, hK, hKU⟩

theorem relative_eq_one (J : Subgroup H) (hJ : IsCompact (J : Set H))
    (a : H) (ha : a ∈ J) : relativeModular H hH a = 1 := by
  let : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have h₁ := (HarmonicAnalysis.Distribution.RenardModular.regularity G).2.2.2
    (J.map H.subtype) (by
      simpa only [Subgroup.coe_map, Subgroup.coe_subtype] using
        hJ.image (continuous_subtype_val : Continuous (H.subtype : H → G)))
    a.val ⟨a, ha, rfl⟩
  have h₂ := (HarmonicAnalysis.Distribution.RenardModular.regularity H).2.2.2 J hJ a ha
  change HarmonicAnalysis.Distribution.renardModular a.val /
    HarmonicAnalysis.Distribution.renardModular a = 1
  rw [h₁, h₂, div_self one_ne_zero]

include hχ in
theorem character_eq_one (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (x : G) (a : H) (ha : a ∈ conjOpenSubgroup H K x) : (χ a : ℂ) = 1 := by
  rw [hχ, relative_eq_one H hH (conjOpenSubgroup H K x).toSubgroup
    (isCompact_conjOpenSubgroup H hH K hK x) a ha]
  norm_num

def scalarFixed (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) :
    fixedVectors (characterRepresentation χ) (conjOpenSubgroup H K x).toSubgroup :=
  ⟨1, fun a => by
    change (χ a.val : ℂ) * 1 = 1
    rw [character_eq_one H hH χ hχ K hK x a.val a.property, one_mul]⟩

/-- The scalar function equal to the relative character on `H x K`. -/
def basic (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) :
    renardSpace H hH :=
  Renard.ofCompact H hχ
    (compactDoubleCosetSection H (characterRepresentation χ) K hK x
      (scalarFixed H hH χ hχ K hK x).val
      (scalarFixed H hH χ hχ K hK x).property)

theorem basic_apply (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (x : G) (a : H) (k : K) :
    (basic H hH χ hχ K hK x).val (a.val * x * k.val) = (χ a : ℂ) := by
  change eval H (characterRepresentation χ)
    (compactDoubleCosetSection H (characterRepresentation χ) K hK x
      (scalarFixed H hH χ hχ K hK x).val
      (scalarFixed H hH χ hχ K hK x).property).val _ = _
  rw [compactDoubleCosetSection_apply]
  change (χ a : ℂ) * 1 = _
  exact mul_one _

theorem basic_self (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) :
    (basic H hH χ hχ K hK x).val x = 1 := by
  simpa using basic_apply H hH χ hχ K hK x 1 1

theorem basic_zero (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (x y : G) (hy : DoubleCoset.mk H K.toSubgroup y ≠ DoubleCoset.mk H K.toSubgroup x) :
    (basic H hH χ hχ K hK x).val y = 0 :=
  fixedDoubleCosetSection_eval_of_ne H (characterRepresentation χ) K hK x
    (scalarFixed H hH χ hχ K hK x) hy

theorem basic_nonnegative (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (x y : G) :
    ((basic H hH χ hχ K hK x).val y).im = 0 ∧
      0 ≤ ((basic H hH χ hχ K hK x).val y).re := by
  by_cases hy : DoubleCoset.mk H K.toSubgroup y = DoubleCoset.mk H K.toSubgroup x
  · obtain ⟨a, ha, k, hk, rfl⟩ := DoubleCoset.eq.mp hy.symm
    rw [basic_apply H hH χ hχ K hK x ⟨a, ha⟩ ⟨k, hk⟩, hχ]
    exact ⟨Complex.ofReal_im _, (relativeModular H hH ⟨a, ha⟩).coe_nonneg⟩
  · rw [basic_zero H hH χ hχ K hK x y hy]
    exact ⟨rfl, le_rfl⟩

theorem basic_ne_zero (ν : Module.Dual ℂ (renardSpace H hH))
    (hν : ∀ (g : G) (φ : renardSpace H hH),
      ν (rightAction H (relativeModular H hH) g φ) = ν φ)
    (hν0 : ν ≠ 0) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) :
    ν (basic H hH χ hχ K hK x) ≠ 0 := by
  obtain ⟨ν₀, hpos, -, huniq, -⟩ := Renard.invariantFunctional G H hH
  obtain ⟨c, hc, -⟩ := huniq ν hν
  have hc0 : c ≠ 0 := by
    intro hz
    exact hν0 (by simpa [hz] using hc)
  have hb : basic H hH χ hχ K hK x ≠ 0 := by
    intro hz
    have he := congrArg (fun f : renardSpace H hH => f.val x) hz
    rw [basic_self] at he
    exact one_ne_zero he
  have hp := (hpos _ hb (basic_nonnegative H hH χ hχ K hK x)).2
  rw [hc, LinearMap.smul_apply, smul_eq_mul]
  apply mul_ne_zero hc0
  intro hz
  simp [hz] at hp

variable {W : Type uV} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W)

/-- The actual covariant scalar integrand, with its compact-modulo-`H` support. -/
def integrand (h : SmoothFunctions H (smoothContragredient ρ))
    (f : CompactFunctions H (twist χ ρ)) : renardSpace H hH :=
  ⟨⟨fun g => smoothDualPairing ρ (eval H _ h g) (eval H _ f.val g),
      (eval_isLocallyConstant H _ h).comp₂
        (eval_isLocallyConstant H _ f.val) (fun ℓ v => smoothDualPairing ρ ℓ v)⟩, by
    refine ⟨?_, ?_⟩
    · intro a g
      change smoothDualPairing ρ (eval H _ h (a.val * g))
        (eval H _ f.val (a.val * g)) = _
      rw [eval_covariant, eval_covariant]
      change smoothDualPairing ρ (smoothContragredient ρ a (eval H _ h g))
        ((χ a : ℂ) • ρ a (eval H _ f.val g)) = _
      rw [map_smul, smoothDualPairing_invariant, hχ, smul_eq_mul]
      rfl
    · obtain ⟨C, hC, hcover⟩ := Renard.exists_compact_lift H f.property
      refine ⟨C, hC, ?_⟩
      intro g hg
      rw [Renard.mem_mul_iff_quotientMap]
      apply hcover
      refine ⟨g, ?_, rfl⟩
      intro hz
      apply hg
      change smoothDualPairing ρ (eval H _ h g) (eval H _ f.val g) = 0
      rw [hz, map_zero]⟩

theorem integrand_apply (h : SmoothFunctions H (smoothContragredient ρ))
    (f : CompactFunctions H (twist χ ρ)) (g : G) :
    (integrand H hH χ hχ ρ h f).val g =
      smoothDualPairing ρ (eval H _ h g) (eval H _ f.val g) := rfl

/-- Integrating the pointwise pairing against the specified invariant functional. -/
def pairing (ν : Module.Dual ℂ (renardSpace H hH)) :
    SmoothFunctions H (smoothContragredient ρ) →ₗ[ℂ]
      CompactFunctions H (twist χ ρ) →ₗ[ℂ] ℂ where
  toFun h :=
    { toFun f := ν (integrand H hH χ hχ ρ h f)
      map_add' f f' := by
        rw [← map_add]
        congr 1
        apply Subtype.ext
        ext g
        exact map_add (smoothDualPairing ρ (eval H _ h g)) _ _
      map_smul' c f := by
        rw [← map_smul]
        congr 1
        apply Subtype.ext
        ext g
        exact map_smul (smoothDualPairing ρ (eval H _ h g)) c _ }
  map_add' h h' := by
    ext f
    change ν (integrand H hH χ hχ ρ (h + h') f) =
      ν (integrand H hH χ hχ ρ h f) + ν (integrand H hH χ hχ ρ h' f)
    rw [← map_add]
    congr 1
  map_smul' c h := by
    ext f
    change ν (integrand H hH χ hχ ρ (c • h) f) =
      c • ν (integrand H hH χ hχ ρ h f)
    rw [← map_smul]
    congr 1

theorem pairing_invariant (ν : Module.Dual ℂ (renardSpace H hH))
    (hν : ∀ (g : G) (φ : renardSpace H hH),
      ν (rightAction H (relativeModular H hH) g φ) = ν φ)
    (g : G) (h : SmoothFunctions H (smoothContragredient ρ))
    (f : CompactFunctions H (twist χ ρ)) :
    pairing H hH χ hχ ρ ν (smoothInduced H _ g h) (compactInduced H _ g f) =
      pairing H hH χ hχ ρ ν h f :=
  hν g (integrand H hH χ hχ ρ h f)

/-- Twisting does not change the fixed coefficients at a compact stabilizer. -/
def fixedTwistEquiv (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) :
    fixedVectors (twist χ ρ) (conjOpenSubgroup H K x).toSubgroup ≃ₗ[ℂ]
      fixedVectors ρ (conjOpenSubgroup H K x).toSubgroup where
  toFun v := ⟨v.val, fun a => by
    have hv := v.property a
    change (χ a.val : ℂ) • ρ a.val v.val = v.val at hv
    rwa [character_eq_one H hH χ hχ K hK x a.val a.property, one_smul] at hv⟩
  invFun v := ⟨v.val, fun a => by
    change (χ a.val : ℂ) • ρ a.val v.val = v.val
    rw [character_eq_one H hH χ hχ K hK x a.val a.property, one_smul]
    exact v.property a⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- On a compact double-coset section the integrand is a scalar basic function. -/
theorem integrand_section (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (h : fixedVectors (smoothInduced H (smoothContragredient ρ)) K.toSubgroup)
    (x : G) (v : fixedVectors (twist χ ρ) (conjOpenSubgroup H K x).toSubgroup) :
    integrand H hH χ hχ ρ h.val
        (compactDoubleCosetSection H (twist χ ρ) K hK x v.val v.property) =
      (smoothDualPairing ρ (eval H _ h.val x) v.val) • basic H hH χ hχ K hK x := by
  apply Subtype.ext
  ext y
  change smoothDualPairing ρ (eval H _ h.val y)
      (eval H _ (compactDoubleCosetSection H (twist χ ρ) K hK x v.val v.property).val y) =
    smoothDualPairing ρ (eval H _ h.val x) v.val * (basic H hH χ hχ K hK x).val y
  by_cases hy : DoubleCoset.mk H K.toSubgroup y = DoubleCoset.mk H K.toSubgroup x
  · obtain ⟨a, ha, k, hk, rfl⟩ := DoubleCoset.eq.mp hy.symm
    rw [compactDoubleCosetSection_apply H (twist χ ρ) K hK x v.val v.property
      ⟨a, ha⟩ ⟨k, hk⟩,
      eval_mul_of_mem_fixedVectors H (smoothContragredient ρ) K.toSubgroup h.property
        ⟨k, hk⟩ (a * x),
      eval_covariant H (smoothContragredient ρ) h.val ⟨a, ha⟩ x,
      basic_apply H hH χ hχ K hK x ⟨a, ha⟩ ⟨k, hk⟩]
    change smoothDualPairing ρ (smoothContragredient ρ ⟨a, ha⟩ (eval H _ h.val x))
      ((χ ⟨a, ha⟩ : ℂ) • ρ ⟨a, ha⟩ v.val) = _
    rw [map_smul, smoothDualPairing_invariant, smul_eq_mul, mul_comm]
  · have hz := fixedDoubleCosetSection_eval_of_ne H (twist χ ρ) K hK x v hy
    change eval H (twist χ ρ)
      (compactDoubleCosetSection H (twist χ ρ) K hK x v.val v.property).val y = 0 at hz
    rw [hz, map_zero, basic_zero H hH χ hχ K hK x y hy, mul_zero]

theorem pairing_section (ν : Module.Dual ℂ (renardSpace H hH))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (h : fixedVectors (smoothInduced H (smoothContragredient ρ)) K.toSubgroup)
    (x : G) (v : fixedVectors (twist χ ρ) (conjOpenSubgroup H K x).toSubgroup) :
    pairing H hH χ hχ ρ ν h.val
        (compactDoubleCosetSection H (twist χ ρ) K hK x v.val v.property) =
      smoothDualPairing ρ (eval H _ h.val x) v.val * ν (basic H hH χ hχ K hK x) := by
  change ν (integrand H hH χ hχ ρ h.val _) = _
  rw [integrand_section, map_smul, smul_eq_mul]

/-- The integrated pairing detects every nonzero smooth induced function. -/
theorem pairing_left (ν : Module.Dual ℂ (renardSpace H hH))
    (hν : ∀ (g : G) (φ : renardSpace H hH),
      ν (rightAction H (relativeModular H hH) g φ) = ν φ)
    (hν0 : ν ≠ 0) (hρ : IsSmooth ρ)
    (h : SmoothFunctions H (smoothContragredient ρ))
    (hz : ∀ f, pairing H hH χ hχ ρ ν h f = 0) : h = 0 := by
  obtain ⟨U, hU⟩ := smoothInduced_smooth H (smoothContragredient ρ) h
  obtain ⟨K, hK, hKU⟩ := compact_cofinal U
  have hh : h ∈ fixedVectors (smoothInduced H (smoothContragredient ρ)) K.toSubgroup :=
    fun k => hU ⟨k.val, hKU k.property⟩
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change eval H (smoothContragredient ρ) h x = 0
  have he : (⟨eval H (smoothContragredient ρ) h x,
      eval_mem_fixedVectors H (smoothContragredient ρ) K x hh⟩ :
      fixedVectors (smoothContragredient ρ) (conjOpenSubgroup H K x).toSubgroup) = 0 := by
    apply (smoothDualFixedRestriction_bijective ρ hρ (conjOpenSubgroup H K x)
      (isCompact_conjOpenSubgroup H hH K hK x)).1
    ext v
    change smoothDualPairing ρ (eval H (smoothContragredient ρ) h x) v.val = 0
    let w := (fixedTwistEquiv H hH χ hχ ρ K hK x).symm v
    have hp := hz (compactDoubleCosetSection H (twist χ ρ) K hK x w.val w.property)
    rw [pairing_section H hH χ hχ ρ ν K hK ⟨h, hh⟩ x w] at hp
    exact (mul_eq_zero.mp hp).resolve_right (basic_ne_zero H hH χ hχ ν hν hν0 K hK x)
  exact congrArg Subtype.val he

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
/-- Arbitrary fixed dual coefficients assemble without a finiteness condition. -/
theorem assemble (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (v : (q : DoubleCoset.Quotient (H : Set G) (K.toSubgroup : Set G)) →
      fixedVectors (smoothContragredient ρ) (conjOpenSubgroup H K q.out).toSubgroup) :
    ∃ h : fixedVectors (smoothInduced H (smoothContragredient ρ)) K.toSubgroup,
      ∀ q, eval H (smoothContragredient ρ) h.val q.out = (v q).val := by
  let sectionAt (q : DoubleCoset.Quotient (H : Set G) (K.toSubgroup : Set G)) :=
    fixedDoubleCosetSection H (smoothContragredient ρ) K hK q.out (v q)
  let F (x : G) := eval H (smoothContragredient ρ)
    (sectionAt (DoubleCoset.mk H K.toSubgroup x)).val x
  have hcov : ∀ (a : H) (x : G),
      F (a.val * x) = smoothContragredient ρ a (F x) := by
    intro a x
    change eval H (smoothContragredient ρ)
      (sectionAt (DoubleCoset.mk H K.toSubgroup (a.val * x))).val (a.val * x) = _
    rw [DoubleCoset.mk_mem_mul]
    exact eval_covariant H (smoothContragredient ρ) _ a x
  have hright : ∀ (k : K) (x : G), F (x * k.val) = F x := by
    intro k x
    change eval H (smoothContragredient ρ)
      (sectionAt (DoubleCoset.mk H K.toSubgroup (x * k.val))).val (x * k.val) = _
    rw [DoubleCoset.mk_mul_mem]
    exact eval_mul_of_mem_fixedVectors H (smoothContragredient ρ) K.toSubgroup
      (sectionAt (DoubleCoset.mk H K.toSubgroup x)).property k x
  refine ⟨⟨smoothFunctionOf H (smoothContragredient ρ) F hcov K hright, ?_⟩, ?_⟩
  · intro k
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact hright k x
  · intro q
    change eval H (smoothContragredient ρ)
      (sectionAt (DoubleCoset.mk H K.toSubgroup q.out)).val q.out = _
    rw [DoubleCoset.out_eq']
    exact fixedDoubleCosetSection_eval_self H (smoothContragredient ρ) K hK q.out (v q)

/-- Every functional on a compact-induction fixed space is given by the pairing. -/
theorem pairing_fixed_surjective (ν : Module.Dual ℂ (renardSpace H hH))
    (hν : ∀ (g : G) (φ : renardSpace H hH),
      ν (rightAction H (relativeModular H hH) g φ) = ν φ)
    (hν0 : ν ≠ 0) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (φ : Module.Dual ℂ (fixedVectors (compactInduced H (twist χ ρ)) K.toSubgroup)) :
    ∃ h ∈ fixedVectors (smoothInduced H (smoothContragredient ρ)) K.toSubgroup,
      ∀ f : fixedVectors (compactInduced H (twist χ ρ)) K.toSubgroup,
        pairing H hH χ hχ ρ ν h f.val = φ f := by
  let A (q : DoubleCoset.Quotient (H : Set G) (K.toSubgroup : Set G)) :
      Module.Dual ℂ (fixedVectors ρ (conjOpenSubgroup H K q.out).toSubgroup) :=
    (ν (basic H hH χ hχ K hK q.out))⁻¹ •
      ((φ.comp (compactFixedSectionLinear H (twist χ ρ) K hK q)).comp
        (fixedTwistEquiv H hH χ hχ ρ K hK q.out).symm.toLinearMap)
  let v (q : DoubleCoset.Quotient (H : Set G) (K.toSubgroup : Set G)) :=
    (smoothDualCompactFixedEquiv ρ hρ (conjOpenSubgroup H K q.out)
      (isCompact_conjOpenSubgroup H hH K hK q.out)).symm (A q)
  obtain ⟨h, heval⟩ := assemble H ρ K hK v
  refine ⟨h.val, h.property, ?_⟩
  have hgen :
      ((pairing H hH χ hχ ρ ν h.val).comp
        (fixedVectors (compactInduced H (twist χ ρ)) K.toSubgroup).subtype).comp
          (compactFixedSectionSum H (twist χ ρ) K hK) =
      φ.comp (compactFixedSectionSum H (twist χ ρ) K hK) := by
    apply DFinsupp.lhom_ext
    intro q w
    change pairing H hH χ hχ ρ ν h.val
      (DFinsupp.lsum ℂ (compactFixedSectionLinear H (twist χ ρ) K hK)
        (DFinsupp.single q w)).val =
      φ (DFinsupp.lsum ℂ (compactFixedSectionLinear H (twist χ ρ) K hK)
        (DFinsupp.single q w))
    rw [DFinsupp.lsum_single]
    change pairing H hH χ hχ ρ ν h.val
      (compactDoubleCosetSection H (twist χ ρ) K hK q.out w.val w.property) =
        φ (compactFixedSectionLinear H (twist χ ρ) K hK q w)
    rw [pairing_section H hH χ hχ ρ ν K hK h q.out w, heval q]
    have hv : smoothDualPairing ρ (v q).val w.val =
        A q (fixedTwistEquiv H hH χ hχ ρ K hK q.out w) :=
      LinearMap.congr_fun
        ((smoothDualCompactFixedEquiv ρ hρ (conjOpenSubgroup H K q.out)
          (isCompact_conjOpenSubgroup H hH K hK q.out)).apply_symm_apply (A q))
        (fixedTwistEquiv H hH χ hχ ρ K hK q.out w)
    rw [hv]
    change ((ν (basic H hH χ hχ K hK q.out))⁻¹ *
      φ (compactFixedSectionLinear H (twist χ ρ) K hK q w)) *
        ν (basic H hH χ hχ K hK q.out) =
      φ (compactFixedSectionLinear H (twist χ ρ) K hK q w)
    field_simp [basic_ne_zero H hH χ hχ ν hν hν0 K hK q.out]
  intro f
  obtain ⟨s, rfl⟩ := (compactFixedEvaluationEquiv H (twist χ ρ) K hK).symm.surjective f
  exact LinearMap.congr_fun hgen s

end ClosedSubgroupDuality

universe uG uV

/-- Renard III.2.7 for every closed subgroup, with the prescribed integral pairing. -/
theorem closedInductionSmoothDuality : ClosedInductionSmoothDualityStatement.{uG, uV} := by
  intro G _ _ _ _ _ _ H hH χ hχ ν hν hν0 W _ _ ρ hρ
  obtain ⟨Φ, hΦ⟩ := exists_smoothDualEquiv_of_fixedSurjective
    (ClosedSubgroupDuality.compact_cofinal (G := G))
    (compactInduced H (twist χ ρ)) (smoothInduced H (smoothContragredient ρ))
    (compactInduced_smooth H (twist χ ρ))
    (smoothInduced_smooth H (smoothContragredient ρ))
    (ClosedSubgroupDuality.pairing H hH χ hχ ρ ν)
    (ClosedSubgroupDuality.pairing_invariant H hH χ hχ ρ ν hν)
    (ClosedSubgroupDuality.pairing_left H hH χ hχ ρ ν hν hν0 hρ)
    (ClosedSubgroupDuality.pairing_fixed_surjective H hH χ hχ ρ ν hν hν0 hρ)
  exact ⟨Φ, fun h f =>
    ⟨ClosedSubgroupDuality.integrand H hH χ hχ ρ h f, fun _ => rfl, hΦ h f⟩⟩

end Langlands.Induction
