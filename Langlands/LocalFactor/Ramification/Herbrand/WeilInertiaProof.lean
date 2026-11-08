import Langlands.LocalFactor.Ramification.Herbrand.InertiaProof
import Langlands.LocalFactor.Ramification.InertiaPresentationStatement
import Langlands.LocalFactor.Ramification.WeilBreakStatement
import Langlands.Weil.Local.ContinuityProof

/-!
# Inertia restrictions, finite presentations and nonempty break thresholds

Absolute inertia maps onto inertia in every actual finite Galois subfield, hence
so does Weil inertia and every finite restriction. A continuous complex
representation of the local Weil group is presented on the inertia of some
actual finite Galois subfield, and some nonnegative upper group acts trivially.
-/

noncomputable section

namespace Langlands.Ramification.HerbrandBridge

open _root_.Langlands.Ramification.Padic Weil.Local
open VirtualRepresentation.LocalWeil.Ramification

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- Absolute inertia surjects onto inertia in every actual finite Galois subfield. -/
theorem absoluteInertiaRestriction_surjective :
    AbsoluteInertiaRestrictionSurjectivityStatement F := by
  intro L τ
  have hτ : (τ : Gal(L/F.Carrier)) ∈
      canonicalUpperRamificationGroup (absoluteFiniteExtension F L) F.Carrier 0 := by
    rw [canonicalUpperRamificationGroup, _root_.Langlands.Ramification.Padic.upperRamificationGroup_zero]
    exact τ.property
  rw [← absoluteUpperFiniteImage F L 0 (by norm_num)] at hτ
  obtain ⟨σ, hσ, he⟩ := Subgroup.mem_map.mp hτ
  rw [absoluteUpperCanonicalInertia F] at hσ
  exact ⟨⟨σ, hσ⟩, Subtype.ext he⟩

/-- Weil inertia surjects onto inertia in every actual finite Galois subfield. -/
theorem weilInertiaRestriction_surjective :
    WeilInertiaRestrictionSurjectivityStatement F := by
  intro L τ
  obtain ⟨σ, rfl⟩ := absoluteInertiaRestriction_surjective F L τ
  refine ⟨(localInertiaEquiv F).symm σ, ?_⟩
  change absoluteInertiaRestriction F L (localInertiaEquiv F ((localInertiaEquiv F).symm σ)) = _
  rw [ContinuousMulEquiv.apply_symm_apply]

/-- Inertia restriction is surjective along every inclusion of actual finite Galois
subfields. -/
theorem finiteInertiaRestriction_surjective :
    FiniteInertiaRestrictionSurjectivityStatement F := by
  intro L M h τ
  obtain ⟨σ, rfl⟩ := absoluteInertiaRestriction_surjective F L τ
  exact ⟨absoluteInertiaRestriction F M σ, finiteInertiaRestriction_absolute F h σ⟩

variable (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F))

/-- A continuous complex representation of the local Weil group is presented on the
inertia of some actual finite Galois subfield. -/
theorem continuousWeilFiniteInertiaPresentation :
    ContinuousWeilFiniteInertiaPresentationStatement F A := by
  intro hA
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  have : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  have hopen : IsOpen ((localInertiaRepresentation F A).ker : Set (localInertia F)) :=
    ((localWeilContinuity.{u, v} F A).2.2.1).mp hA
  set e := localInertiaEquiv F
  have hN : (e.symm ⁻¹' ((localInertiaRepresentation F A).ker : Set (localInertia F))) ∈
      nhds (1 : F.absoluteInertia F.canonicalTopologicalData) :=
    (hopen.preimage e.symm.continuous).mem_nhds (by simp)
  rw [nhds_subtype, Filter.mem_comap] at hN
  obtain ⟨V, hV, hVN⟩ := hN
  have hV' : V ∈ nhds (1 : Gal(AlgebraicClosure F.Carrier/F.Carrier)) := hV
  obtain ⟨E, hEfd, hEn, hEV⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal F.Carrier (AlgebraicClosure F.Carrier) V).mp hV'
  let L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier) :=
    { toIntermediateField := E
      finiteDimensional := hEfd
      isGalois := { to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable F.Carrier E
                      (AlgebraicClosure F.Carrier)
                    to_normal := hEn } }
  refine ⟨⟨L, fun w hw => ?_⟩⟩
  have hw1 : absoluteFiniteRestriction F L (localProjection F w) = 1 := by
    have := congrArg Subtype.val (show weilInertiaRestriction F L w = 1 from hw)
    rwa [weilInertiaRestriction_coe] at this
  have hfix : localProjection F w ∈ E.fixingSubgroup :=
    (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff (localProjection F w) L).mpr hw1
  have hmem : e w ∈ ((↑) : F.absoluteInertia F.canonicalTopologicalData →
      Field.absoluteGaloisGroup F.Carrier) ⁻¹' V := hEV hfix
  have := hVN hmem
  simpa using this

/-- A chosen finite inertia presentation of a continuous representation. -/
noncomputable def chosenInertiaPresentation (hA : A.IsContinuous) : FiniteInertiaPresentation F A :=
  Classical.choice (continuousWeilFiniteInertiaPresentation F A hA)

/-- A continuous complex representation of the local Weil group has finite inertia
image. -/
theorem continuousWeilFiniteInertiaImage : ContinuousWeilFiniteInertiaImageStatement F A := by
  intro hA
  exact (((localWeilContinuity.{u, v} F A).2.2.2.2).mp
    (((localWeilContinuity.{u, v} F A).2.2.1).mp hA)).1

/-- Continuity gives a nonnegative upper index at which the action is trivial. -/
theorem weilTrivialityThresholdsNonempty : WeilTrivialityThresholdsNonempty.{u, v} F := by
  intro A hA
  obtain ⟨P⟩ := continuousWeilFiniteInertiaPresentation F A hA
  obtain ⟨b, hb⟩ := exists_upperRamificationGroup_eq_bot
    (absoluteFiniteExtension F P.extension).canonicalTopologicalData F.Carrier
  refine ⟨max b 0, le_max_right _ _, fun w hw => ?_⟩
  have hw0 : localProjection F w ∈ absoluteUpperRamificationGroup F 0 :=
    absoluteUpperRamificationGroup_antitone F (le_max_right b 0) hw
  rw [absoluteUpperCanonicalInertia F] at hw0
  have hwI : w ∈ localInertia F := by
    rw [localInertia_eq_comap F]
    exact hw0
  have hL := absoluteUpperRamificationGroup_le_comap F (max b 0) P.extension hw
  rw [Subgroup.mem_comap] at hL
  have hbot : absoluteFiniteRestriction F P.extension (localProjection F w) = 1 := by
    have h := hb (max b 0) (le_max_left _ _)
    rw [canonicalUpperRamificationGroup, h, Subgroup.mem_bot] at hL
    exact hL
  have hker : (⟨w, hwI⟩ : localInertia F) ∈
      (weilInertiaRestriction F P.extension).toMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact hbot
  exact P.kernel_le hker

/-- Triviality at a positive index persists slightly to its left. -/
theorem exists_lt_isTrivialAt (hA : A.IsContinuous) {b : ℝ} (hb : 0 < b)
    (htriv : IsTrivialAt F A b) : ∃ b', 0 < b' ∧ b' < b ∧ IsTrivialAt F A b' := by
  set P := chosenInertiaPresentation F A hA
  set T := (absoluteFiniteExtension F P.extension).canonicalTopologicalData
  obtain ⟨c, hc1, hcb, heq⟩ := exists_lt_upperRamificationGroup_eq T F.Carrier
    (show (-1 : ℝ) < b by linarith)
  set b' := max c (b / 2)
  have hb'pos : 0 < b' := lt_of_lt_of_le (by linarith) (le_max_right c (b / 2))
  have hb'b : b' < b := max_lt hcb (by linarith)
  have hupper : Padic.upperRamificationGroup T F.Carrier b' =
      Padic.upperRamificationGroup T F.Carrier b := by
    apply le_antisymm
    · rw [← heq]
      exact Padic.upperRamificationGroup_antitone T F.Carrier (le_max_left _ _)
    · exact Padic.upperRamificationGroup_antitone T F.Carrier hb'b.le
  refine ⟨b', hb'pos, hb'b, fun w hw => ?_⟩
  have hw0 : localProjection F w ∈ absoluteUpperRamificationGroup F 0 :=
    absoluteUpperRamificationGroup_antitone F hb'pos.le hw
  rw [absoluteUpperCanonicalInertia F] at hw0
  have hwI : w ∈ localInertia F := by
    rw [localInertia_eq_comap F]
    exact hw0
  have hL := absoluteUpperRamificationGroup_le_comap F b' P.extension hw
  rw [Subgroup.mem_comap] at hL
  change _ ∈ Padic.upperRamificationGroup T F.Carrier b' at hL
  rw [hupper, ← canonicalUpperRamificationGroup, ← absoluteUpperFiniteImage F P.extension b
    (by linarith)] at hL
  obtain ⟨σ, hσ, hσw⟩ := Subgroup.mem_map.mp hL
  have hσ0 : σ ∈ F.absoluteInertia F.canonicalTopologicalData := by
    rw [← absoluteUpperCanonicalInertia F]
    exact absoluteUpperRamificationGroup_antitone F hb.le hσ
  set w' : localInertia F := (localInertiaEquiv F).symm ⟨σ, hσ0⟩
  have hw'σ : localProjection F (w' : localWeilGroup F) = σ := by
    have := congrArg Subtype.val ((localInertiaEquiv F).apply_symm_apply ⟨σ, hσ0⟩)
    exact this
  have hAw' : A.representation (w' : localWeilGroup F) = 1 := by
    apply htriv
    change localProjection F (w' : localWeilGroup F) ∈ absoluteUpperRamificationGroup F b
    rw [hw'σ]
    exact hσ
  have hker : w'⁻¹ * ⟨w, hwI⟩ ∈ (weilInertiaRestriction F P.extension).toMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    apply Subtype.ext
    change (absoluteFiniteRestriction F P.extension (localProjection F (w' : localWeilGroup F)))⁻¹ *
      absoluteFiniteRestriction F P.extension (localProjection F w) = 1
    have hσw' : absoluteFiniteRestriction F P.extension σ =
        absoluteFiniteRestriction F P.extension (localProjection F w) := hσw
    rw [hw'σ, hσw']
    exact inv_mul_cancel _
  have hA' := P.kernel_le hker
  rw [MonoidHom.mem_ker] at hA'
  change A.representation ((w' : localWeilGroup F)⁻¹ * w) = 1 at hA'
  have hsplit : w = (w' : localWeilGroup F) * ((w' : localWeilGroup F)⁻¹ * w) := by group
  rw [hsplit, map_mul, hAw', hA', one_mul]

/-- For a positive index, the last break lies strictly below it exactly when the upper
group of that index acts trivially. -/
theorem lastBreak_lt_iff_isTrivialAt (hA : A.IsContinuous) {b : ℝ} (hb : 0 < b) :
    lastBreak F A < b ↔ IsTrivialAt F A b := by
  have hne := weilTrivialityThresholdsNonempty F A hA
  constructor
  · intro h
    obtain ⟨s, hs, hsb⟩ := exists_lt_of_csInf_lt hne h
    exact isTrivialAt_mono F A hsb.le hs.2
  · intro h
    obtain ⟨b', hb'pos, hb'b, hb'⟩ := exists_lt_isTrivialAt F A hA hb h
    exact lt_of_le_of_lt (lastBreak_le_of_mem F A ⟨hb'pos.le, hb'⟩) hb'b

/-- The zero label means trivial action by every positive upper group. -/
theorem weilLastBreakZero : WeilLastBreakZero.{u, v} F := by
  intro A hA
  constructor
  · intro h r hr
    exact (lastBreak_lt_iff_isTrivialAt F A hA hr).mp (h ▸ hr)
  · intro h
    apply le_antisymm _ (lastBreak_nonneg F A)
    apply le_of_forall_pos_lt_add
    intro ε hε
    rw [zero_add]
    exact (lastBreak_lt_iff_isTrivialAt F A hA hε).mpr (h ε hε)

/-- The fixed space of an upper group is everything exactly when it acts trivially. -/
theorem upperFixedSpace_eq_top_iff (r : ℝ) : upperFixedSpace F A r = ⊤ ↔ IsTrivialAt F A r := by
  constructor
  · intro h w hw
    apply LinearMap.ext
    intro v
    have hv : v ∈ upperFixedSpace F A r := h ▸ Submodule.mem_top
    exact (mem_upperFixedSpace F A r v).mp hv w hw
  · intro h
    apply eq_top_iff.mpr
    intro v _
    rw [mem_upperFixedSpace]
    intro w hw
    rw [h w hw]
    rfl

/-- The fixed space of an upper group is a subrepresentation, hence trivial or everything
for an irreducible representation. -/
theorem upperFixedSpace_eq_bot_or_eq_top (hirr : A.IsIrreducible) (r : ℝ) :
    upperFixedSpace F A r = ⊥ ∨ upperFixedSpace F A r = ⊤ := by
  have hn : (upperGroup F r).Normal := (absoluteUpperRamificationGroup_normal F r).comap _
  let S : Subrepresentation A.representation :=
    { toSubmodule := upperFixedSpace F A r
      apply_mem_toSubmodule := by
        intro g v hv
        rw [mem_upperFixedSpace] at hv ⊢
        intro w hw
        have hc : g⁻¹ * w * g ∈ upperGroup F r := by
          simpa using hn.conj_mem w hw g⁻¹
        have hsplit : w * g = g * (g⁻¹ * w * g) := by group
        rw [← Module.End.mul_apply, ← map_mul, hsplit, map_mul, Module.End.mul_apply, hv _ hc] }
  have : IsSimpleOrder (Subrepresentation A.representation) := hirr
  rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

/-- For an irreducible continuous representation, the positive thresholds are described by
the fixed spaces of the upper groups. -/
theorem weilIrreduciblePositiveThresholds : WeilIrreduciblePositiveThresholds.{u, v} F := by
  intro A hA hirr
  refine ⟨fun a ha => ⟨fun hle => ?_, fun hbot => ?_⟩, fun b hb => ?_⟩
  · rcases upperFixedSpace_eq_bot_or_eq_top F A hirr a with h | h
    · exact h
    · exact absurd ((lastBreak_lt_iff_isTrivialAt F A hA ha).mpr
        ((upperFixedSpace_eq_top_iff F A a).mp h)) (not_lt.mpr hle)
  · by_contra hlt
    rw [not_le] at hlt
    have htop := (upperFixedSpace_eq_top_iff F A a).mpr
      ((lastBreak_lt_iff_isTrivialAt F A hA ha).mp hlt)
    have : IsSimpleOrder (Subrepresentation A.representation) := hirr
    have hbt : (⊥ : Subrepresentation A.representation) = ⊤ :=
      Subrepresentation.toSubmodule_injective (hbot.symm.trans htop)
    exact bot_ne_top hbt
  · rw [upperFixedSpace_eq_top_iff]
    exact lastBreak_lt_iff_isTrivialAt F A hA hb

end Langlands.Ramification.HerbrandBridge
