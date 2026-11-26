import Langlands.Correspondence.HenniartTameOrbitFormula
import Langlands.Representation.Clifford.PGroup
import Langlands.LocalFactor.Ramification.FiniteTameInertiaProof
import Langlands.LocalFactor.Ramification.Herbrand.AbsoluteProof
import Langlands.LocalFactor.Ramification.Herbrand.InertiaProof
import Langlands.LocalFactor.Ramification.Herbrand.WeilInertiaProof
import Langlands.LocalFactor.Ramification.Herbrand.WildInertiaStructure
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Wild inertia inside the inertia of the Weil group

Wild inertia `P` of a p-adic field `K` is closed in inertia `I`; its image in the inertia of
each finite Galois subextension is the first lower ramification group; `I / P` is abelian and
every open subgroup of `I` containing `P` has cyclic quotient of index prime to `p`; and `P` is
pro-`p`, so its open-kernel irreducible representations have `p`-power dimension.
-/

noncomputable section

namespace Langlands.Henniart.WildInertia

open Weil.Local Ramification.Padic Ramification.HerbrandBridge

universe u

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

local instance : CharZero K.Carrier := Algebra.charZero_of_charZero (Padic p) K.Carrier

/-- The finite Galois subfields of the fixed algebraic closure. -/
abbrev FG := FiniteGaloisIntermediateField K.Carrier (AlgebraicClosure K.Carrier)

/-- The supremum of the upper ramification groups of positive index is the first lower group. -/
theorem iSup_upper_eq_lower_one {L : PadicField.{u} p} (T : L.TopologicalData)
    (F : Type*) [Field F] [Algebra (Padic p) F] [Algebra F L.Carrier]
    [IsScalarTower (Padic p) F L.Carrier] :
    (⨆ (w : ℝ) (_ : 0 < w), upperRamificationGroup T F w) = lowerRamificationGroup T F 1 := by
  apply le_antisymm
  · refine iSup₂_le fun w hw => ?_
    rw [upperRamificationGroup_eq_lower]
    have h1 : (1 : ℤ) ≤ ⌈herbrandPsi T F w⌉ := Int.one_le_ceil_iff.mpr (herbrandPsi_pos T F hw)
    have h2 := lowerRamificationGroupInt_antitone T F h1
    refine h2.trans ?_
    rw [← lowerRamificationGroupReal_int, ← lowerRamificationGroupReal_nat]
    simp
  · have hpos : 0 < herbrandPhi T F 1 := herbrandPhi_pos T F one_pos
    refine le_trans ?_ (le_iSup₂ (f := fun (w : ℝ) (_ : 0 < w) => upperRamificationGroup T F w)
      _ hpos)
    rw [upperRamificationGroup_phi]
    exact (lowerRamificationGroupReal_nat T F 1).ge.trans (le_of_eq (by simp))

/-- Absolute wild inertia lies in absolute inertia. -/
theorem wildInertia_le_absoluteInertia :
    wildInertia K ≤ K.absoluteInertia K.canonicalTopologicalData := by
  change (⨆ (v : ℝ) (_ : 0 < v), absoluteUpperRamificationGroup K v).topologicalClosure ≤ _
  apply Subgroup.topologicalClosure_minimal _ _ (K.absoluteInertia_isClosed _)
  refine iSup₂_le fun v hv => ?_
  rw [← absoluteUpperCanonicalInertia K]
  exact absoluteUpperRamificationGroup_antitone K hv.le

/-- Wild inertia of the Weil group lies in inertia. -/
theorem weilWildInertia_le_localInertia : weilWildInertia K ≤ localInertia K := by
  rw [localInertia_eq_comap]
  exact Subgroup.comap_mono (wildInertia_le_absoluteInertia K)

/-- Wild inertia as a subgroup of the inertia of the Weil group. -/
abbrev wildIn : Subgroup (localInertia K) := (weilWildInertia K).subgroupOf (localInertia K)

/-- The topological data of a finite Galois subfield. -/
abbrev finT (L : FG K) := (absoluteFiniteExtension K L).canonicalTopologicalData

/-- Restriction of Weil inertia to a finite Galois subfield. -/
abbrev res (L : FG K) := weilInertiaRestriction K L

theorem res_coe (L : FG K) (w : localInertia K) :
    ((res K L w : Gal(L/K.Carrier))) = absoluteFiniteRestriction K L (localProjection K w) :=
  weilInertiaRestriction_coe K L w

theorem res_surjective (L : FG K) : Function.Surjective (res K L) :=
  weilInertiaRestriction_surjective K L

/-- The image of wild inertia in a finite Galois quotient is the first lower group. -/
theorem map_wildIn (L : FG K) :
    (wildIn K).map (res K L).toMonoidHom =
      (lowerRamificationGroup (finT K L) K.Carrier 1).subgroupOf (inertia (finT K L) K.Carrier) := by
  have himage := absoluteUpperClosedRightImage K L 0 (by norm_num)
  have hsup := iSup_upper_eq_lower_one (finT K L) K.Carrier
  change (wildInertia K).map (absoluteFiniteRestriction K L).toMonoidHom = _ at himage
  ext τ
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    change ((res K L w : Gal(L/K.Carrier))) ∈ lowerRamificationGroup (finT K L) K.Carrier 1
    rw [res_coe, ← hsup]
    change absoluteFiniteRestriction K L (localProjection K w) ∈
      ⨆ (w : ℝ) (_ : 0 < w), canonicalUpperRamificationGroup (absoluteFiniteExtension K L)
        K.Carrier w
    rw [← himage]
    exact Subgroup.mem_map_of_mem _ hw
  · intro hτ
    rw [Subgroup.mem_subgroupOf] at hτ
    rw [← hsup] at hτ
    change (τ : Gal(L/K.Carrier)) ∈ ⨆ (w : ℝ) (_ : 0 < w),
      canonicalUpperRamificationGroup (absoluteFiniteExtension K L) K.Carrier w at hτ
    rw [← himage] at hτ
    obtain ⟨σ, hσ, hστ⟩ := hτ
    have hσI : σ ∈ K.absoluteInertia K.canonicalTopologicalData :=
      wildInertia_le_absoluteInertia K hσ
    let w := (localInertiaEquiv K).symm ⟨σ, hσI⟩
    have hw : localProjection K w = σ :=
      congrArg Subtype.val ((localInertiaEquiv K).apply_symm_apply ⟨σ, hσI⟩)
    refine ⟨w, ?_, ?_⟩
    · change localProjection K w ∈ wildInertia K
      rw [hw]
      exact hσ
    · apply Subtype.ext
      change (res K L w : Gal(L/K.Carrier)) = τ
      rw [res_coe, hw]
      exact hστ

/-- The kernels of the finite restrictions form a basis of neighbourhoods of one in Weil
inertia. -/
theorem exists_res_ker_subset {O : Set (localInertia K)} (hO : IsOpen O) (h1 : 1 ∈ O) :
    ∃ L : FG K, ∀ w : localInertia K, res K L w = 1 → w ∈ O := by
  let e := localInertiaEquiv K
  have hO' : IsOpen (e '' O) := e.toHomeomorph.isOpenMap O hO
  obtain ⟨O₂, hO₂, hO₂e⟩ := isOpen_induced_iff.mp hO'
  have h12 : (1 : Field.absoluteGaloisGroup K.Carrier) ∈ O₂ := by
    have : (1 : K.absoluteInertia K.canonicalTopologicalData) ∈ e '' O :=
      ⟨1, h1, map_one e⟩
    rw [← hO₂e] at this
    exact this
  obtain ⟨L, hL⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois (A := O₂)).mp (hO₂.mem_nhds h12)
  refine ⟨L, fun w hw => ?_⟩
  have hw' : absoluteFiniteRestriction K L (localProjection K w) = 1 := by
    rw [← res_coe]
    exact congrArg Subtype.val hw
  have hfix : localProjection K w ∈ L.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker]
    exact hw'
  have hmem : (e w : K.absoluteInertia K.canonicalTopologicalData) ∈ e '' O := by
    rw [← hO₂e]
    exact hL hfix
  obtain ⟨w', hw'O, hw'e⟩ := hmem
  rw [e.injective hw'e] at hw'O
  exact hw'O

/-- Wild inertia is closed in Weil inertia. -/
theorem isClosed_wildIn : IsClosed ((wildIn K : Subgroup (localInertia K)) : Set (localInertia K)) := by
  have h1 : IsClosed ((wildInertia K : Subgroup _) : Set (Field.absoluteGaloisGroup K.Carrier)) :=
    Subgroup.isClosed_topologicalClosure
      (⨆ (v : ℝ) (_ : 0 < v), absoluteUpperRamificationGroup K v)
  have h2 : IsClosed ((weilWildInertia K : Subgroup _) : Set (localWeilGroup K)) :=
    h1.preimage (localProjection K).continuous
  exact h2.preimage continuous_subtype_val

/-- An open subgroup of Weil inertia contains the kernel of some finite restriction. -/
theorem ker_res_le {U : Subgroup (localInertia K)} (hU : IsOpen (U : Set (localInertia K))) :
    ∃ L : FG K, (res K L).toMonoidHom.ker ≤ U := by
  obtain ⟨L, hL⟩ := exists_res_ker_subset K hU U.one_mem
  exact ⟨L, fun w hw => hL w hw⟩

/-- The lower group of index one is the image of wild inertia. -/
theorem inertiaLowerGroup_eq_map (L : FG K) :
    inertiaLowerGroup (finT K L) K.Carrier 1 = (wildIn K).map (res K L).toMonoidHom :=
  (map_wildIn K L).symm

/-- Every open subgroup of Weil inertia containing wild inertia has index prime to `p`. -/
theorem coprime_index_of_wildIn_le {U : Subgroup (localInertia K)} (hNU : wildIn K ≤ U)
    (hUo : IsOpen (U : Set (localInertia K))) : Nat.Coprime U.index p := by
  obtain ⟨L, hL⟩ := ker_res_le K hUo
  have hsurj : Function.Surjective (res K L).toMonoidHom := res_surjective K L
  rw [← Subgroup.index_map_eq U hsurj hL]
  have hW : inertiaLowerGroup (finT K L) K.Carrier 1 ≤ U.map (res K L).toMonoidHom := by
    rw [inertiaLowerGroup_eq_map]
    exact Subgroup.map_mono hNU
  have hcop := (inertia_quotient_lowerOne_cyclic_coprime (finT K L) K.Carrier).2
  exact Nat.Coprime.coprime_dvd_left (Subgroup.index_dvd_of_le hW) hcop

/-- For every open subgroup of Weil inertia containing wild inertia, the powers of one element
meet every right coset. -/
theorem cyclicOpenQuotients_wildIn : Clifford.CyclicOpenQuotients (wildIn K) := by
  intro U hNU hUo
  obtain ⟨L, hL⟩ := ker_res_le K hUo
  let r := (res K L).toMonoidHom
  let W' := inertiaLowerGroup (finT K L) K.Carrier 1
  have : W'.Normal := inertiaLowerGroup_isNormal (finT K L) K.Carrier 1
  have hcyc := (inertia_quotient_lowerOne_cyclic_coprime (finT K L) K.Carrier).1
  obtain ⟨gbar, hgbar⟩ := hcyc.exists_generator
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective gbar
  obtain ⟨g, rfl⟩ := res_surjective K L g₀
  refine ⟨g, fun x => ?_⟩
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgbar (QuotientGroup.mk (r x)))
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hi
  have hW : r (x * (g ^ i)⁻¹) ∈ W' := by
    rw [map_mul, map_inv, map_zpow]
    exact ‹W'.Normal›.mem_comm hi
  have hmap : W' = (wildIn K).map r := inertiaLowerGroup_eq_map K L
  rw [hmap] at hW
  obtain ⟨n, hn, hnr⟩ := hW
  refine ⟨i, ?_⟩
  have hker : n⁻¹ * (x * (g ^ i)⁻¹) ∈ U := by
    apply hL
    rw [MonoidHom.mem_ker, map_mul, map_inv, hnr, inv_mul_cancel]
  have := U.mul_mem (hNU hn) hker
  rwa [mul_inv_cancel_left] at this

/-- Membership in wild inertia is detected in the finite Galois quotients. -/
theorem mem_wildIn_of_forall {y : localInertia K}
    (hy : ∀ L : FG K, res K L y ∈ inertiaLowerGroup (finT K L) K.Carrier 1) : y ∈ wildIn K := by
  by_contra hyN
  let O : Set (localInertia K) := (fun w => y * w) ⁻¹' ((wildIn K : Set (localInertia K))ᶜ)
  have hO : IsOpen O :=
    (isClosed_wildIn K).isOpen_compl.preimage (continuous_const.mul continuous_id)
  have h1 : (1 : localInertia K) ∈ O := by
    change y * 1 ∈ ((wildIn K : Set (localInertia K))ᶜ)
    rw [mul_one]
    exact hyN
  obtain ⟨L, hL⟩ := exists_res_ker_subset K hO h1
  have hmem := hy L
  rw [inertiaLowerGroup_eq_map] at hmem
  obtain ⟨n, hn, hnr⟩ := hmem
  have hnr' : res K L n = res K L y := hnr
  have hk : res K L (y⁻¹ * n) = 1 := by
    rw [map_mul, map_inv, hnr', inv_mul_cancel]
  have hO' := hL _ hk
  change y * (y⁻¹ * n) ∈ ((wildIn K : Set (localInertia K))ᶜ) at hO'
  rw [mul_inv_cancel_left] at hO'
  exact hO' hn

/-- Commutators of Weil inertia lie in wild inertia. -/
theorem commutatorsIn_wildIn : Clifford.CommutatorsIn (wildIn K) := by
  intro x y
  apply mem_wildIn_of_forall
  intro L
  have : (inertiaLowerGroup (finT K L) K.Carrier 1).Normal :=
    inertiaLowerGroup_isNormal (finT K L) K.Carrier 1
  have hcyc := (inertia_quotient_lowerOne_cyclic_coprime (finT K L) K.Carrier).1
  have hcomm : ∀ a b : (inertia (finT K L) K.Carrier) ⧸ inertiaLowerGroup (finT K L) K.Carrier 1,
      a * b = b * a := fun a b => (IsMulCommutative.is_comm (M := _)).comm a b
  rw [← QuotientGroup.eq_one_iff, map_mul, map_mul, map_mul, map_inv, map_inv,
    QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv, hcomm (QuotientGroup.mk (res K L x)) (QuotientGroup.mk (res K L y))]
  group

/-- The first lower group of a finite Galois subextension has `p`-power order. -/
theorem exists_card_inertiaLowerGroup (L : FG K) :
    ∃ b : ℕ, Nat.card (inertiaLowerGroup (finT K L) K.Carrier 1) = p ^ b := by
  have hP := (Ramification.Padic.finiteTameInertiaStructure p K (absoluteFiniteExtension K L)
    (finT K L)).1
  have hP' : IsPGroup p (inertiaLowerGroup (finT K L) K.Carrier 1) := by
    intro g
    obtain ⟨k, hk⟩ := hP ⟨g.1.1, g.2⟩
    refine ⟨k, ?_⟩
    have h2 := congrArg Subtype.val hk
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
    apply Subtype.ext
    apply Subtype.ext
    simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using h2
  exact IsPGroup.iff_card.mp hP'

/-- Wild inertia inside Weil inertia has the `p`-power property. -/
theorem pPowerOpen_wildIn : Clifford.PPowerOpen p (wildIn K) := by
  intro M hM
  obtain ⟨O, hO, hOM⟩ := isOpen_induced_iff.mp hM
  have h1 : (1 : localInertia K) ∈ O := by
    have h1M : (1 : wildIn K) ∈ (M : Set (wildIn K)) := M.one_mem
    rw [← hOM] at h1M
    exact h1M
  obtain ⟨L, hL⟩ := exists_res_ker_subset K hO h1
  obtain ⟨b, hb⟩ := exists_card_inertiaLowerGroup K L
  refine ⟨b, fun n => ?_⟩
  have hn : res K L n ∈ inertiaLowerGroup (finT K L) K.Carrier 1 := by
    rw [inertiaLowerGroup_eq_map]
    exact ⟨n, n.2, rfl⟩
  have hpow : res K L ((n : localInertia K) ^ p ^ b) = 1 := by
    rw [map_pow]
    have h := pow_card_eq_one' (G := inertiaLowerGroup (finT K L) K.Carrier 1) (x := ⟨_, hn⟩)
    rw [hb] at h
    exact congrArg Subtype.val h
  have hmem := hL _ hpow
  change n ^ p ^ b ∈ (M : Set (wildIn K))
  rw [← hOM]
  exact hmem

/-- Wild inertia regarded inside Weil inertia and inside the Weil group. -/
def wildEquiv : wildIn K ≃ₜ* weilWildInertia K where
  toMulEquiv := Subgroup.subgroupOfEquivOfLe (weilWildInertia_le_localInertia K)
  continuous_toFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

@[simp] theorem wildEquiv_apply (n : wildIn K) :
    ((wildEquiv K n : weilWildInertia K) : localWeilGroup K) = ((n : localInertia K) : localWeilGroup K) :=
  rfl

/-- Inertia of the Weil group is compact. -/
instance compactSpace_localInertia : CompactSpace (localInertia K) :=
  isCompact_iff_compactSpace.mp (localInertia_isCompact K)

/-- Wild inertia is compact. -/
instance compactSpace_wildIn : CompactSpace (wildIn K) :=
  isCompact_iff_compactSpace.mp (isClosed_wildIn K).isCompact

/-- Wild inertia of the Weil group is compact. -/
instance compactSpace_weilWildInertia : CompactSpace (weilWildInertia K) :=
  (wildEquiv K).toHomeomorph.compactSpace

/-- Wild inertia of the Weil group has the `p`-power property. -/
theorem pPowerOpen_weilWildInertia : Clifford.PPowerOpen p (weilWildInertia K) :=
  (pPowerOpen_wildIn K).of_continuous (wildEquiv K).toMulEquiv (wildEquiv K).continuous_toFun

end Langlands.Henniart.WildInertia
