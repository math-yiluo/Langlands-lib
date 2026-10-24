import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Topology.CompactOpen.NeighborhoodBasis

/-! Compact covariant sections with a prescribed value and quotient neighborhood. -/

noncomputable section

open Topology

namespace Langlands.Induction

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V]

section DoubleCoset

variable [IsTopologicalGroup G]

private def inDoubleCoset (P : Subgroup G) (K : OpenSubgroup G) (x y : G) : Prop :=
  ∃ p : P, ∃ k : K, y = (p : G) * x * (k : G)

private def doubleCosetValue (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (x : G) (v : V) (y : G) : V := by
  classical
  exact if h : inDoubleCoset P K x y then σ h.choose v else 0

private theorem doubleCosetValue_eq (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (x : G) (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup P K x).toSubgroup)
    (p : P) (k : K) :
    doubleCosetValue P σ K x v ((p : G) * x * (k : G)) = σ p v := by
  classical
  have h : inDoubleCoset P K x ((p : G) * x * (k : G)) := ⟨p, k, rfl⟩
  rw [doubleCosetValue, dite_eq_left h]
  obtain ⟨l, hl⟩ := h.choose_spec
  have hm : x⁻¹ * ((p⁻¹ * h.choose : P) : G) * x ∈ K := by
    have he : x⁻¹ * ((p⁻¹ * h.choose : P) : G) * x = (k : G) * (l : G)⁻¹ := by
      calc
        _ = ((p : G) * x)⁻¹ * ((h.choose : G) * x * (l : G)) * (l : G)⁻¹ := by
          simp [mul_assoc]
        _ = ((p : G) * x)⁻¹ * ((p : G) * x * (k : G)) * (l : G)⁻¹ := by rw [← hl]
        _ = _ := by group
    rw [he]
    exact K.mul_mem k.property (K.inv_mem l.property)
  have hfix := hv ⟨p⁻¹ * h.choose, mem_conjOpenSubgroup.mpr hm⟩
  change σ (p⁻¹ * h.choose) v = v at hfix
  have he := congrArg (σ p) hfix
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] using he

private theorem doubleCosetValue_covariant (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (x : G) (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup P K x).toSubgroup)
    (p : P) (y : G) :
    doubleCosetValue P σ K x v ((p : G) * y) = σ p (doubleCosetValue P σ K x v y) := by
  classical
  by_cases h : inDoubleCoset P K x y
  · obtain ⟨q, k, rfl⟩ := h
    rw [doubleCosetValue_eq P σ K x v hv]
    have he : (p : G) * ((q : G) * x * (k : G)) = ((p * q : P) : G) * x * (k : G) := by
      simp [mul_assoc]
    rw [he, doubleCosetValue_eq P σ K x v hv, map_mul, Module.End.mul_apply]
  · have hn : ¬ inDoubleCoset P K x ((p : G) * y) := by
      rintro ⟨q, k, he⟩
      apply h
      refine ⟨p⁻¹ * q, k, ?_⟩
      have he' := congrArg (fun z => (p : G)⁻¹ * z) he
      simpa [mul_assoc] using he'
    simp [doubleCosetValue, h, hn]

private theorem doubleCosetValue_mul (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (x : G) (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup P K x).toSubgroup)
    (k : K) (y : G) :
    doubleCosetValue P σ K x v (y * (k : G)) = doubleCosetValue P σ K x v y := by
  classical
  by_cases h : inDoubleCoset P K x y
  · obtain ⟨p, l, rfl⟩ := h
    have he : (p : G) * x * (l : G) * (k : G) = (p : G) * x * ((l * k : K) : G) := by
      simp [mul_assoc]
    rw [he, doubleCosetValue_eq P σ K x v hv, doubleCosetValue_eq P σ K x v hv]
  · have hn : ¬ inDoubleCoset P K x (y * (k : G)) := by
      rintro ⟨p, l, he⟩
      apply h
      refine ⟨p, l * k⁻¹, ?_⟩
      have he' := congrArg (fun z => z * (k : G)⁻¹) he
      simpa [mul_assoc] using he'
    simp [doubleCosetValue, h, hn]

omit [IsTopologicalGroup G] in
private theorem doubleCosetValue_support_subset (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (x : G) (v : V) :
    quotientSupport P (doubleCosetValue P σ K x v) ⊆
      (fun k => quotientMap P (x * k)) '' (K : Set G) := by
  classical
  rintro _ ⟨y, hy, rfl⟩
  have h : inDoubleCoset P K x y := by
    by_contra hn
    exact hy (by simp [doubleCosetValue, hn])
  obtain ⟨p, k, rfl⟩ := h
  refine ⟨k, k.property, ?_⟩
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simp [mul_inv_rev, mul_assoc]

/-- The compact covariant section on `P * x * K` with prescribed value `v` at `x`,
provided `P ∩ x K x⁻¹` fixes `v`. -/
def compactDoubleCosetSection (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup P K x).toSubgroup) :
    CompactFunctions P σ := by
  let f := smoothFunctionOf P σ (doubleCosetValue P σ K x v)
    (doubleCosetValue_covariant P σ K x v hv) K (doubleCosetValue_mul P σ K x v hv)
  refine ⟨f, ?_⟩
  apply (hK.image ((continuous_quotient_mk').comp (continuous_const.mul continuous_id))).of_isClosed_subset
    (isClosed_quotientSupport P σ f)
  exact doubleCosetValue_support_subset P σ K x v

/-- Evaluation of the double-coset section at any chosen representative. -/
theorem compactDoubleCosetSection_apply (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup P K x).toSubgroup) (p : P) (k : K) :
    eval P σ (compactDoubleCosetSection P σ K hK x v hv).val
      ((p : G) * x * (k : G)) = σ p v :=
  doubleCosetValue_eq P σ K x v hv p k

/-- The section's actual projected nonzero support lies in the compact image of `x * K`. -/
theorem compactDoubleCosetSection_support_subset (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup P K x).toSubgroup) :
    quotientSupport P (eval P σ (compactDoubleCosetSection P σ K hK x v hv).val) ⊆
      (fun k => quotientMap P (x * k)) '' (K : Set G) :=
  doubleCosetValue_support_subset P σ K x v

/-- The chosen subgroup fixes the entire section by right translation. -/
theorem compactDoubleCosetSection_mul (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) (v : V)
    (hv : v ∈ fixedVectors σ (conjOpenSubgroup P K x).toSubgroup) (k : K) (y : G) :
    eval P σ (compactDoubleCosetSection P σ K hK x v hv).val (y * (k : G)) =
      eval P σ (compactDoubleCosetSection P σ K hK x v hv).val y :=
  doubleCosetValue_mul P σ K x v hv k y

end DoubleCoset

section Local

variable [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]

private theorem exists_localSectionSubgroup (P : Subgroup G) (σ : Representation R P V)
    (hσ : IsSmooth σ) (x : G) (v : V) (U : Set (LeftQuotient P))
    (hU : IsOpen U) (hx : quotientMap P x ∈ U) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      v ∈ fixedVectors σ (conjOpenSubgroup P K x).toSubgroup ∧
      (fun k => quotientMap P (x * k)) '' (K : Set G) ⊆ U := by
  obtain ⟨H, hH⟩ := hσ v
  obtain ⟨O, hO, he⟩ := IsInducing.subtypeVal.isOpen_iff.mp H.isOpen
  have h1 : (1 : G) ∈ O := by
    have hh : (1 : P) ∈ (Subtype.val : P → G) ⁻¹' O := by
      exact (Set.ext_iff.mp he (1 : P)).mpr H.one_mem
    exact hh
  let N : Set G := (fun k => x * k * x⁻¹) ⁻¹' O ∩
    (fun k => quotientMap P (x * k)) ⁻¹' U
  have hN : N ∈ 𝓝 (1 : G) := by
    apply IsOpen.mem_nhds
    · exact (hO.preimage ((continuous_const.mul continuous_id).mul_const _)).inter
        (hU.preimage (continuous_quotient_mk'.comp (continuous_const.mul continuous_id)))
    · exact ⟨by simpa using h1, by simpa using hx⟩
  obtain ⟨K, hK, hKN⟩ := compactOpenSubgroupBasis G N hN
  refine ⟨K, hK, ?_, ?_⟩
  · intro p
    have hp : x⁻¹ * ((p : P) : G) * x ∈ K := mem_conjOpenSubgroup.mp p.property
    have hpO : ((p : P) : G) ∈ O := by
      simpa [mul_assoc] using (hKN hp).1
    have hpH : (p : P) ∈ H := (Set.ext_iff.mp he (p : P)).mp hpO
    exact hH ⟨p, hpH⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact (hKN hk).2

/-- A compactly induced section with value `v` at `x`, supported over the prescribed
open neighborhood `U` of the coset of `x`. No closedness hypothesis on `P` is needed. -/
def compactLocalSection (P : Subgroup G) (σ : Representation R P V)
    (hσ : IsSmooth σ) (x : G) (v : V) (U : Set (LeftQuotient P))
    (hU : IsOpen U) (hx : quotientMap P x ∈ U) : CompactFunctions P σ :=
  let h := exists_localSectionSubgroup P σ hσ x v U hU hx
  compactDoubleCosetSection P σ h.choose h.choose_spec.1 x v h.choose_spec.2.1

/-- The constructed local section has the prescribed value at `x`. -/
theorem compactLocalSection_apply (P : Subgroup G) (σ : Representation R P V)
    (hσ : IsSmooth σ) (x : G) (v : V) (U : Set (LeftQuotient P))
    (hU : IsOpen U) (hx : quotientMap P x ∈ U) :
    eval P σ (compactLocalSection P σ hσ x v U hU hx).val x = v := by
  unfold compactLocalSection
  simpa using compactDoubleCosetSection_apply P σ
    (exists_localSectionSubgroup P σ hσ x v U hU hx).choose
    (exists_localSectionSubgroup P σ hσ x v U hU hx).choose_spec.1 x v
    (exists_localSectionSubgroup P σ hσ x v U hU hx).choose_spec.2.1 1 1

/-- The actual projected nonzero support of the constructed local section lies in `U`. -/
theorem compactLocalSection_support_subset (P : Subgroup G) (σ : Representation R P V)
    (hσ : IsSmooth σ) (x : G) (v : V) (U : Set (LeftQuotient P))
    (hU : IsOpen U) (hx : quotientMap P x ∈ U) :
    quotientSupport P (eval P σ (compactLocalSection P σ hσ x v U hU hx).val) ⊆ U := by
  let h := exists_localSectionSubgroup P σ hσ x v U hU hx
  exact (compactDoubleCosetSection_support_subset P σ h.choose h.choose_spec.1
    x v h.choose_spec.2.1).trans h.choose_spec.2.2

end Local

end Langlands.Induction
