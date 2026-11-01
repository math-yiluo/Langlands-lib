import Langlands.Representation.Aubert.CorrectedSupportFiltration
import Langlands.Representation.Aubert.LengthMinimality
import Langlands.Representation.Parabolic.QuotientCompactProof
import Langlands.Group.GL.UpperBruhatFiltrationGeometryProof
import Mathlib.Topology.Maps.Proper.Basic

/-! Openness of corrected two-sided Bruhat supports in the supplied p-adic topology. -/

noncomputable section

namespace Langlands.Aubert.Support

open GeneralLinear Geometric

universe uF

section CompactCore

variable {G : Type*} [Group G]
  (H P Q : Subgroup G) (K L : Set G)
  (hKP : K ⊆ P) (hLQ : L ⊆ Q)
  (hP : ∀ p ∈ P, ∃ h ∈ H, ∃ k ∈ K, p = h * k)
  (hQ : ∀ q ∈ Q, ∃ l ∈ L, ∃ h ∈ H, q = l * h)
  (U : Set G) (hU : IsTwoSidedInvariant H H U)

include hKP hLQ hP hQ hU in
/-- A Borel-invariant support only needs to be tested on compact coset representatives. -/
theorem mem_twoSidedCore_iff_compact_representatives (g : G) :
    g ∈ twoSidedCore P Q U ↔ ∀ k ∈ K, ∀ l ∈ L, k * g * l ∈ U := by
  constructor
  · intro hg k hk l hl
    exact (mem_twoSidedCore_iff P Q U g).mp hg k (hKP hk) l (hLQ hl)
  · intro hg
    apply (mem_twoSidedCore_iff P Q U g).mpr
    intro p hp q hq
    obtain ⟨a, ha, k, hk, rfl⟩ := hP p hp
    obtain ⟨l, hl, b, hb, rfl⟩ := hQ q hq
    simpa only [mul_assoc] using hU (k * g * l) (hg k hk l hl) a ha b hb

variable [TopologicalSpace G] [IsTopologicalGroup G]

include hKP hLQ hP hQ hU in
/-- Compact coset representatives make the two-sided core of an open invariant set open. -/
theorem isOpen_twoSidedCore_of_compact_representatives
    (hK : IsCompact K) (hL : IsCompact L) (hOpen : IsOpen U) :
    IsOpen (twoSidedCore P Q U) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  let S : Set (G × (K × L)) := {x | x.2.1.val * x.1 * x.2.2.val ∉ U}
  have hcont : Continuous (fun x : G × (K × L) => x.2.1.val * x.1 * x.2.2.val) := by
    fun_prop
  have hclosed : IsClosed S := hOpen.isClosed_compl.preimage hcont
  have heq : twoSidedCore P Q U = (Prod.fst '' S)ᶜ := by
    ext g
    rw [mem_twoSidedCore_iff_compact_representatives H P Q K L hKP hLQ hP hQ U hU]
    constructor
    · intro hg
      rintro ⟨⟨x, k, l⟩, hx, hxy⟩
      change k.val * x * l.val ∉ U at hx
      change x = g at hxy
      subst x
      exact hx (hg k.val k.property l.val l.property)
    · intro hg k hk l hl
      by_contra hkl
      exact hg ⟨(g, ⟨k, hk⟩, ⟨l, hl⟩), hkl, rfl⟩
  rw [heq]
  exact (isClosedMap_fst_of_compactSpace S hclosed).isOpen_compl

end CompactCore

section Bruhat

variable {F : Type uF} [Field F] {n : ℕ}

/-- The elementary inversion count agrees with the published Bruhat boundary rank. -/
theorem inversionLength_eq_permutationInversionCount (w : Equiv.Perm (Fin n)) :
    inversionLength w = permutationInversionCount n w := by
  rw [permutationInversionCount_eq_card_permutationInversions]
  rfl

/-- The inverse-permutation support convention agrees with the actual upper Bruhat cell. -/
theorem borelCell_eq_upperBruhatCell (w : Equiv.Perm (Fin n)) :
    borelCell F w = upperBruhatCell n F w⁻¹ := by
  ext g
  simp only [borelCell, DoubleCoset.mem_doubleCoset, upperBruhatCell,
    Set.mem_ofPred_eq, map_inv]
  constructor
  · rintro ⟨a, ha, b, hb, hg⟩
    exact ⟨a, ha, b, hb, hg⟩
  · rintro ⟨a, ha, b, hb, hg⟩
    exact ⟨a, ha, b, hb, hg⟩

/-- Every Borel Bruhat union is invariant under both upper triangular actions. -/
theorem bruhatSupport_borel_invariant (θ : Set (Equiv.Perm (Fin n))) :
    IsTwoSidedInvariant (upperTriangularSubgroup n F) (upperTriangularSubgroup n F)
      (bruhatSupport F θ) := by
  rintro g ⟨w, hw, hg⟩ a ha b hb
  obtain ⟨c, hc, d, hd, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
  exact ⟨w, hw, DoubleCoset.mem_doubleCoset.mpr
    ⟨a * c, mul_mem ha hc, d * b, mul_mem hd hb, by simp only [mul_assoc]⟩⟩

variable [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]

/-- A length-compatible Weyl tail is an open actual matrix support. Ties may be arbitrary. -/
theorem isOpen_bruhatSupport_of_length_upper
    (θ : Set (Equiv.Perm (Fin n)))
    (hθ : ∀ v ∈ θ, ∀ w, inversionLength v < inversionLength w → w ∈ θ) :
    IsOpen (bruhatSupport F θ) := by
  classical
  let E := {g : GeneralLinear n F | ∃ w : Equiv.Perm (Fin n),
    w ∉ θ ∧ g ∈ borelCell F w}
  have heq : E = ⋃ w : {w : Equiv.Perm (Fin n) // w ∉ θ}, borelCell F w.val := by
    ext g
    simp only [E, Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun ⟨w, hw, hg⟩ => ⟨⟨w, hw⟩, hg⟩,
      fun ⟨w, hg⟩ => ⟨w.val, w.property, hg⟩⟩
  have hclosed : IsClosed E := by
    apply isClosed_of_closure_subset
    rw [heq, closure_iUnion_of_finite]
    rintro g hg
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hg
    apply Set.mem_iUnion.mpr
    by_cases hgw : g ∈ borelCell F w.val
    · exact ⟨w, hgw⟩
    · rw [borelCell_eq_upperBruhatCell] at hw hgw
      obtain ⟨v, hv, hgv⟩ := upperBruhatBoundary F n w.val⁻¹ ⟨hw, hgw⟩
      have hinv (v : Equiv.Perm (Fin n)) : inversionLength v⁻¹ = inversionLength v :=
        inversionLength_symm v
      have hlen : inversionLength v⁻¹ < inversionLength w.val := by
        simpa only [← inversionLength_eq_permutationInversionCount,
          hinv] using hv
      have hvθ : v⁻¹ ∉ θ := fun hvθ => w.property (hθ v⁻¹ hvθ w.val hlen)
      refine ⟨⟨v⁻¹, hvθ⟩, ?_⟩
      simpa only [borelCell_eq_upperBruhatCell, inv_inv] using hgv
  have hcompl : bruhatSupport F θ = Eᶜ := by
    ext g
    constructor
    · rintro ⟨w, hw, hgw⟩ ⟨v, hv, hgv⟩
      have hEq : w⁻¹ = v⁻¹ := upperBruhatCell_index_eq
        ((borelCell_eq_upperBruhatCell (F := F) w) ▸ hgw)
        ((borelCell_eq_upperBruhatCell (F := F) v) ▸ hgv)
      exact hv ((inv_injective hEq) ▸ hw)
    · intro hg
      obtain ⟨w, hgw⟩ := exists_borelCell F g
      by_cases hw : w ∈ θ
      · exact ⟨w, hw, hgw⟩
      · exact False.elim (hg ⟨w, hw, hgw⟩)
  rw [hcompl]
  exact hclosed.isOpen_compl

end Bruhat

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)

/-- The compact integral representatives inside a closed standard parabolic. -/
def integralParabolicRepresentatives :
    letI := T.valuativeRel
    Set (GeneralLinear n F.Carrier) :=
  letI := T.valuativeRel
  (Iwasawa.integralRange (ValuativeRel.valuation F.Carrier) n :
    Set (GeneralLinear n F.Carrier)) ∩ B.parabolic F.Carrier

theorem isCompact_integralParabolicRepresentatives :
    letI := T.topology
    letI := T.valuativeRel
    IsCompact (integralParabolicRepresentatives T B) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  exact (Parabolic.isCompact_integralRange T n).inter_right (B.isClosed_parabolic F.Carrier)

/-- Iwasawa decomposition restricts to a parabolic, with a left Borel factor. -/
theorem parabolic_eq_borel_mul_integral :
    letI := T.valuativeRel
    ∀ b ∈ B.parabolic F.Carrier,
      ∃ a ∈ upperTriangularSubgroup n F.Carrier,
        ∃ k ∈ integralParabolicRepresentatives T B, b = a * k := by
  let := T.valuativeRel
  intro b hb
  obtain ⟨k, hk, hbk⟩ := Iwasawa.exists_mul_upperTriangular
    (ValuativeRel.valuation F.Carrier) n b
  have hUpper : b * k ∈ upperTriangularSubgroup n F.Carrier :=
    (mem_upperTriangularSubgroup_iff _).mpr hbk
  have hP : k ∈ B.parabolic F.Carrier := by
    have h := (B.parabolic F.Carrier).mul_mem ((B.parabolic F.Carrier).inv_mem hb)
      (B.upperTriangularSubgroup_le_parabolic F.Carrier hUpper)
    simpa only [inv_mul_cancel_left] using h
  exact ⟨b * k, hUpper, k⁻¹, ⟨inv_mem hk, inv_mem hP⟩, by simp only [mul_inv_cancel_right]⟩

/-- Inverting the restricted Iwasawa decomposition gives a right Borel factor. -/
theorem parabolic_eq_integral_mul_borel :
    letI := T.valuativeRel
    ∀ b ∈ B.parabolic F.Carrier,
      ∃ k ∈ integralParabolicRepresentatives T B,
        ∃ a ∈ upperTriangularSubgroup n F.Carrier, b = k * a := by
  let := T.valuativeRel
  intro b hb
  obtain ⟨a, ha, k, hk, heq⟩ := parabolic_eq_borel_mul_integral T B b⁻¹ (inv_mem hb)
  refine ⟨k⁻¹, ⟨inv_mem hk.1, inv_mem hk.2⟩, a⁻¹, inv_mem ha, ?_⟩
  simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv heq

/-- Taking the corrected two-sided support core preserves openness. -/
theorem isOpen_corrected_bruhatSupport
    (θ : Set (Equiv.Perm (Fin n))) :
    letI := T.topology
    IsOpen (bruhatSupport F.Carrier θ) →
      IsOpen (bruhatSupport F.Carrier (weylSupport B C θ)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup n
  intro hθ
  rw [← twoSidedCore_bruhatSupport F.Carrier B C θ]
  exact isOpen_twoSidedCore_of_compact_representatives
    (upperTriangularSubgroup n F.Carrier) (B.parabolic F.Carrier) (C.parabolic F.Carrier)
    (integralParabolicRepresentatives T B) (integralParabolicRepresentatives T C)
    (fun _ h => h.2) (fun _ h => h.2)
    (parabolic_eq_borel_mul_integral T B) (parabolic_eq_integral_mul_borel T C)
    (bruhatSupport F.Carrier θ) (bruhatSupport_borel_invariant θ)
    (isCompact_integralParabolicRepresentatives T B)
    (isCompact_integralParabolicRepresentatives T C) hθ

/-- Every length-compatible tail has open actual corrected support for all source/target shapes. -/
theorem isOpen_corrected_bruhatSupport_of_length_upper
    (θ : Set (Equiv.Perm (Fin n)))
    (hθ : ∀ v ∈ θ, ∀ w, inversionLength v < inversionLength w → w ∈ θ) :
    letI := T.topology
    IsOpen (bruhatSupport F.Carrier (weylSupport B C θ)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  exact isOpen_corrected_bruhatSupport T B C θ
    (isOpen_bruhatSupport_of_length_upper θ hθ)

/-- The corresponding corrected subset of the actual inducing quotient is open. -/
theorem isOpen_correctedQuotientSupport_of_length_upper
    (θ : Set (Equiv.Perm (Fin n)))
    (hθ : ∀ v ∈ θ, ∀ w, inversionLength v < inversionLength w → w ∈ θ) :
    letI := T.topology
    IsOpen (correctedQuotientSupport F.Carrier B C θ) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen (Induction.quotientMap (B.parabolic F.Carrier) ⁻¹'
    correctedQuotientSupport F.Carrier B C θ)
  have heq : Induction.quotientMap (B.parabolic F.Carrier) ⁻¹'
      correctedQuotientSupport F.Carrier B C θ =
      bruhatSupport F.Carrier (weylSupport B C θ) := by
    ext g
    exact quotientMap_mem_correctedQuotientSupport_iff F.Carrier B C θ g
  rw [heq]
  exact isOpen_corrected_bruhatSupport_of_length_upper T B C θ hθ

end Padic
end Langlands.Aubert.Support
