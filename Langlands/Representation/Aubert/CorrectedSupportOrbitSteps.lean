import Langlands.Representation.Aubert.CorrectedSupportTopology
import Langlands.Representation.Geometric.OpenSupportOrbitQuotient
import Langlands.Representation.Geometric.OrbitRepresentatives

/-! Actual single-orbit differences of corrected Weyl support steps. -/

noncomputable section

namespace Langlands.Aubert.Support

open GeneralLinear Geometric

universe uF

variable (F : Type uF) [Field F] {n : ℕ} (B C : BlockShape n)

private theorem mem_doubleCoset_iff_mk_eq {G : Type*} [Group G]
    (H K : Subgroup G) (a b : G) :
    b ∈ DoubleCoset.doubleCoset a H K ↔ DoubleCoset.mk H K a = DoubleCoset.mk H K b := by
  rw [DoubleCoset.mem_doubleCoset, DoubleCoset.eq]
  rfl

/-- The actual Borel cells indexed by distinct Weyl elements are disjoint. -/
theorem borelCell_index_eq {v w : Equiv.Perm (Fin n)} {g : GeneralLinear n F}
    (hv : g ∈ borelCell F v) (hw : g ∈ borelCell F w) : v = w := by
  apply inverse_permutation_borelCell_injective F
  exact DoubleCoset.mk_eq_of_doubleCoset_eq
    ((DoubleCoset.doubleCoset_eq_of_mem hv).symm.trans
      (DoubleCoset.doubleCoset_eq_of_mem hw))

/-- Passing from Weyl subsets to actual matrix Bruhat unions preserves difference. -/
theorem bruhatSupport_sdiff (θ η : Set (Equiv.Perm (Fin n))) :
    bruhatSupport F (θ \ η) = bruhatSupport F θ \ bruhatSupport F η := by
  ext g
  constructor
  · rintro ⟨w, ⟨hwθ, hwη⟩, hgw⟩
    refine ⟨⟨w, hwθ, hgw⟩, ?_⟩
    rintro ⟨v, hv, hgv⟩
    exact hwη ((borelCell_index_eq F hgv hgw) ▸ hv)
  · rintro ⟨⟨w, hw, hgw⟩, hgη⟩
    exact ⟨w, ⟨hw, fun hwη => hgη ⟨w, hwη, hgw⟩⟩, hgw⟩

/-- A block Weyl double coset indexes exactly the actual parabolic matrix double coset. -/
theorem bruhatSupport_blockDoubleCoset (w : Equiv.Perm (Fin n)) :
    bruhatSupport F (DoubleCoset.doubleCoset w (blockWeyl C) (blockWeyl B)) =
      DoubleCoset.doubleCoset (permutation n F w)⁻¹ (B.parabolic F) (C.parabolic F) := by
  ext g
  constructor
  · rintro ⟨v, hv, hgv⟩
    apply (mem_doubleCoset_iff_mk_eq _ _ _ _).mpr
    have hW := DoubleCoset.mk_eq_of_doubleCoset_eq (DoubleCoset.doubleCoset_eq_of_mem hv)
    have hM := inverse_permutation_doubleCoset_eq_of_weyl_eq F B C hW
    exact hM.symm.trans ((mem_doubleCoset_iff_mk_eq _ _ _ _).mp
      (borelCell_subset_parabolicCell F B C v hgv))
  · intro hg
    obtain ⟨v, hgv⟩ := exists_borelCell F g
    refine ⟨v, ?_, hgv⟩
    apply (mem_doubleCoset_iff_mk_eq _ _ _ _).mpr
    have hvM := (mem_doubleCoset_iff_mk_eq _ _ _ _).mp
      (borelCell_subset_parabolicCell F B C v hgv)
    have hwM := (mem_doubleCoset_iff_mk_eq _ _ _ _).mp hg
    exact (weyl_doubleCoset_eq_of_inverse_permutation_eq B C (hvM.trans hwM.symm)).symm

/-- An active singleton support step has exactly one actual parabolic double coset. -/
theorem corrected_bruhatSupport_singleton_step
    (θ : Set (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n))
    (hw : w ∈ weylSupport B C θ) :
    bruhatSupport F (weylSupport B C θ) \
        bruhatSupport F (weylSupport B C (θ \ {w})) =
      DoubleCoset.doubleCoset (permutation n F w)⁻¹ (B.parabolic F) (C.parabolic F) := by
  rw [← bruhatSupport_sdiff, weylSupport_singleton_step B C θ w hw,
    bruhatSupport_blockDoubleCoset]

/-- On the actual inducing quotient, the singleton step is exactly the actual orbit. -/
theorem correctedQuotientSupport_singleton_step
    (θ : Set (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n))
    (hw : w ∈ weylSupport B C θ) :
    correctedQuotientSupport F B C θ \ correctedQuotientSupport F B C (θ \ {w}) =
      cosetOrbit (B.parabolic F) (C.parabolic F) (permutation n F w) := by
  ext x
  induction x using Quotient.inductionOn with
  | h g =>
    change (Induction.quotientMap (B.parabolic F) g ∈ correctedQuotientSupport F B C θ ∧
        Induction.quotientMap (B.parabolic F) g ∉ correctedQuotientSupport F B C (θ \ {w})) ↔ _
    rw [quotientMap_mem_correctedQuotientSupport_iff,
      quotientMap_mem_correctedQuotientSupport_iff]
    change g ∈ (bruhatSupport F (weylSupport B C θ) \
      bruhatSupport F (weylSupport B C (θ \ {w}))) ↔ _
    rw [corrected_bruhatSupport_singleton_step F B C θ w hw]
    exact (mem_doubleCoset_iff_mk_eq _ _ _ _).trans
      (quotientMap_mem_cosetOrbit_iff (B.parabolic F) (C.parabolic F)
        (permutation n F w) g).symm

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)

/-- The concrete corrected singleton support step, as actual open orbit support data. -/
def correctedOpenOrbitSupportPair
    (θ : Set (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n))
    (hθ : ∀ v ∈ θ, ∀ z, inversionLength v < inversionLength z → z ∈ θ)
    (hLower : ∀ v ∈ θ \ {w}, ∀ z, inversionLength v < inversionLength z → z ∈ θ \ {w})
    (hw : w ∈ weylSupport B C θ) :
    letI := T.topology
    OpenOrbitSupportPair (B.parabolic F.Carrier) (C.parabolic F.Carrier)
      (permutation n F.Carrier w) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  exact {
    lower := correctedQuotientSupport F.Carrier B C (θ \ {w})
    upper := correctedQuotientSupport F.Carrier B C θ
    lower_invariant := correctedQuotientSupport_right_invariant F.Carrier B C (θ \ {w})
    upper_invariant := correctedQuotientSupport_right_invariant F.Carrier B C θ
    lower_open := isOpen_correctedQuotientSupport_of_length_upper T B C (θ \ {w}) hLower
    upper_open := isOpen_correctedQuotientSupport_of_length_upper T B C θ hθ
    lower_subset_upper := correctedQuotientSupport_mono F.Carrier B C Set.sdiff_subset
    difference := correctedQuotientSupport_singleton_step F.Carrier B C θ w hw }

end Padic
end Langlands.Aubert.Support
