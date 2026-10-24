import Langlands.Galois.Local.InertiaDisjointRamificationStatement
import Langlands.Galois.Local.UnramifiedCriterionProof

/-! # Total ramification from disjointness with the actual inertia fixed field -/

noncomputable section

namespace Langlands.PadicField

open Langlands.Weil.Local

universe u

/-- Disjointness with the actual inertia fixed field forces total ramification,
including for finite intermediate extensions which are not Galois. -/
theorem inertiaDisjointTotallyRamified : InertiaDisjointTotallyRamified.{u} := by
  intro p _ F D
  dsimp only
  intro hdisj
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let I := F.absoluteInertia F.canonicalTopologicalData
  let T : Subgroup (Field.absoluteGaloisGroup F.Carrier) := D.field.fixingSubgroup
  let H := T ⊔ I
  have hHopen : IsOpen (H : Set (Field.absoluteGaloisGroup F.Carrier)) :=
    Subgroup.isOpen_mono le_sup_left D.field.fixingSubgroup_isOpen
  have hfixed : IntermediateField.fixedField H = ⊥ := by
    apply le_bot_iff.mp
    rw [← hdisj.inf_eq_bot]
    apply le_inf
    · calc IntermediateField.fixedField H
          ≤ IntermediateField.fixedField D.field.fixingSubgroup :=
            IntermediateField.fixedField_le le_sup_left
        _ = D.field := InfiniteGalois.fixedField_fixingSubgroup D.field
    · exact IntermediateField.fixedField_le le_sup_right
  have hH : H = ⊤ := by
    let HC : ClosedSubgroup (Field.absoluteGaloisGroup F.Carrier) :=
      ⟨H, (show OpenSubgroup (Field.absoluteGaloisGroup F.Carrier) from ⟨H, hHopen⟩).isClosed⟩
    have h := InfiniteGalois.fixingSubgroup_fixedField HC
    change (IntermediateField.fixedField H).fixingSubgroup = H at h
    rw [hfixed, IntermediateField.fixingSubgroup_bot] at h
    exact h.symm
  let E := D.asPadicField (p := p)
  let f := intermediateEmbedding F D
  let S := (extensionGaloisMap F E f).toMonoidHom.range
  let c := intermediateClosureCorrection F D
  have hS : S.map (MulAut.conj c).toMonoidHom = T := by
    rw [show S = (extensionIntermediateField F E f).fixingSubgroup from
      extensionGaloisMap_range F E f]
    ext τ
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact (intermediateClosureCorrection_conj_mem F D σ).mpr hσ
    · intro hτ
      obtain ⟨σ, rfl⟩ := (MulAut.conj c).surjective τ
      exact ⟨σ, (intermediateClosureCorrection_conj_mem F D σ).mp hτ, rfl⟩
  have hI : I.map (MulAut.conj c).toMonoidHom = I :=
    Subgroup.Normal.map_conj_eq I c
  have hSI : S ⊔ I = ⊤ := by
    apply top_unique
    intro τ _
    have hτ : (MulAut.conj c) τ ∈ (S ⊔ I).map (MulAut.conj c).toMonoidHom := by
      rw [Subgroup.map_sup, hS, hI]
      change (MulAut.conj c) τ ∈ H
      rw [hH]
      exact Subgroup.mem_top _
    obtain ⟨σ, hσ, heq⟩ := hτ
    exact (MulAut.conj c).injective heq ▸ hσ
  have hres : extensionResidueDegree F E f = 1 := by
    rw [← extensionGaloisMap_range_sup_absoluteInertia_index F E f]
    change (S ⊔ I).index = 1
    rw [hSI, Subgroup.index_top]
  have hdegree : extensionDegree F E f = Module.finrank F.Carrier D.field := by
    have h : extensionAlgebra F E f = (inferInstance : Algebra F.Carrier D.field) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    unfold extensionDegree
    rw [h]
  have hram := ramificationIndex_mul_extensionResidueDegree F E f
  rw [hres, mul_one, hdegree] at hram
  exact hram

end Langlands.PadicField
