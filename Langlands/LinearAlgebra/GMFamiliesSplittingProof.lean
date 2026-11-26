import Langlands.LinearAlgebra.GMFamiliesStatement
import Langlands.LinearAlgebra.GMFamiliesFaceTheta

/-! # Arthur's product splitting formula -/

noncomputable section

open Classical

universe u

namespace Langlands.GMFamily

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {R : Finset E} {a : Submodule ℝ E}

private def splitWeight (P Q Q' : Finset E) (Λ : StrongDual ℝ a) : ℂ :=
  (-1 : ℂ) ^ (Module.finrank ℝ (faceSpace R a Q) - Module.finrank ℝ (faceSpace R a Q')) *
    (theta a (P ∩ leviRoots R Q) Λ)⁻¹ *
    (thetaHat (Q ∩ leviRoots R Q') (restrictParam a (faceSpace R a Q) Λ))⁻¹

private theorem isEmpty_simpleRoots_empty (b : Submodule ℝ E) : IsEmpty ↥(simpleRoots b (∅ : Finset E)) := by
  have h : simpleRoots b (∅ : Finset E) = ∅ := by simp [simpleRoots, restrictedRoots]
  rw [h]
  exact ⟨fun i => Finset.notMem_empty _ i.property⟩

private theorem theta_empty (b : Submodule ℝ E) (Λ : StrongDual ℝ b) :
    theta b (∅ : Finset E) Λ = 1 := by
  have _ := isEmpty_simpleRoots_empty b
  exact thetaOf_isEmpty b _ Λ

private theorem thetaHat_empty (b : Submodule ℝ E) (Λ : StrongDual ℝ b) :
    thetaHat (∅ : Finset E) Λ = 1 := by
  have _ := isEmpty_simpleRoots_empty b
  rw [thetaHat_eq_thetaOf_gramDual, thetaOf_isEmpty]

private theorem splitWeight_self (P : Finset E) (Λ : StrongDual ℝ a) :
    splitWeight (R := R) P P P Λ = 1 := by
  have he : P ∩ leviRoots R P = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun r hr =>
    ((Finset.mem_filter.mp (Finset.mem_inter.mp hr).2).2.1) (Finset.mem_inter.mp hr).1
  simp [splitWeight, he, theta_empty, thetaHat_empty]

private theorem restrictParam_self (Λ : StrongDual ℝ a) : restrictParam a a Λ = Λ := by
  ext v
  rw [restrictParam_apply_inclusion le_rfl]
  rfl

private def intervalSubset {ι : Type*} [DecidableEq ι] (I J : Finset ι) : Finset I :=
  Finset.univ.filter fun i => i.1 ∈ J

@[simp] private theorem mem_intervalSubset {ι : Type*} [DecidableEq ι] {I J : Finset ι} (i : I) :
    i ∈ intervalSubset I J ↔ i.1 ∈ J := by simp [intervalSubset]

private def intervalLeftEquiv {ι : Type*} [DecidableEq ι] {I J : Finset ι} (h : J ⊆ I) :
    intervalSubset I J ≃ J where
  toFun := fun i => ⟨i.1.1, (mem_intervalSubset i.1).mp i.property⟩
  invFun := fun i => ⟨⟨i.1, h i.property⟩, (mem_intervalSubset _).mpr i.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

private def intervalRightEquiv {ι : Type*} [DecidableEq ι] (I J : Finset ι) :
    {i : I // i ∉ intervalSubset I J} ≃ ↥(I \ J) where
  toFun := fun i => ⟨i.1.1, Finset.mem_sdiff.mpr ⟨i.1.property, fun h => i.property ((mem_intervalSubset i.1).mpr h)⟩⟩
  invFun := fun i => ⟨⟨i.1, (Finset.mem_sdiff.mp i.property).1⟩,
    fun h => (Finset.mem_sdiff.mp i.property).2
      ((mem_intervalSubset (I := I) (J := J) ⟨i.1, (Finset.mem_sdiff.mp i.property).1⟩).mp h)⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

private def complementTheta {ι : Type*} [Fintype ι] (v : ι → a) (J : Finset ι)
    (Λ : StrongDual ℝ a) : ℂ :=
  thetaOf a (fun i : {i // i ∉ J} => gramDual v i) Λ

omit [FiniteDimensional ℝ E] in
private theorem thetaOf_same_fintype {ι : Type*} (v : ι → a) (Λ : StrongDual ℝ a)
    (f₁ f₂ : Fintype ι) : @thetaOf E _ _ a ι f₁ v Λ = @thetaOf E _ _ a ι f₂ v Λ :=
  congrArg (fun f => @thetaOf E _ _ a ι f v Λ) (Subsingleton.elim _ _)

private def indexedWeight {ι : Type*} [Fintype ι] (v : ι → a) (J : Finset ι) (Λ : StrongDual ℝ a) : ℂ :=
  (-1 : ℂ) ^ (Fintype.card ι - J.card) * (thetaOf a (fun i : J => v i) Λ)⁻¹ *
    (complementTheta v J Λ)⁻¹

set_option maxHeartbeats 550000 in
private theorem splitWeight_eq_indexedWeight (hR : IsRootSet R) (ha : IsLeviSpace R a) {P Q Q' : Finset E}
    (hP : P ∈ parabolics R a) (hQ : Q ∈ faces R a) (hQ' : Q' ∈ faces R a) (hQP : Q ⊆ P) (hQQ' : Q' ⊆ Q)
    (Λ : StrongDual ℝ a) :
    splitWeight (R := R) P Q Q' Λ = indexedWeight (fun i : faceIndices a P Q' => (i.1 : a))
      (intervalSubset (faceIndices a P Q') (faceIndices a P Q)) Λ := by
  let I := faceIndices a P Q'
  let J := faceIndices a P Q
  let K := intervalSubset I J
  let v : I → a := fun i => (i.1 : a)
  let e₁ : K ≃ J := intervalLeftEquiv (faceIndices_subset hQQ')
  let e₂ : {i : I // i ∉ K} ≃ ↥(I \ J) := intervalRightEquiv I J
  have hc : K.card = J.card := by simpa only [Fintype.card_coe] using Fintype.card_congr e₁
  have hd := finrank_faceSpace_add_card hR ha hP hQ hQP
  have hd' := finrank_faceSpace_add_card hR ha hP hQ' (hQQ'.trans hQP)
  have hdim : Module.finrank ℝ (faceSpace R a Q) - Module.finrank ℝ (faceSpace R a Q') =
      Fintype.card I - K.card := by
    rw [Fintype.card_coe, hc]
    change Module.finrank ℝ (faceSpace R a Q) + J.card = Module.finrank ℝ a at hd
    change Module.finrank ℝ (faceSpace R a Q') + I.card = Module.finrank ℝ a at hd'
    omega
  have hθ : theta a (P ∩ leviRoots R Q) Λ = thetaOf a (fun i : K => v i) Λ :=
    (theta_inter_leviRoots hR hP hQ hQP Λ).trans
      (thetaOf_reindex a e₁ (fun i : J => (i.1 : a)) Λ).symm
  have hθ' : thetaHat (Q ∩ leviRoots R Q') (restrictParam a (faceSpace R a Q) Λ) =
      thetaOf a (fun i : {i : I // i ∉ K} => gramDual v i) Λ :=
    (thetaHat_face_leviRoots hR ha hP hQ hQ' hQP hQQ' Λ).trans
      (thetaOf_reindex a e₂ (fun i : ↥(I \ J) => gramDual v ⟨i.1, (Finset.mem_sdiff.mp i.property).1⟩) Λ).symm
  have hθ'' : thetaHat (Q ∩ leviRoots R Q') (restrictParam a (faceSpace R a Q) Λ) = complementTheta v K Λ := by
    refine hθ'.trans ?_
    unfold complementTheta
    exact thetaOf_same_fintype (fun i : {i : I // i ∉ K} => gramDual v i) Λ _ _
  change splitWeight (R := R) P Q Q' Λ = indexedWeight v K Λ
  exact congrArg₂ (· * ·)
    (congrArg₂ (fun n z => (-1 : ℂ) ^ n * z⁻¹) hdim hθ) (congrArg Inv.inv hθ'')

set_option maxHeartbeats 500000 in
private theorem sum_splitWeight (hR : IsRootSet R) (ha : IsLeviSpace R a) {P Q' : Finset E}
    (hP : P ∈ parabolics R a) (hQ' : Q' ∈ faces R a) (hQ'P : Q' ⊆ P)
    (Λ : StrongDual ℝ a)
    (hx : ∀ i : faceIndices a P Q', Λ (i.1 : a) ≠ 0)
    (hy : ∀ i : faceIndices a P Q', Λ (gramDual (fun j : faceIndices a P Q' => (j.1 : a)) i) ≠ 0) :
    (∑ Q ∈ (faces R a).filter (fun Q => Q ⊆ P ∧ Q' ⊆ Q), splitWeight (R := R) P Q Q' Λ) =
      if Q' = P then 1 else 0 := by
  by_cases hself : Q' = P
  · subst Q'
    have he : (faces R a).filter (fun Q => Q ⊆ P ∧ P ⊆ Q) = {P} := by
      ext Q
      simp only [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun h => Finset.Subset.antisymm h.2.1 h.2.2, fun h => h.symm ▸ ⟨hQ', le_rfl, le_rfl⟩⟩
    simp [he, splitWeight_self]
  let I := faceIndices a P Q'
  let U := (faces R a).filter (fun Q => Q ⊆ P ∧ Q' ⊆ Q)
  let indices (Q : Finset E) : Finset I := intervalSubset I (faceIndices a P Q)
  have hmem (Q : Finset E) (i : I) : i ∈ indices Q ↔ i.1 ∈ faceIndices a P Q := mem_intervalSubset i
  let v : I → a := fun i => (i.1 : a)
  let weight (J : Finset I) : ℂ := indexedWeight v J Λ
  have hPface := parabolics_subset_faces R a hP
  have hInonempty : I.Nonempty := by
    by_contra h
    have h0 : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hsub : faceIndices a P Q' ⊆ faceIndices a P P := by
      change I ⊆ _
      rw [h0]
      exact Finset.empty_subset _
    exact hself (Finset.Subset.antisymm hQ'P ((faceIndices_subset_iff hR hP hQ' hPface hQ'P le_rfl).mp hsub))
  let _ : Nonempty I := ⟨⟨hInonempty.choose, hInonempty.choose_spec⟩⟩
  have hdata (Q : Finset E) (hQ : Q ∈ U) : Q ∈ faces R a ∧ Q ⊆ P ∧ Q' ⊆ Q := Finset.mem_filter.mp hQ
  have hinj (Q₁ Q₂ : Finset E) (h₁ : Q₁ ∈ U) (h₂ : Q₂ ∈ U) (he : indices Q₁ = indices Q₂) : Q₁ = Q₂ := by
    obtain ⟨h₁f, h₁p, h₁q⟩ := hdata Q₁ h₁
    obtain ⟨h₂f, h₂p, h₂q⟩ := hdata Q₂ h₂
    have hs (A B : Finset E) (hA : Q' ⊆ A) (he' : indices A = indices B) :
        faceIndices a P A ⊆ faceIndices a P B := by
      intro i hi
      let j : I := ⟨i, faceIndices_subset hA hi⟩
      have hj := (hmem A j).mpr hi
      rw [he'] at hj
      exact (hmem B j).mp hj
    apply Finset.Subset.antisymm
    · exact (faceIndices_subset_iff hR hP h₂f h₁f h₂p h₁p).mp (hs _ _ h₂q he.symm)
    · exact (faceIndices_subset_iff hR hP h₁f h₂f h₁p h₂p).mp (hs _ _ h₁q he)
  have hsurj (J : Finset I) : ∃ Q ∈ U, indices Q = J := by
    let K := J.image (fun i : I => i.1)
    obtain ⟨Q, hf, hqp, he⟩ := exists_faceIndices hR ha hP K
    have hki : K ⊆ I := by
      intro r hr
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
      exact i.property
    have hinc : Q' ⊆ Q := (faceIndices_subset_iff hR hP hf hQ' hqp hQ'P).mp (he.symm ▸ hki)
    refine ⟨Q, Finset.mem_filter.mpr ⟨hf, hqp, hinc⟩, ?_⟩
    ext i
    rw [hmem, he, Finset.mem_image]
    exact ⟨fun ⟨j, hj, hj'⟩ => (Subtype.ext hj' : j = i) ▸ hj, fun hj => ⟨i, hj, rfl⟩⟩
  have hweight (Q : Finset E) (hQ : Q ∈ U) : splitWeight (R := R) P Q Q' Λ = weight (indices Q) := by
    obtain ⟨hf, hqp, hinc⟩ := hdata Q hQ
    exact splitWeight_eq_indexedWeight hR ha hP hf hQ' hqp hinc Λ
  rw [ite_eq_right hself]
  calc
    ∑ Q ∈ U, splitWeight (R := R) P Q Q' Λ = ∑ J : Finset I, weight J := by
      exact Finset.sum_bij (fun Q _ => indices Q) (fun _ _ => Finset.mem_univ _)
        (fun Q₁ h₁ Q₂ h₂ he => hinj Q₁ Q₂ h₁ h₂ he)
        (fun J _ => by obtain ⟨Q, hQ, he⟩ := hsurj J; exact ⟨Q, hQ, he⟩) hweight
    _ = 0 := alternating_thetaOf_inv a v ((simpleRoots_independent hR ha hP).comp _ Subtype.val_injective) Λ hx hy

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem sum_filter_chains (F : Finset (Finset E)) (P : Finset E) (f : Finset E → Finset E → ℂ) :
    (∑ Q ∈ F.filter (· ⊆ P), ∑ Q' ∈ F.filter (· ⊆ Q), f Q Q') =
      ∑ Q' ∈ F.filter (· ⊆ P), ∑ Q ∈ F.filter (fun Q => Q ⊆ P ∧ Q' ⊆ Q), f Q Q' := by
  simp only [Finset.sum_filter]
  calc
    _ = ∑ Q ∈ F, ∑ Q' ∈ F, if Q ⊆ P ∧ Q' ⊆ Q then f Q Q' else 0 := by
      apply Finset.sum_congr rfl
      intro Q _
      by_cases h : Q ⊆ P <;> simp [h]
    _ = ∑ Q' ∈ F, ∑ Q ∈ F, if Q ⊆ P ∧ Q' ⊆ Q then f Q Q' else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Q' _
      by_cases h : Q' ⊆ P
      · simp [h]
      · have hn (Q : Finset E) : ¬ (Q ⊆ P ∧ Q' ⊆ Q) := fun hh => h (hh.2.trans hh.1)
        simp [h, hn]

set_option maxHeartbeats 350000 in
private theorem dPrime_inversion (hR : IsRootSet R) (ha : IsLeviSpace R a) {P : Finset E}
    (hP : P ∈ parabolics R a) (d : Finset E → StrongDual ℝ a → ℂ) (Λ : StrongDual ℝ a)
    (hx : ∀ Q' ∈ faces R a, ∀ i : faceIndices a P Q', Λ (i.1 : a) ≠ 0)
    (hy : ∀ Q' ∈ faces R a, ∀ i : faceIndices a P Q',
      Λ (gramDual (fun j : faceIndices a P Q' => (j.1 : a)) i) ≠ 0) :
    (∑ Q ∈ (faces R a).filter (· ⊆ P),
      (theta a (P ∩ leviRoots R Q) Λ)⁻¹ * dPrime R a d Q (paramProj a (faceSpace R a Q) Λ)) =
      d P Λ * (theta a P Λ)⁻¹ := by
  let F := faces R a
  let m (Q' : Finset E) := famRestrict R a d Q' Λ *
    (theta (faceSpace R a Q') Q' (restrictParam a (faceSpace R a Q') Λ))⁻¹
  calc
    _ = ∑ Q ∈ F.filter (· ⊆ P), ∑ Q' ∈ F.filter (· ⊆ Q), m Q' * splitWeight (R := R) P Q Q' Λ := by
      apply Finset.sum_congr rfl
      intro Q _
      rw [dPrime, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q' hQ'
      have hinc := (Finset.mem_filter.mp hQ').2
      have hle : faceSpace R a Q' ≤ faceSpace R a Q := faceSpace_mono hinc
      rw [famRestrict_paramProj Λ d hinc, restrictParam_paramProj (faceSpace_le Q) hle,
        restrictParam_paramProj (faceSpace_le Q) (le_refl _)]
      dsimp [m, splitWeight]
      ring
    _ = ∑ Q' ∈ F.filter (· ⊆ P), ∑ Q ∈ F.filter (fun Q => Q ⊆ P ∧ Q' ⊆ Q),
          m Q' * splitWeight (R := R) P Q Q' Λ := sum_filter_chains F P _
    _ = ∑ Q' ∈ F.filter (· ⊆ P), (if Q' = P then m P else 0) := by
      apply Finset.sum_congr rfl
      intro Q' hQ'
      obtain ⟨hf, hp⟩ := Finset.mem_filter.mp hQ'
      rw [← Finset.mul_sum, sum_splitWeight hR ha hP hf hp Λ (hx Q' hf) (hy Q' hf)]
      by_cases h : Q' = P <;> simp [h]
    _ = m P := by simp [F, parabolics_subset_faces R a hP]
    _ = _ := by
      dsimp only [m]
      rw [famRestrict_parabolic hR hP, faceSpace_parabolic hR hP, restrictParam_self]

private def splittingExceptionalVectors (R : Finset E) (a : Submodule ℝ E) : Finset a :=
  ((parabolics R a).biUnion fun P => simpleRoots a P ∪
    (faces R a).biUnion (fun Q => Finset.univ.image (gramDual (fun j : faceIndices a P Q => (j.1 : a))))).erase 0

set_option maxHeartbeats 350000 in
/-- Arthur's product splitting formula for the defining expressions at generic parameters. -/
theorem splittingFormula : SplittingFormulaStatement.{u} := by
  intro E _ _ _ R a hR ha c d _ _
  refine ⟨splittingExceptionalVectors R a, Finset.notMem_erase _ _, fun Λ hΛ => ?_⟩
  have hr (P : Finset E) (hP : P ∈ parabolics R a) (Q : Finset E) (i : faceIndices a P Q) :
      Λ (i.1 : a) ≠ 0 := by
    apply hΛ
    unfold splittingExceptionalVectors
    exact Finset.mem_erase.mpr ⟨(simpleRoots_independent hR ha hP).ne_zero i.1,
      Finset.mem_biUnion.mpr ⟨P, hP, Finset.mem_union_left _ i.1.property⟩⟩
  have hd (P : Finset E) (hP : P ∈ parabolics R a) (Q : Finset E) (hQ : Q ∈ faces R a)
      (i : faceIndices a P Q) : Λ (gramDual (fun j : faceIndices a P Q => (j.1 : a)) i) ≠ 0 := by
    apply hΛ
    unfold splittingExceptionalVectors
    refine Finset.mem_erase.mpr ⟨gramDual_ne_zero _ ((simpleRoots_independent hR ha hP).comp _ Subtype.val_injective) i, ?_⟩
    exact Finset.mem_biUnion.mpr ⟨P, hP, Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨Q, hQ, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)⟩
  symm
  calc
    _ = ∑ Q ∈ faces R a, ∑ P ∈ (parabolics R a).filter (Q ⊆ ·),
        c P Λ * (theta a (P ∩ leviRoots R Q) Λ)⁻¹ * dPrime R a d Q (paramProj a (faceSpace R a Q) Λ) := by
      apply Finset.sum_congr rfl
      intro Q hQ
      rw [cQM_eq_sum_chambers hR hQ, Finset.sum_mul]
    _ = ∑ P ∈ parabolics R a, ∑ Q ∈ (faces R a).filter (· ⊆ P),
        c P Λ * (theta a (P ∩ leviRoots R Q) Λ)⁻¹ * dPrime R a d Q (paramProj a (faceSpace R a Q) Λ) := by
      simp only [Finset.sum_filter]
      exact Finset.sum_comm
    _ = cM R a (familyMul a c d) Λ := by
      unfold cM familyMul
      apply Finset.sum_congr rfl
      intro P hP
      simp_rw [mul_assoc, ← Finset.mul_sum]
      rw [dPrime_inversion hR ha hP d Λ (fun Q _ => hr P hP Q) (hd P hP), ← mul_assoc]

end Langlands.GMFamily
