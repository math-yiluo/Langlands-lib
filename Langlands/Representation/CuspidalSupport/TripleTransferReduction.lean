import Langlands.Representation.CuspidalSupport.UniformTripleTransferStatement
import Langlands.Representation.CuspidalSupport.TripleMergedTensor
import Langlands.Representation.Classification.RepeatedCuspidalTripleJacquetTransferStatement

/-! Rank transport and the ambient reduction to the isolated local triple input. -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The rank-aware repeated-factor transfer property for any actual shape
having exactly three slots. -/
def ThreeSlotRepeatedCuspidalTransfer {r : ℕ} (D : BlockShape r) (hD : D.length = 3) :
    Prop :=
  letI := T.topology
  ∀ (E : SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (C : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := D.size i)),
    E.IsIrreducible → E.IsAdmissible → E.HasFiniteLength →
    SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject (fun i => (C i).obj))
      ((T.normalizedJacquetFunctor D).obj E) →
    let a : Fin D.length := ⟨0, by omega⟩
    let b : Fin D.length := ⟨1, by omega⟩
    let c : Fin D.length := ⟨2, by omega⟩
    ((⟨D.size a, (C a).isoClass⟩ :
      Σ d, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) =
        ⟨D.size b, T.supercuspidalClassRealPowerTwist (D.size b) 1 (C b).isoClass⟩) →
    (((⟨D.size c, (C c).isoClass⟩ :
        Σ d, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) =
          ⟨D.size b, (C b).isoClass⟩) →
      SmoothRep.IsSubquotient
        (FiniteTensor.externalSmoothObject (fun i => (C (D.adjacentSwap 0 (by omega) i)).obj))
        ((T.normalizedJacquetFunctor (D.permute (D.adjacentSwap 0 (by omega)))).obj E)) ∧
    (((⟨D.size c, (C c).isoClass⟩ :
        Σ d, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) =
          ⟨D.size a, (C a).isoClass⟩) →
      SmoothRep.IsSubquotient
        (FiniteTensor.externalSmoothObject (fun i => (C (D.adjacentSwap 1 (by omega) i)).obj))
        ((T.normalizedJacquetFunctor (D.permute (D.adjacentSwap 1 (by omega)))).obj E) ∨
      SmoothRep.IsSubquotient
        (FiniteTensor.externalSmoothObject (fun i => (C (D.adjacentSwap 0 (by omega) i)).obj))
        ((T.normalizedJacquetFunctor (D.permute (D.adjacentSwap 0 (by omega)))).obj E))

private theorem subquotient_external_shape_transport {r : ℕ} (D D' : BlockShape r)
    (hD : D = D') :
    letI := T.topology
    ∀ (C : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (D.size i) F.Carrier))
      (C' : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (D'.size i) F.Carrier)),
      HEq C C' →
      ∀ E : SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier),
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject C')
        ((T.normalizedJacquetFunctor D').obj E) →
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject C)
        ((T.normalizedJacquetFunctor D).obj E) := by
  let := T.topology
  subst D'
  intro C C' hC E h
  cases hC
  exact h

private theorem threeSlotTransfer_of_constant
    (H : UniformRepeatedCuspidalTripleJacquetTransfer.{uF, uV} F T)
    {r : ℕ} (D : BlockShape r) (hD : D.length = 3)
    (d : ℕ) (hd : 0 < d) (hs : ∀ i, D.size i = d) :
    ThreeSlotRepeatedCuspidalTransfer.{uF, uV} F T D hD := by
  let := T.topology
  have hr : r = d + (d + d) := by
    rw [← D.sum_eq]
    simp_rw [hs]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hD, smul_eq_mul]
    omega
  subst r
  have hshape : D = threeBlocks d d d hd hd hd := by
    apply BlockShape.ext_of_size hD
    intro i
    rw [hs i]
    have hi := (Fin.cast hD i).isLt
    generalize Fin.cast hD i = k
    fin_cases k <;> rfl
  subst D
  dsimp only [ThreeSlotRepeatedCuspidalTransfer]
  intro E C hEi hEa hEf hOcc hAB
  have hfamily :
      (fun i => (C i).obj) =
        threeBlockSmoothFamily (C 0).obj (C 1).obj (C 2).obj := by
    funext i
    fin_cases i <;> rfl
  have hOcc' :
      SmoothRep.IsSubquotient (uniformTripleTensor F T hd (C 0).obj (C 1).obj (C 2).obj)
        ((T.normalizedJacquetFunctor (threeBlocks d d d hd hd hd)).obj E) := by
    exact subquotient_external_shape_transport F T _ _ rfl _ _
      (heq_of_eq hfamily.symm) E hOcc
  have hLocal := H d hd E (C 0) (C 1) (C 2) hEi hEa hEf hOcc'
    (sigma_mk_injective hAB)
  have habShape :
      (threeBlocks d d d hd hd hd).permute
        ((threeBlocks d d d hd hd hd).adjacentSwap 0 (by omega)) =
      threeBlocks d d d hd hd hd := by
    apply BlockShape.ext_of_size
      (B₁ := (threeBlocks d d d hd hd hd).permute
        ((threeBlocks d d d hd hd hd).adjacentSwap 0 (by omega)))
      (B₂ := threeBlocks d d d hd hd hd) rfl
    intro i
    fin_cases i <;> rfl
  have hbcShape :
      (threeBlocks d d d hd hd hd).permute
        ((threeBlocks d d d hd hd hd).adjacentSwap 1 (by omega)) =
      threeBlocks d d d hd hd hd := by
    apply BlockShape.ext_of_size
      (B₁ := (threeBlocks d d d hd hd hd).permute
        ((threeBlocks d d d hd hd hd).adjacentSwap 1 (by omega)))
      (B₂ := threeBlocks d d d hd hd hd) rfl
    intro i
    fin_cases i <;> rfl
  have habFamily :
      HEq (fun i => (C ((threeBlocks d d d hd hd hd).adjacentSwap 0 (by omega) i)).obj)
        (threeBlockSmoothFamily (C 1).obj (C 0).obj (C 2).obj) := by
    apply Function.hfunext rfl
    intro i i' hii
    have hii' : i = i' := eq_of_heq hii
    subst i'
    fin_cases i <;> rfl
  have hbcFamily :
      HEq (fun i => (C ((threeBlocks d d d hd hd hd).adjacentSwap 1 (by omega) i)).obj)
        (threeBlockSmoothFamily (C 0).obj (C 2).obj (C 1).obj) := by
    apply Function.hfunext rfl
    intro i i' hii
    have hii' : i = i' := eq_of_heq hii
    subst i'
    fin_cases i <;> rfl
  constructor
  · intro hCB
    exact subquotient_external_shape_transport F T _ _ habShape _ _ habFamily E
      (hLocal.1 (sigma_mk_injective hCB))
  · intro hCA
    rcases hLocal.2 (sigma_mk_injective hCA) with hbc | hab
    · exact Or.inl (subquotient_external_shape_transport F T _ _ hbcShape _ _ hbcFamily E hbc)
    · exact Or.inr (subquotient_external_shape_transport F T _ _ habShape _ _ habFamily E hab)

/-- The rank-indexed class hypotheses force all three ranks to coincide,
so the isolated uniform input applies to every three-slot shape. -/
theorem threeSlotRepeatedCuspidalTransfer_of_uniform
    (H : UniformRepeatedCuspidalTripleJacquetTransfer.{uF, uV} F T)
    {r : ℕ} (D : BlockShape r) (hD : D.length = 3) :
    ThreeSlotRepeatedCuspidalTransfer.{uF, uV} F T D hD := by
  let := T.topology
  dsimp only [ThreeSlotRepeatedCuspidalTransfer]
  intro E C hEi hEa hEf hOcc hAB
  have hab := congrArg Sigma.fst hAB
  have uniform (hcb : D.size ⟨2, by omega⟩ = D.size ⟨1, by omega⟩) :
      ∀ i, D.size i = D.size ⟨1, by omega⟩ := by
    intro i
    have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
      have := i.isLt
      omega
    rcases hi with hi | hi | hi
    · have hie : i = ⟨0, by omega⟩ := Fin.ext hi
      exact (congrArg D.size hie).trans hab
    · have hie : i = ⟨1, by omega⟩ := Fin.ext hi
      exact congrArg D.size hie
    · have hie : i = ⟨2, by omega⟩ := Fin.ext hi
      exact (congrArg D.size hie).trans hcb
  constructor
  · intro hCB
    exact (threeSlotTransfer_of_constant F T H D hD
      (D.size ⟨1, by omega⟩) (D.positive _) (uniform (congrArg Sigma.fst hCB))
      E C hEi hEa hEf hOcc hAB).1 hCB
  · intro hCA
    exact (threeSlotTransfer_of_constant F T H D hD
      (D.size ⟨1, by omega⟩) (D.positive _)
      (uniform ((congrArg Sigma.fst hCA).trans hab))
      E C hEi hEa hEf hOcc hAB).2 hCA

/-- The actual supplied supercuspidals inside each merged block, without
choosing new isomorphism-class representatives. -/
def tripleInnerSupercuspidalFamily {n : ℕ} (B : BlockShape n)
    (j : ℕ) (hj : j + 2 < B.length) :
    letI := T.topology
    (∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i)) →
    ∀ m k, SupercuspidalRep.{uF, uV} (F := F.Carrier)
      (n := (B.tripleRefinement j hj m).size k) :=
  letI := T.topology
  fun C m k => C (B.tripleBlockEquiv j hj ⟨m, k⟩)

private theorem subquotient_external_permutation_transport {r : ℕ}
    (D : BlockShape r) (σ τ : Equiv.Perm (Fin D.length)) (hστ : σ = τ) :
    letI := T.topology
    ∀ (C : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (D.size i) F.Carrier))
      (E : SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)),
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject (fun i => C (σ i)))
        ((T.normalizedJacquetFunctor (D.permute σ)).obj E) →
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject (fun i => C (τ i)))
        ((T.normalizedJacquetFunctor (D.permute τ)).obj E) := by
  let := T.topology
  cases hστ
  exact fun _ _ h => h

private theorem selectedTripleOccurrence_of_threeSlot
    {n : ℕ} (B : BlockShape n) (j : ℕ) (hj : j + 2 < B.length)
    (δ : ℕ) (hδ : δ ≤ 1) :
    letI := T.topology
    ∀ (C : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i))
      (E : SmoothRep.{0, uF, uV} ℂ
        (GeneralLinear ((B.tripleMerge j hj).size (B.tripleMergeIndex j hj)) F.Carrier)),
      SmoothRep.IsSubquotient
        (FiniteTensor.externalSmoothObject (fun k =>
          (tripleInnerSupercuspidalFamily F T B j hj C (B.tripleMergeIndex j hj)
            ((B.tripleRefinement j hj (B.tripleMergeIndex j hj)).adjacentSwap δ
              (by have := B.tripleRefinement_length_merged j hj; omega) k)).obj))
        ((T.normalizedJacquetFunctor
          ((B.tripleRefinement j hj (B.tripleMergeIndex j hj)).permute
            ((B.tripleRefinement j hj (B.tripleMergeIndex j hj)).adjacentSwap δ
              (by have := B.tripleRefinement_length_merged j hj; omega)))).obj E) →
      SmoothRep.IsSubquotient
        (triplePermutedTensor F T B j hj δ hδ (fun i => (C i).obj) (B.tripleMergeIndex j hj))
        ((T.normalizedJacquetFunctor
          (B.triplePermutedRefinement j hj δ hδ (B.tripleMergeIndex j hj))).obj E) := by
  let := T.topology
  intro C E h
  have hswap :
      (B.tripleRefinement j hj (B.tripleMergeIndex j hj)).adjacentSwap δ
        (by have := B.tripleRefinement_length_merged j hj; omega) =
      B.tripleInnerSwap j hj δ hδ (B.tripleMergeIndex j hj) := by
    rw [BlockShape.tripleInnerSwap, dite_eq_left (B.tripleMergeIndex_val j hj)]
    rfl
  exact subquotient_external_permutation_transport F T _ _ _ hswap
    (fun k => (tripleInnerSupercuspidalFamily F T B j hj C (B.tripleMergeIndex j hj) k).obj)
    E h

/-- The complete ambient conjunction follows from precisely the isolated
uniform local triple input. This is a conditional reduction, not a proof of
that local input. -/
theorem repeatedCuspidalTripleJacquetTransfer_of_uniform
    (H : UniformRepeatedCuspidalTripleJacquetTransfer.{uF, max uF uV} F T) :
    Classification.RepeatedCuspidalTripleJacquetTransfer.{uF, uV} F T := by
  let := T.topology
  dsimp only [Classification.RepeatedCuspidalTripleJacquetTransfer]
  intro n B π C _ hπa hπf hOcc j hj
  obtain ⟨X, hXi, hXa, hXf, hX, hBlocks⟩ :=
    exists_tripleCoarseFactors F T B j hj π (fun i => (C i).obj)
      hπa hπf (fun i => (C i).property.1) (fun i => (C i).property.2.1) hOcc
  let m := B.tripleMergeIndex j hj
  let D := B.tripleRefinement j hj m
  let K := tripleInnerSupercuspidalFamily F T B j hj C m
  have hD : D.length = 3 := B.tripleRefinement_length_merged j hj
  let k0 : Fin D.length := ⟨0, by omega⟩
  let k1 : Fin D.length := ⟨1, by omega⟩
  let k2 : Fin D.length := ⟨2, by omega⟩
  have h0 : B.tripleLabelEquiv j hj ⟨m, k0⟩ = ⟨j, by omega⟩ := by
    apply Fin.ext
    rw [BlockShape.tripleLabelEquiv_val]
    simp [m, k0]
  have h1 : B.tripleLabelEquiv j hj ⟨m, k1⟩ = ⟨j + 1, by omega⟩ := by
    apply Fin.ext
    rw [BlockShape.tripleLabelEquiv_val]
    simp [m, k1]
  have h2 : B.tripleLabelEquiv j hj ⟨m, k2⟩ = ⟨j + 2, hj⟩ := by
    apply Fin.ext
    rw [BlockShape.tripleLabelEquiv_val]
    simp [m, k2]
  let cls (i : Fin B.length) :
      Σ d, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d) :=
    ⟨B.size i, (C i).isoClass⟩
  let nuCls (i : Fin B.length) :
      Σ d, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d) :=
    ⟨B.size i, T.supercuspidalClassRealPowerTwist (B.size i) 1 (C i).isoClass⟩
  have hLocal :=
    threeSlotRepeatedCuspidalTransfer_of_uniform F T H D hD
      (X m) K (hXi m) (hXa m) (hXf m) (hBlocks m)
  constructor
  · intro hAB hCB
    have hAB' :
        (⟨D.size k0, (K k0).isoClass⟩ :
          Σ d, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
        ⟨D.size k1,
          T.supercuspidalClassRealPowerTwist (D.size k1) 1
            (K k1).isoClass⟩ := by
      exact (congrArg cls h0).trans (hAB.trans (congrArg nuCls h1).symm)
    have hCB' :
        (⟨D.size k2, (K k2).isoClass⟩ :
          Σ d, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
        ⟨D.size k1, (K k1).isoClass⟩ := by
      exact (congrArg cls h2).trans (hCB.trans (congrArg cls h1).symm)
    have hSelected := selectedTripleOccurrence_of_threeSlot F T B j hj 0 (by omega)
      C (X m) ((hLocal hAB').1 hCB')
    exact subquotient_tripleSwapJacquet_of_selected F T B j hj 0 (by omega)
      π X (fun i => (C i).obj) hX hBlocks hSelected
  · intro hAB hCA
    have hAB' :
        (⟨D.size k0, (K k0).isoClass⟩ :
          Σ d, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
        ⟨D.size k1,
          T.supercuspidalClassRealPowerTwist (D.size k1) 1
            (K k1).isoClass⟩ := by
      exact (congrArg cls h0).trans (hAB.trans (congrArg nuCls h1).symm)
    have hCA' :
        (⟨D.size k2, (K k2).isoClass⟩ :
          Σ d, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
        ⟨D.size k0, (K k0).isoClass⟩ := by
      exact (congrArg cls h2).trans (hCA.trans (congrArg cls h0).symm)
    rcases (hLocal hAB').2 hCA' with hbc | hab
    · have hSelected := selectedTripleOccurrence_of_threeSlot F T B j hj 1 (by omega)
        C (X m) hbc
      exact Or.inl (subquotient_tripleSwapJacquet_of_selected F T B j hj 1 (by omega)
        π X (fun i => (C i).obj) hX hBlocks hSelected)
    · have hSelected := selectedTripleOccurrence_of_threeSlot F T B j hj 0 (by omega)
        C (X m) hab
      exact Or.inr (subquotient_tripleSwapJacquet_of_selected F T B j hj 0 (by omega)
        π X (fun i => (C i).obj) hX hBlocks hSelected)

end Langlands.CuspidalSupport
