import Langlands.Representation.RankinSelberg.CauchyPartitionMinors

/-! # Finite degree indices for the Schur Cauchy sum -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

/-- The total staircase exponent in rank `n + 1`. -/
def staircaseDegree (n : ℕ) : ℕ := ∑ i : Fin (n + 1), i.rev.val

/-- Partitions of degree `d`, bounded in the finite coordinate set `Fin (d+1)`. -/
abbrev DegreePartition (n d : ℕ) :=
  {α : Fin (n + 1) → Fin (d + 1) // Antitone α ∧ ∑ i, (α i).val = d}

/-- Subsets of exponent indices in the shifted total degree. -/
abbrev DegreeSubset (n d : ℕ) :=
  {S : {S : Finset (Fin (d + staircaseDegree n + 1)) // S.card = n + 1} //
    ∑ i, (S.val.orderEmbOfFin S.property i).val = d + staircaseDegree n}

/-- The increasing natural exponents of a finite-degree partition. -/
def degreePartitionNatExponents {n d : ℕ} (α : DegreePartition n d) : Fin (n + 1) → ℕ :=
  fun i => (α.val i.rev).val + i.val

theorem degreePartitionNatExponents_strictMono {n d : ℕ} (α : DegreePartition n d) :
    StrictMono (degreePartitionNatExponents α) := by
  intro i j hij
  have h := α.property.1 (Fin.rev_le_rev.mpr hij.le)
  change (α.val i.rev).val ≤ (α.val j.rev).val at h
  have hij' : i.val < j.val := hij
  dsimp [degreePartitionNatExponents]
  omega

theorem sum_degreePartitionNatExponents {n d : ℕ} (α : DegreePartition n d) :
    (∑ i, degreePartitionNatExponents α i) = d + staircaseDegree n := by
  have hα : (∑ i : Fin (n + 1), (α.val i.rev).val) = ∑ i, (α.val i).val := by
    simpa only [Fin.revPerm_apply] using
      (Equiv.sum_comp Fin.revPerm (fun i : Fin (n + 1) => (α.val i).val))
  have hrev : (∑ i : Fin (n + 1), i.rev.val) = ∑ i : Fin (n + 1), i.val := by
    simpa only [Fin.revPerm_apply] using
      (Equiv.sum_comp Fin.revPerm (fun i : Fin (n + 1) => i.val))
  simp only [degreePartitionNatExponents, Finset.sum_add_distrib]
  rw [hα, α.property.2, staircaseDegree, hrev]

/-- The same tuple in the finite exponent interval for its total degree. -/
def degreePartitionExponents {n d : ℕ} (α : DegreePartition n d) :
    Fin (n + 1) → Fin (d + staircaseDegree n + 1) := fun i =>
  ⟨degreePartitionNatExponents α i, by
    have h := Finset.single_le_sum (fun j _ => Nat.zero_le (degreePartitionNatExponents α j))
      (Finset.mem_univ i)
    rw [sum_degreePartitionNatExponents] at h
    omega⟩

theorem degreePartitionExponents_strictMono {n d : ℕ} (α : DegreePartition n d) :
    StrictMono (degreePartitionExponents α) :=
  degreePartitionNatExponents_strictMono α

/-- The selected exponent subset of a finite-degree partition. -/
def degreePartitionSubset {n d : ℕ} (α : DegreePartition n d) :
    {S : Finset (Fin (d + staircaseDegree n + 1)) // S.card = n + 1} :=
  ⟨Finset.univ.image (degreePartitionExponents α), by
    rw [Finset.card_image_of_injective _ (degreePartitionExponents_strictMono α).injective,
      Finset.card_univ, Fintype.card_fin]⟩

theorem degreePartitionSubset_orderEmb {n d : ℕ} (α : DegreePartition n d) :
    (degreePartitionSubset α).val.orderEmbOfFin (degreePartitionSubset α).property =
      degreePartitionExponents α := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro i
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · exact degreePartitionExponents_strictMono α

/-- The partition's exponent subset lies in its shifted degree. -/
def degreePartitionToSubset {n d : ℕ} (α : DegreePartition n d) : DegreeSubset n d :=
  ⟨degreePartitionSubset α, by
    rw [degreePartitionSubset_orderEmb]
    exact sum_degreePartitionNatExponents α⟩

/-- Removing the staircase from a degree subset gives a finite-degree partition. -/
def degreeSubsetToPartition {n d : ℕ} (S : DegreeSubset n d) : DegreePartition n d := by
  let e : Fin (n + 1) → ℕ := fun i => (S.val.val.orderEmbOfFin S.val.property i).val
  have he : StrictMono e := (S.val.val.orderEmbOfFin S.val.property).strictMono
  have hpos := exponentPartition_nonneg e he
  have hsum : (∑ i, exponentPartition e i) = (d : ℤ) := by
    have h := sum_exponentPartition e
    have hs : (∑ i, e i) = d + staircaseDegree n := S.property
    rw [hs] at h
    change ((d + staircaseDegree n : ℕ) : ℤ) =
      (∑ i, exponentPartition e i) + (staircaseDegree n : ℤ) at h
    omega
  have hbound (i : Fin (n + 1)) : (exponentPartition e i).toNat < d + 1 := by
    have h := Finset.single_le_sum (fun j _ => hpos j) (Finset.mem_univ i)
    rw [hsum] at h
    have hi := hpos i
    omega
  refine ⟨fun i => ⟨(exponentPartition e i).toNat, hbound i⟩, ?_, ?_⟩
  · intro i j hij
    exact Int.toNat_le_toNat ((exponentPartition_antitone e he) hij)
  · apply Int.ofNat_inj.mp
    push_cast
    simp_rw [Int.toNat_of_nonneg (hpos _)]
    exact hsum

theorem degreeSubsetToPartition_exponents {n d : ℕ} (S : DegreeSubset n d) :
    degreePartitionExponents (degreeSubsetToPartition S) =
      S.val.val.orderEmbOfFin S.val.property := by
  funext i
  apply Fin.ext
  change (exponentPartition (fun j =>
      (S.val.val.orderEmbOfFin S.val.property j).val) i.rev).toNat + i.val = _
  simp only [exponentPartition, Fin.rev_rev]
  have h := le_strictMono_fin (fun j => (S.val.val.orderEmbOfFin S.val.property j).val)
    (S.val.val.orderEmbOfFin S.val.property).strictMono i
  omega

theorem degreePartitionToSubset_left_inverse {n d : ℕ} (α : DegreePartition n d) :
    degreeSubsetToPartition (degreePartitionToSubset α) = α := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  change (exponentPartition (fun j =>
      ((degreePartitionSubset α).val.orderEmbOfFin (degreePartitionSubset α).property j).val) i).toNat = _
  rw [degreePartitionSubset_orderEmb]
  change (((degreePartitionNatExponents α i.rev : ℕ) : ℤ) - i.rev.val).toNat = (α.val i).val
  simp only [degreePartitionNatExponents, Fin.rev_rev]
  omega

theorem degreePartitionToSubset_right_inverse {n d : ℕ} (S : DegreeSubset n d) :
    degreePartitionToSubset (degreeSubsetToPartition S) = S := by
  apply Subtype.ext
  apply Subtype.ext
  change Finset.univ.image (degreePartitionExponents (degreeSubsetToPartition S)) = S.val.val
  rw [degreeSubsetToPartition_exponents, Finset.image_orderEmbOfFin_univ]

/-- Exact finite-degree correspondence for the Cauchy coefficient sum. -/
def degreePartitionSubsetEquiv (n d : ℕ) : DegreePartition n d ≃ DegreeSubset n d where
  toFun := degreePartitionToSubset
  invFun := degreeSubsetToPartition
  left_inv := degreePartitionToSubset_left_inverse
  right_inv := degreePartitionToSubset_right_inverse

end Langlands.GeneralLinear.Spherical
