import Langlands.AllFieldBZ.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
import Langlands.Representation.Derivative.MirabolicLatticeBox

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicLatticeBox`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicLatticeBox` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Derivative.Mirabolic
open Langlands.Derivative.Mirabolic hiding character_dotProduct_eq_one character_mul_eq_one coe_latticeBox exists_latticeBox_subset exists_ne_zero_mem_additiveLattice finite_latticeBox_quotient inv_mem_additiveLattice_of_notMem isCompact_latticeBox isOpen_latticeBox latticeBox latticeBox_mono mem_latticeBox mem_latticeBox_of_forall_character_eq_one
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
open Topology
open scoped Matrix
universe uF

section CharacterSum
variable {G : Type*} [AddCommGroup G]

end CharacterSum
section Lattice
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- The box `(π^(-N) O)^k` of radical coordinates. -/
def latticeBox (k : ℕ) (N : ℤ) : AddSubgroup (Fin k → F.Carrier) :=
  AddSubgroup.pi Set.univ fun _ => T.additiveLattice N

theorem mem_latticeBox {k : ℕ} {N : ℤ} {d : Fin k → F.Carrier} :
    d ∈ latticeBox T k N ↔ ∀ j, d j ∈ T.additiveLattice N := by
  simp [latticeBox, AddSubgroup.mem_pi]

theorem latticeBox_mono {k : ℕ} {N N' : ℤ} (h : N ≤ N') :
    latticeBox T k N ≤ latticeBox T k N' := fun _ hd =>
  (mem_latticeBox T).mpr fun j => T.additiveLattice_mono h ((mem_latticeBox T).mp hd j)

theorem coe_latticeBox (k : ℕ) (N : ℤ) :
    (latticeBox T k N : Set (Fin k → F.Carrier)) =
      Set.univ.pi fun _ => (T.additiveLattice N : Set F.Carrier) := by
  ext d
  simp [mem_latticeBox, Set.mem_pi]

theorem isOpen_latticeBox (k : ℕ) (N : ℤ) :
    letI := T.topology
    IsOpen (latticeBox T k N : Set (Fin k → F.Carrier)) := by
  let := T.topology
  rw [coe_latticeBox]
  exact isOpen_set_pi Set.finite_univ fun _ _ => T.isOpen_additiveLattice N

theorem isCompact_latticeBox (k : ℕ) (N : ℤ) :
    letI := T.topology
    IsCompact (latticeBox T k N : Set (Fin k → F.Carrier)) := by
  let := T.topology
  rw [coe_latticeBox]
  exact isCompact_univ_pi fun _ => T.isCompact_additiveLattice N

/-- Every neighborhood of zero in the coordinate space contains a lattice box. -/
theorem exists_latticeBox_subset {k : ℕ} {s : Set (Fin k → F.Carrier)}
    (hs : letI := T.topology; s ∈ 𝓝 (0 : Fin k → F.Carrier)) :
    ∃ N : ℤ, (latticeBox T k N : Set (Fin k → F.Carrier)) ⊆ s := by
  let := T.topology
  rw [nhds_pi, Filter.mem_pi'] at hs
  obtain ⟨I, t, ht, hsub⟩ := hs
  choose n hn using fun i => T.exists_additiveLattice_subset (ht i)
  refine ⟨-∑ i, |n i|, fun d hd => hsub fun i _ => hn i ?_⟩
  have hle : -∑ j, |n j| ≤ n i := by
    have h1 := Finset.single_le_sum (fun j _ => abs_nonneg (n j)) (Finset.mem_univ i)
    have h2 := neg_abs_le (n i)
    linarith
  exact T.additiveLattice_mono hle ((mem_latticeBox T).mp hd i)

/-- The quotient of a lattice box by a smaller one is finite. -/
theorem finite_latticeBox_quotient (k : ℕ) (N l : ℤ) :
    Finite ((latticeBox T k N) ⧸ (latticeBox T k l).addSubgroupOf (latticeBox T k N)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : CompactSpace (latticeBox T k N) :=
    isCompact_iff_compactSpace.mp (isCompact_latticeBox T k N)
  apply AddSubgroup.quotient_finite_of_isOpen
  rw [AddSubgroup.coe_addSubgroupOf]
  exact (isOpen_latticeBox T k l).preimage continuous_subtype_val

end Lattice
section Duality
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- An element outside `π^(-N) O` has inverse in `π^N O`. -/
theorem inv_mem_additiveLattice_of_notMem {N : ℤ} {x : F.Carrier}
    (hx : x ∉ T.additiveLattice N) : x⁻¹ ∈ T.additiveLattice (-N) := by
  rw [LocalFieldPackage.TopologicalData.mem_additiveLattice] at hx ⊢
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (by simp)
  rw [map_inv₀]
  have hlt : WithZero.exp N < T.discreteValuation x := lt_of_not_ge hx
  have hpos : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp N := WithZero.exp_pos
  calc (T.discreteValuation x)⁻¹ ≤ (WithZero.exp N)⁻¹ := inv_anti₀ hpos hlt.le
    _ = WithZero.exp (-N) := by rw [WithZero.exp_neg]

/-- Every additive lattice contains a nonzero element. -/
theorem exists_ne_zero_mem_additiveLattice (N : ℤ) :
    ∃ t : F.Carrier, t ≠ 0 ∧ t ∈ T.additiveLattice N := by
  have hπ : T.uniformizer ^ (-N) ≠ 0 := by
    apply zpow_ne_zero
    apply T.discreteValuation.ne_zero_iff.mp
    rw [T.discreteValuation_uniformizer]
    exact WithZero.exp_ne_zero
  refine ⟨T.uniformizer ^ (-N), hπ, ?_⟩
  rw [T.mem_additiveLattice_iff_div_mem_integers, div_self hπ]
  exact (T.Integers).one_mem

/-- `ψ(a x) = 1` for `a ∈ π^(-(n(ψ) - M)) O` and `x ∈ π^(-M) O`. -/
theorem character_mul_eq_one (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {M : ℤ}
    {a x : F.Carrier} (ha : a ∈ T.additiveLattice (T.additiveConductor ψ - M))
    (hx : x ∈ T.additiveLattice M) : ψ (a * x) = 1 := by
  apply (T.additiveConductor_spec ψ).1
  rw [LocalFieldPackage.TopologicalData.mem_additiveLattice] at ha hx ⊢
  rw [map_mul]
  calc T.discreteValuation a * T.discreteValuation x ≤
        WithZero.exp (T.additiveConductor ψ - M) * WithZero.exp M := mul_le_mul' ha hx
    _ = WithZero.exp (T.additiveConductor ψ) := by rw [← WithZero.exp_add]; congr 1; ring

/-- `ψ(y ⬝ c) = 1` for `y` in the box at level `n(ψ) - M` and `c` in the box at level `M`. -/
theorem character_dotProduct_eq_one (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {k : ℕ} {M : ℤ} {y c : Fin k → F.Carrier}
    (hy : y ∈ latticeBox T k (T.additiveConductor ψ - M)) (hc : c ∈ latticeBox T k M) :
    ψ (y ⬝ᵥ c) = 1 := by
  rw [dotProduct]
  refine Finset.sum_induction _ (fun x => ψ x = 1) (fun a b ha hb => ?_) ?_ fun j _ =>
    character_mul_eq_one T ψ ((mem_latticeBox T).mp hy j) ((mem_latticeBox T).mp hc j)
  · rw [AddChar.map_add_eq_mul, ha, hb, mul_one]
  · exact AddChar.map_zero_eq_one _

/-- If `y ↦ ψ(y ⬝ c)` is trivial on the box at level `A`, then `c` lies in the box at
level `n(ψ) - A`. -/
theorem mem_latticeBox_of_forall_character_eq_one
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {k : ℕ} {A : ℤ}
    {c : Fin k → F.Carrier} (h : ∀ y ∈ latticeBox T k A, ψ (y ⬝ᵥ c) = 1) :
    c ∈ latticeBox T k (T.additiveConductor ψ - A) := by
  rw [mem_latticeBox]
  intro j
  apply T.mem_additiveLattice_of_forall_mul_eq_one ψ A
  intro t ht
  have hy : (Pi.single j t : Fin k → F.Carrier) ∈ latticeBox T k A := by
    rw [mem_latticeBox]
    intro i
    by_cases hij : i = j
    · subst hij
      simpa using ht
    · simp [hij]
  have := h _ hy
  rwa [single_dotProduct, mul_comm] at this

end Duality
section LocallyConstant
variable {G X : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [TopologicalSpace X]

end LocallyConstant
end Langlands.AllFieldBZ.Derivative.Mirabolic
