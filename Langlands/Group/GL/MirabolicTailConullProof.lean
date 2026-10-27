import Langlands.Group.GL.MirabolicTailConullStatement
import Langlands.Group.GL.CountabilityProof
import Langlands.Group.GL.Transvection

/-!
# Proof of the open full-measure inverse-row tail locus

Openness follows from continuity of inversion and of matrix entries. The
exceptional set is covered by finitely many pieces with a nonzero head
coordinate; an elementary transvection with a small nonzero parameter moves
each piece off itself, so Steinhaus's theorem makes each piece null.
See the paired Markdown for the full route.
-/

namespace Langlands.GeneralLinear

open MeasureTheory Filter Topology Set
open scoped Pointwise

universe uF

section Steinhaus

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- A measurable set is null for an inner regular Haar measure when every
neighbourhood of the identity contains an element moving the set off itself. -/
theorem haar_null_of_forall_nhds_disjoint_translate (μ : Measure G) [μ.IsHaarMeasure]
    [μ.InnerRegular] {E : Set G} (hE : MeasurableSet E)
    (h : ∀ U ∈ 𝓝 (1 : G), ∃ u ∈ U, ∀ x ∈ E, u * x ∉ E) : μ E = 0 := by
  by_contra hne
  obtain ⟨u, hu, hdisj⟩ :=
    h _ (Measure.div_mem_nhds_one_of_haar_pos μ E hE (pos_iff_ne_zero.mpr hne))
  obtain ⟨y, hy, x, hx, rfl⟩ := hu
  exact hdisj x hx (by simpa using hy)

end Steinhaus

section Transvection

variable {K : Type*} [Field K] {n : ℕ}

theorem transvectionUnit_zero (i j : Fin n) (hij : i ≠ j) :
    transvectionUnit i j hij (0 : K) = 1 := by
  ext : 1
  simp [transvectionUnit]

/-- After left translation by `1 + t E_{ij}`, column `j` of the inverse becomes
`r_j - t r_i` in every row. -/
theorem inv_transvectionUnit_mul_apply_same (i j : Fin n) (hij : i ≠ j) (t : K)
    (g : GeneralLinear n K) (r : Fin n) :
    ((transvectionUnit i j hij t * g)⁻¹ : GeneralLinear n K) r j =
      (g⁻¹ : GeneralLinear n K) r j + -t * (g⁻¹ : GeneralLinear n K) r i := by
  rw [mul_inv_rev]
  exact Matrix.mul_transvection_apply_same i j r (-t) _

/-- Every row of the inverse of an invertible matrix has a nonzero entry. -/
theorem exists_inv_apply_ne_zero (g : GeneralLinear n K) (r : Fin n) :
    ∃ k, (g⁻¹ : GeneralLinear n K) r k ≠ 0 := by
  by_contra! h
  have h1 : ((g⁻¹ * g : GeneralLinear n K) : Matrix (Fin n) (Fin n) K) r r = 1 := by simp
  rw [Units.val_mul, Matrix.mul_apply] at h1
  simp [h] at h1

variable [TopologicalSpace K] [IsTopologicalRing K]

theorem continuous_transvectionUnit (i j : Fin n) (hij : i ≠ j) :
    Continuous (transvectionUnit (F := K) i j hij) := by
  have hm : ∀ s : K → K, Continuous s →
      Continuous fun t => Matrix.transvection i j (s t) := by
    intro s hs
    refine continuous_matrix fun r c => ?_
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
    by_cases h : i = r ∧ j = c
    · simp only [h, and_self, ↓reduceIte]
      exact continuous_const.add hs
    · simp only [h, ↓reduceIte]
      exact continuous_const
  exact Units.continuous_iff.mpr ⟨hm id continuous_id, hm (fun t => -t) continuous_neg⟩

end Transvection

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Every neighbourhood of zero in the supplied topology contains a nonzero
element: the images of nonzero elements of `Padic p` near zero, by the algebra
map, which is continuous for the supplied module topology. -/
theorem padic_exists_ne_zero_mem_nhds_zero (T : F.TopologicalData) :
    letI := T.topology
    ∀ U ∈ 𝓝 (0 : F.Carrier), ∃ t ∈ U, t ≠ 0 := by
  let := T.topology
  have := T.moduleTopology
  let := T.valuativeRel
  have := T.localField
  intro U hU
  have hc : Continuous (algebraMap (Padic p) F.Carrier) := continuous_algebraMap _ _
  have hpre : algebraMap (Padic p) F.Carrier ⁻¹' U ∈ 𝓝 (0 : Padic p) :=
    hc.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨c, hc0, hcU⟩ := Filter.nonempty_of_mem (inter_mem_nhdsWithin {0}ᶜ hpre)
  exact ⟨_, hcU, (map_ne_zero _).mpr hc0⟩

end Padic

/-- The inverse last-row tail is nonzero on an open set whose complement is
null for every left Haar measure, in the supplied topology. -/
theorem padicMirabolicTailConull : PadicMirabolicTailConullStatement.{uF} := by
  intro p _ F T a b
  let := T.topology
  let mG : MeasurableSpace (GeneralLinear (a + b + 1) F.Carrier) := borel _
  have : BorelSpace (GeneralLinear (a + b + 1) F.Carrier) := ⟨rfl⟩
  have := T.fieldT2
  have := T.generalLinearTopologicalGroup (a + b + 1)
  have := T.generalLinearLocallyCompactSpace (a + b + 1)
  have := T.generalLinearSecondCountableTopology (a + b + 1)
  have : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    have := T.localField
    infer_instance
  have hcont : ∀ r k : Fin (a + b + 1),
      Continuous fun g : GeneralLinear (a + b + 1) F.Carrier => (g⁻¹) r k :=
    fun r k => (Units.continuous_val.comp continuous_inv).matrix_elem r k
  refine ⟨?_, ?_⟩
  · simp only [Set.ofPred_exists]
    exact isOpen_iUnion fun j => isOpen_ne_fun (hcont _ _) continuous_const
  · intro μ hμ
    have := hμ
    have : μ.InnerRegular := inferInstance
    let L : Fin (a + b + 1) := Fin.last (a + b)
    let E : Fin a → Set (GeneralLinear (a + b + 1) F.Carrier) := fun i =>
      {g | (g⁻¹) L L = 0 ∧ (g⁻¹) L (Fin.castAdd (b + 1) i) ≠ 0}
    have hsub : {g : GeneralLinear (a + b + 1) F.Carrier |
        ∀ j : Fin (b + 1), (g⁻¹) (Fin.last (a + b)) (Fin.natAdd a j) = 0} ⊆ ⋃ i, E i := by
      intro g hg
      obtain ⟨k, hk⟩ := exists_inv_apply_ne_zero g L
      have hL : (g⁻¹) L L = 0 := by
        have := hg (Fin.last b)
        rwa [Fin.natAdd_last] at this
      have hcases : (∃ i : Fin a, k = Fin.castAdd (b + 1) i) ∨
          ∃ j : Fin (b + 1), k = Fin.natAdd a j :=
        Fin.addCases (motive := fun k : Fin (a + (b + 1)) =>
            (∃ i : Fin a, k = Fin.castAdd (b + 1) i) ∨ ∃ j : Fin (b + 1), k = Fin.natAdd a j)
          (fun i => Or.inl ⟨i, rfl⟩) (fun j => Or.inr ⟨j, rfl⟩) k
      rcases hcases with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · exact mem_iUnion.mpr ⟨i, hL, hk⟩
      · exact absurd (hg j) hk
    refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
    have hmeas : MeasurableSet (E i) :=
      (isClosed_eq (hcont L L) continuous_const).measurableSet.inter
        (isOpen_ne_fun (hcont L _) continuous_const).measurableSet
    have hij : Fin.castAdd (b + 1) i ≠ L := by
      intro h
      have h' := congrArg Fin.val h
      simp only [Fin.val_castAdd, L, Fin.val_last] at h'
      have := i.isLt
      omega
    refine haar_null_of_forall_nhds_disjoint_translate μ hmeas fun U hU => ?_
    have hφ : transvectionUnit (Fin.castAdd (b + 1) i) L hij ⁻¹' U ∈ 𝓝 (0 : F.Carrier) :=
      (continuous_transvectionUnit _ _ hij).continuousAt.preimage_mem_nhds
        (by rwa [transvectionUnit_zero])
    obtain ⟨t, htU, ht0⟩ := padic_exists_ne_zero_mem_nhds_zero T _ hφ
    refine ⟨_, htU, fun g hg hg' => ?_⟩
    obtain ⟨hgL, hgi⟩ := hg
    obtain ⟨hg'L, -⟩ := hg'
    have key := inv_transvectionUnit_mul_apply_same (Fin.castAdd (b + 1) i) L hij t g L
    rw [hg'L, hgL, zero_add, eq_comm, mul_eq_zero, neg_eq_zero] at key
    exact key.elim ht0 hgi

end Langlands.GeneralLinear
