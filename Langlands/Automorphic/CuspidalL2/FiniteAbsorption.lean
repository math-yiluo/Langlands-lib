import Langlands.Automorphic.CuspidalL2.Basics

/-! # Representatives of adelic block matrices and absorption of their finite parts -/

noncomputable section
universe u
open scoped Classical Topology
open NumberField Filter IsDedekindDomain HeightOneSpectrum
set_option autoImplicit false

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Every adele is a rational number plus `δ` times an element of the compact box
`archimedeanFundamentalSet K × integralFiniteAdeles K`. -/
theorem exists_adele_decomposition {δ : ℕ} (hδ : δ ≠ 0) (z : Adeles K) :
    ∃ ξ : K, ∃ w : Adeles K, w.1 ∈ archimedeanFundamentalSet K ∧
      w.2 ∈ integralFiniteAdeles K ∧
      z = algebraMap K (Adeles K) ξ + (δ : Adeles K) * w := by
  set z' : Adeles K := algebraMap K (Adeles K) ((δ : K)⁻¹) * z with hz'
  obtain ⟨x, hx⟩ := exists_sub_mem_integralFiniteAdeles z'.2
  obtain ⟨y, hy⟩ := exists_sub_integer_mem_archimedeanFundamentalSet K
    (z'.1 - algebraMap K (InfiniteAdeles K) x)
  have hyf : algebraMap K (FiniteAdeles K) (y : K) ∈ integralFiniteAdeles K :=
    (mem_integralFiniteAdeles K _).mpr fun v ↦ coe_mem_adicCompletionIntegers v y
  refine ⟨(δ : K) * (x + (y : K)), z' - algebraMap K (Adeles K) (x + (y : K)), ?_, ?_, ?_⟩
  · change z'.1 - algebraMap K (InfiniteAdeles K) (x + (y : K)) ∈ _
    rwa [map_add, ← sub_sub]
  · change z'.2 - algebraMap K (FiniteAdeles K) (x + (y : K)) ∈ integralFiniteAdeles K
    rw [map_add, ← sub_sub]
    exact (integralFiniteAdeles K).sub_mem hx hyf
  · have hδK : (δ : K) ≠ 0 := Nat.cast_ne_zero.mpr hδ
    have hcast : (δ : Adeles K) = algebraMap K (Adeles K) (δ : K) := (map_natCast _ _).symm
    rw [hcast, hz', mul_sub, ← mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel₀ hδK, map_one,
      one_mul, add_sub_cancel]

/-- Entrywise version of `exists_adele_decomposition` for adelic block matrices. -/
theorem exists_matrix_decomposition {a b δ : ℕ} (hδ : δ ≠ 0)
    (Y : Matrix (Fin a) (Fin b) (Adeles K)) :
    ∃ ξ : Matrix (Fin a) (Fin b) K, ∃ W : Matrix (Fin a) (Fin b) (Adeles K),
      (∀ i j, (W i j).1 ∈ archimedeanFundamentalSet K ∧ (W i j).2 ∈ integralFiniteAdeles K) ∧
      Y = ξ.map (algebraMap K (Adeles K)) + (δ : Adeles K) • W := by
  choose ξ W hW1 hW2 hY using fun i j => exists_adele_decomposition K hδ (Y i j)
  refine ⟨Matrix.of ξ, Matrix.of W, fun i j => ⟨hW1 i j, hW2 i j⟩, ?_⟩
  ext i j
  exact hY i j

/-- **Finite absorption.** For a compact set `Q` and an open subgroup `L` of the finite adelic
group, some positive integer `δ` has the property that every conjugate `q⁻¹ u(δ W) q`,
`q ∈ Q`, of a block unipotent with integral block `W` lies in `L`. -/
theorem exists_nsmul_conj_blockUnipotent_mem {a b : ℕ} (h : a + b = n)
    (L : Subgroup (FiniteAdelicGL K n)) (hL : IsOpen (L : Set (FiniteAdelicGL K n)))
    {Q : Set (FiniteAdelicGL K n)} (hQ : IsCompact Q) :
    ∃ δ : ℕ, δ ≠ 0 ∧ ∀ W : Matrix (Fin a) (Fin b) (FiniteAdeles K),
      (∀ i j, W i j ∈ integralFiniteAdeles K) → ∀ q ∈ Q,
        q⁻¹ * GeneralLinear.blockUnipotent h (δ • W) * q ∈ L := by
  let V : AddSubgroup (Matrix (Fin a) (Fin b) (FiniteAdeles K)) :=
    { carrier := {W | ∀ q ∈ Q, q⁻¹ * GeneralLinear.blockUnipotent h W * q ∈ L}
      add_mem' := by
        intro W W' hW hW' q hq
        have := L.mul_mem (hW q hq) (hW' q hq)
        rw [GeneralLinear.blockUnipotent_add]
        simpa [mul_assoc] using this
      zero_mem' := by
        intro q hq
        simp
      neg_mem' := by
        intro W hW q hq
        have hinv : GeneralLinear.blockUnipotent h (-W) =
            (GeneralLinear.blockUnipotent h W)⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, ← GeneralLinear.blockUnipotent_add, neg_add_cancel,
            GeneralLinear.blockUnipotent_zero]
        have := L.inv_mem (hW q hq)
        rw [hinv]
        simpa [mul_assoc] using this }
  have hcont : Continuous fun p : Matrix (Fin a) (Fin b) (FiniteAdeles K) × FiniteAdelicGL K n =>
      p.2⁻¹ * GeneralLinear.blockUnipotent h p.1 * p.2 :=
    (continuous_snd.inv.mul ((GeneralLinear.continuous_blockUnipotent h).comp
      continuous_fst)).mul continuous_snd
  have hev : ∀ᶠ W in 𝓝 (0 : Matrix (Fin a) (Fin b) (FiniteAdeles K)),
      ∀ q ∈ Q, q⁻¹ * GeneralLinear.blockUnipotent h W * q ∈ L :=
    hQ.eventually_forall_of_forall_eventually fun q _ =>
      (hL.preimage hcont).mem_nhds (by simp)
  have hVopen : IsOpen (V : Set (Matrix (Fin a) (Fin b) (FiniteAdeles K))) :=
    AddSubgroup.isOpen_of_mem_nhds V hev
  let O : AddSubgroup (Matrix (Fin a) (Fin b) (FiniteAdeles K)) :=
    { carrier := {W | ∀ i j, W i j ∈ integralFiniteAdeles K}
      add_mem' := fun hW hW' i j => (integralFiniteAdeles K).add_mem (hW i j) (hW' i j)
      zero_mem' := fun i j => (integralFiniteAdeles K).zero_mem
      neg_mem' := fun hW i j => (integralFiniteAdeles K).neg_mem (hW i j) }
  have hOc : IsCompact (O : Set (Matrix (Fin a) (Fin b) (FiniteAdeles K))) := by
    have : (O : Set (Matrix (Fin a) (Fin b) (FiniteAdeles K))) =
        Set.univ.pi fun _ => Set.univ.pi fun _ =>
          (integralFiniteAdeles K : Set (FiniteAdeles K)) := by
      ext W
      exact ⟨fun hW i _ j _ => hW i j, fun hW i j => hW i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_integralFiniteAdeles K
  have : CompactSpace O := isCompact_iff_compactSpace.mp hOc
  have : Finite (O ⧸ V.addSubgroupOf O) :=
    AddSubgroup.quotient_finite_of_isOpen _ (AddSubgroup.addSubgroupOf_isOpen O V hVopen)
  refine ⟨(V.addSubgroupOf O).index, AddSubgroup.index_ne_zero_of_finite, ?_⟩
  intro W hW q hq
  have hmem := AddSubgroup.nsmul_index_mem (V.addSubgroupOf O) ⟨W, hW⟩
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  exact hmem q hq

end Langlands.Global
