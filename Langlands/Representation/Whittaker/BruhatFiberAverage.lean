import Langlands.Representation.Whittaker.CompatibleTorus
import Langlands.LocalField.Canonical
import Langlands.LocalField.Topology
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral

/-!
# Shalika's action on the torus coordinates of a Bruhat cell and its raw fiber integral

For a permutation `w` of `Fin r`, the subgroup `U_w⁺ = permutationUnipotentPlus r K w`
acts on `U × ((Fin r → Kˣ) × U)` by
`u • (u₁, d, u₂) = (u₁ * p * h(d) * u⁻¹ * h(d)⁻¹ * p⁻¹, d, u * u₂)`, where
`p = permutation r K w` and `h = Iwasawa.diagonalUnits`. The action preserves
`upperBruhatTorusMap r w`. Over a Hausdorff topological field every orbit map is a
closed embedding, so the unweighted Bochner integral of a test function along an orbit
converges for every Borel measure on `U_w⁺` finite on compact sets. The action and the
orbit integral `∫ α(u * m) du⁺` are those on the right side of Shalika (1974), printed
p.176, formula (1.11), `f_α(π(m)) = ∫ α(u * m) du⁺`. Only the raw function on the
coordinate space is constructed here. The cell function `f_α` of Lemma 1.10 and the
identity with it are not. The arbitrary measure finite on compact sets and the
topological laws are internal extensions. See the paired Markdown for the hypotheses,
the proofs and the scope.
-/

noncomputable section

open MeasureTheory Topology

namespace Langlands.Whittaker

open Langlands.GeneralLinear HarmonicAnalysis

universe uK uF

section Action

variable (r : ℕ) (K : Type uK) [Field K] (w : Equiv.Perm (Fin r))

/-- Diagonal normalization: for `u ∈ U_w⁺` and every diagonal parameter `d`, the matrix
`p * h(d) * u⁻¹ * h(d)⁻¹ * p⁻¹` is upper unipotent. -/
theorem permutation_diagonal_conj_inv_mem_upperUnipotent (d : Fin r → Kˣ)
    (u : permutationUnipotentPlus r K w) :
    permutation r K w * Iwasawa.diagonalUnits d * u.val⁻¹ *
        (Iwasawa.diagonalUnits d)⁻¹ * (permutation r K w)⁻¹ ∈ upperUnipotent r K := by
  have hu : permutation r K w * u.val⁻¹ * (permutation r K w)⁻¹ ∈ upperUnipotent r K := by
    have h := inv_mem ((mem_permutationUnipotentPlus_iff r K w u.val).mp u.property).2
    have he : (permutation r K w * u.val * (permutation r K w)⁻¹)⁻¹ =
        permutation r K w * u.val⁻¹ * (permutation r K w)⁻¹ := by
      group
    rwa [he] at h
  have he : permutation r K w * Iwasawa.diagonalUnits d * u.val⁻¹ *
        (Iwasawa.diagonalUnits d)⁻¹ * (permutation r K w)⁻¹ =
      permutation r K w * Iwasawa.diagonalUnits d * u.val⁻¹ *
        (permutation r K w * Iwasawa.diagonalUnits d)⁻¹ := by
    group
  rw [he]
  exact monomial_conj_mem_upperUnipotent w d hu

/-- The first component `u₁ * p * h(d) * u⁻¹ * h(d)⁻¹ * p⁻¹` of the action is upper
unipotent. -/
theorem bruhatFiberAct_fst_mem (u : permutationUnipotentPlus r K w)
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    m.1.val * permutation r K w * Iwasawa.diagonalUnits m.2.1 * u.val⁻¹ *
        (Iwasawa.diagonalUnits m.2.1)⁻¹ * (permutation r K w)⁻¹ ∈ upperUnipotent r K := by
  have he : m.1.val * permutation r K w * Iwasawa.diagonalUnits m.2.1 * u.val⁻¹ *
        (Iwasawa.diagonalUnits m.2.1)⁻¹ * (permutation r K w)⁻¹ =
      m.1.val * (permutation r K w * Iwasawa.diagonalUnits m.2.1 * u.val⁻¹ *
        (Iwasawa.diagonalUnits m.2.1)⁻¹ * (permutation r K w)⁻¹) := by
    simp only [mul_assoc]
  rw [he]
  exact mul_mem m.1.property
    (permutation_diagonal_conj_inv_mem_upperUnipotent r K w m.2.1 u)

/-- Shalika's action of `U_w⁺` on `M = U × ((Fin r → Kˣ) × U)`:
`u • (u₁, d, u₂) = (u₁ * p * h(d) * u⁻¹ * h(d)⁻¹ * p⁻¹, d, u * u₂)`. The last
component uses the actual inclusion `U_w⁺ ≤ U`. -/
def bruhatFiberAct (u : permutationUnipotentPlus r K w)
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K :=
  (⟨m.1.val * permutation r K w * Iwasawa.diagonalUnits m.2.1 * u.val⁻¹ *
      (Iwasawa.diagonalUnits m.2.1)⁻¹ * (permutation r K w)⁻¹,
      bruhatFiberAct_fst_mem r K w u m⟩,
    m.2.1,
    Subgroup.inclusion (permutationUnipotentPlus_le_upperUnipotent r K w) u * m.2.2)

variable {r K w}

/-- Evaluation of the first component in the actual general linear group. -/
@[simp]
theorem bruhatFiberAct_fst_val (u : permutationUnipotentPlus r K w)
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    (bruhatFiberAct r K w u m).1.val =
      m.1.val * permutation r K w * Iwasawa.diagonalUnits m.2.1 * u.val⁻¹ *
        (Iwasawa.diagonalUnits m.2.1)⁻¹ * (permutation r K w)⁻¹ :=
  rfl

/-- Evaluation of the first component on underlying matrices. -/
theorem bruhatFiberAct_fst_matrix (u : permutationUnipotentPlus r K w)
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    ((bruhatFiberAct r K w u m).1.val : Matrix (Fin r) (Fin r) K) =
      (m.1.val : Matrix (Fin r) (Fin r) K) * (permutation r K w : Matrix (Fin r) (Fin r) K) *
        (Iwasawa.diagonalUnits m.2.1 : Matrix (Fin r) (Fin r) K) *
        ((u.val⁻¹ : Langlands.GeneralLinear r K) : Matrix (Fin r) (Fin r) K) *
        (((Iwasawa.diagonalUnits m.2.1)⁻¹ : Langlands.GeneralLinear r K) :
          Matrix (Fin r) (Fin r) K) *
        (((permutation r K w)⁻¹ : Langlands.GeneralLinear r K) : Matrix (Fin r) (Fin r) K) := by
  rw [bruhatFiberAct_fst_val]
  simp only [Units.val_mul]

/-- The diagonal parameter is preserved. -/
@[simp]
theorem bruhatFiberAct_snd_fst (u : permutationUnipotentPlus r K w)
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    (bruhatFiberAct r K w u m).2.1 = m.2.1 :=
  rfl

/-- The last component is left multiplication through the actual inclusion `U_w⁺ ≤ U`. -/
theorem bruhatFiberAct_snd_snd (u : permutationUnipotentPlus r K w)
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    (bruhatFiberAct r K w u m).2.2 =
      Subgroup.inclusion (permutationUnipotentPlus_le_upperUnipotent r K w) u * m.2.2 :=
  rfl

/-- Evaluation of the last component in the actual general linear group. -/
@[simp]
theorem bruhatFiberAct_snd_snd_val (u : permutationUnipotentPlus r K w)
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    (bruhatFiberAct r K w u m).2.2.val = u.val * m.2.2.val :=
  rfl

/-- The identity law. -/
@[simp]
theorem bruhatFiberAct_one (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    bruhatFiberAct r K w 1 m = m := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext rfl (Subtype.ext ?_))
  · rw [bruhatFiberAct_fst_val, OneMemClass.coe_one]
    group
  · rw [bruhatFiberAct_snd_snd_val, OneMemClass.coe_one, one_mul]

/-- The composition law `u • (v • m) = (u * v) • m`. -/
theorem bruhatFiberAct_bruhatFiberAct (u v : permutationUnipotentPlus r K w)
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    bruhatFiberAct r K w u (bruhatFiberAct r K w v m) = bruhatFiberAct r K w (u * v) m := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext rfl (Subtype.ext ?_))
  · rw [bruhatFiberAct_fst_val, bruhatFiberAct_fst_val, bruhatFiberAct_fst_val,
      bruhatFiberAct_snd_fst, Subgroup.coe_mul]
    group
  · rw [bruhatFiberAct_snd_snd_val, bruhatFiberAct_snd_snd_val, bruhatFiberAct_snd_snd_val,
      Subgroup.coe_mul, mul_assoc]

variable (r K w) in
/-- The action bundled as a `MulAction`. It is a definition, not a global instance. -/
abbrev bruhatFiberMulAction :
    MulAction (permutationUnipotentPlus r K w)
      (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) where
  smul := bruhatFiberAct r K w
  one_smul := bruhatFiberAct_one
  mul_smul u v m := (bruhatFiberAct_bruhatFiberAct u v m).symm

theorem bruhatFiberMulAction_smul (u : permutationUnipotentPlus r K w)
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    letI := bruhatFiberMulAction r K w
    u • m = bruhatFiberAct r K w u m :=
  rfl

/-- Fiber law: the action preserves Shalika's multiplication map `(u₁, d, u₂) ↦ u₁ p h(d) u₂`. -/
theorem upperBruhatTorusMap_bruhatFiberAct (u : permutationUnipotentPlus r K w)
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    upperBruhatTorusMap r w (bruhatFiberAct r K w u m) = upperBruhatTorusMap r w m := by
  apply Subtype.ext
  rw [upperBruhatTorusMap_val, upperBruhatTorusMap_val, bruhatFiberAct_fst_val,
    bruhatFiberAct_snd_fst, bruhatFiberAct_snd_snd_val]
  group

end Action

section Topology

variable (r : ℕ) (K : Type uK) [Field K] (w : Equiv.Perm (Fin r))
variable [TopologicalSpace K] [IsTopologicalRing K]

/-- Joint continuity of the action for the inherited matrix-group topologies. -/
@[fun_prop]
theorem continuous_bruhatFiberAct :
    Continuous fun x : permutationUnipotentPlus r K w ×
        (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) =>
      bruhatFiberAct r K w x.1 x.2 := by
  have hh : Continuous fun x : permutationUnipotentPlus r K w ×
      (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) =>
        Iwasawa.diagonalUnits x.2.2.1 :=
    (continuous_diagonalUnits r).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))
  have hu : Continuous fun x : permutationUnipotentPlus r K w ×
      (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) => x.1.val :=
    continuous_subtype_val.comp continuous_fst
  have h₁ : Continuous fun x : permutationUnipotentPlus r K w ×
      (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) => x.2.1.val :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have h₂ : Continuous fun x : permutationUnipotentPlus r K w ×
      (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) => x.2.2.2.val :=
    continuous_subtype_val.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))
  refine Continuous.prodMk (continuous_induced_rng.2 ?_)
    (Continuous.prodMk (continuous_fst.comp (continuous_snd.comp continuous_snd))
      (continuous_induced_rng.2 ?_))
  · exact ((((h₁.mul continuous_const).mul hh).mul hu.inv).mul hh.inv).mul continuous_const
  · exact hu.mul h₂

/-- Continuity of each fixed-`u` map. -/
theorem continuous_bruhatFiberAct_left (u : permutationUnipotentPlus r K w) :
    Continuous (bruhatFiberAct r K w u) :=
  (continuous_bruhatFiberAct r K w).comp (f := fun m => (u, m))
    (continuous_const.prodMk continuous_id)

/-- Continuity of each orbit map `u ↦ u • m`. -/
theorem continuous_bruhatFiberAct_orbit
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    Continuous fun u : permutationUnipotentPlus r K w => bruhatFiberAct r K w u m :=
  (continuous_bruhatFiberAct r K w).comp (f := fun u => (u, m))
    (continuous_id.prodMk continuous_const)

/-- Each fixed-`u` map is a homeomorphism, with inverse the map for `u⁻¹`. -/
def bruhatFiberActHomeomorph (u : permutationUnipotentPlus r K w) :
    (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) ≃ₜ
      (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) where
  toFun := bruhatFiberAct r K w u
  invFun := bruhatFiberAct r K w u⁻¹
  left_inv m := by rw [bruhatFiberAct_bruhatFiberAct, inv_mul_cancel, bruhatFiberAct_one]
  right_inv m := by rw [bruhatFiberAct_bruhatFiberAct, mul_inv_cancel, bruhatFiberAct_one]
  continuous_toFun := continuous_bruhatFiberAct_left r K w u
  continuous_invFun := continuous_bruhatFiberAct_left r K w u⁻¹

@[simp]
theorem bruhatFiberActHomeomorph_apply (u : permutationUnipotentPlus r K w)
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    bruhatFiberActHomeomorph r K w u m = bruhatFiberAct r K w u m :=
  rfl

@[simp]
theorem bruhatFiberActHomeomorph_symm_apply (u : permutationUnipotentPlus r K w)
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    (bruhatFiberActHomeomorph r K w u).symm m = bruhatFiberAct r K w u⁻¹ m :=
  rfl

/-- Each slice `u ↦ α (u • m)` of a test function is continuous. -/
theorem continuous_bruhatFiberAct_slice
    (α : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K))
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    Continuous fun u : permutationUnipotentPlus r K w => α (bruhatFiberAct r K w u m) :=
  α.continuous.comp (continuous_bruhatFiberAct_orbit r K w m)

variable [T2Space K]

/-- `U_w⁺` is closed in the actual matrix general linear group. -/
theorem isClosed_permutationUnipotentPlus :
    IsClosed (permutationUnipotentPlus r K w : Set (Langlands.GeneralLinear r K)) := by
  have hU := UpperUnipotent.isClosed (R := K) (n := r)
  have he : (permutationUnipotentPlus r K w : Set (Langlands.GeneralLinear r K)) =
      (upperUnipotent r K : Set (Langlands.GeneralLinear r K)) ∩
        (fun g => permutation r K w * g * (permutation r K w)⁻¹) ⁻¹'
          (upperUnipotent r K : Set (Langlands.GeneralLinear r K)) :=
    Set.ext fun g => mem_permutationUnipotentPlus_iff r K w g
  rw [he]
  exact hU.inter (hU.preimage ((continuous_const.mul continuous_id).mul continuous_const))

/-- For each fixed `m`, the orbit map `u ↦ u • m` is a closed embedding of `U_w⁺`. -/
theorem isClosedEmbedding_bruhatFiberAct_orbit
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    IsClosedEmbedding fun u : permutationUnipotentPlus r K w => bruhatFiberAct r K w u m := by
  have hU : IsClosedEmbedding
      (Subtype.val : upperUnipotent r K → Langlands.GeneralLinear r K) :=
    (UpperUnipotent.isClosed (R := K) (n := r)).isClosedEmbedding_subtypeVal
  have hj : IsClosedEmbedding (Prod.map
      (Subtype.val : upperUnipotent r K → Langlands.GeneralLinear r K)
      (Prod.map (id : (Fin r → Kˣ) → (Fin r → Kˣ))
        (Subtype.val : upperUnipotent r K → Langlands.GeneralLinear r K))) :=
    hU.prodMap (IsClosedEmbedding.id.prodMap hU)
  have hP : IsClosedEmbedding
      (Subtype.val : permutationUnipotentPlus r K w → Langlands.GeneralLinear r K) :=
    (isClosed_permutationUnipotentPlus r K w).isClosedEmbedding_subtypeVal
  have hΦ : IsClosedEmbedding fun v : Langlands.GeneralLinear r K =>
      (m.1.val * permutation r K w * Iwasawa.diagonalUnits m.2.1 * v⁻¹ *
        (Iwasawa.diagonalUnits m.2.1)⁻¹ * (permutation r K w)⁻¹, m.2.1, v * m.2.2.val) := by
    refine Function.LeftInverse.isClosedEmbedding
      (f := fun x : Langlands.GeneralLinear r K × (Fin r → Kˣ) ×
        Langlands.GeneralLinear r K => x.2.2 * m.2.2.val⁻¹) (fun v => ?_) ?_ ?_
    · exact mul_inv_cancel_right v m.2.2.val
    · exact (continuous_snd.comp continuous_snd).mul continuous_const
    · exact Continuous.prodMk
        ((continuous_const.mul continuous_inv).mul continuous_const |>.mul continuous_const)
        (continuous_const.prodMk (continuous_id.mul continuous_const))
  rw [← hj.of_comp_iff]
  exact hΦ.comp hP

end Topology

section Average

variable (r : ℕ) (K : Type uK) [Field K] (w : Equiv.Perm (Fin r))
variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

/-- Each slice `u ↦ α (u • m)` of a test function has compact support, because the orbit
map is a closed embedding. -/
theorem hasCompactSupport_bruhatFiberAct_slice
    (α : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K))
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    HasCompactSupport fun u : permutationUnipotentPlus r K w => α (bruhatFiberAct r K w u m) :=
  α.hasCompactSupport.comp_isClosedEmbedding (isClosedEmbedding_bruhatFiberAct_orbit r K w m)

variable (μ : letI := borel (permutationUnipotentPlus r K w)
  Measure (permutationUnipotentPlus r K w))
variable [IsFiniteMeasureOnCompacts μ]

/-- Every displayed slice is Bochner integrable for the Borel measure `μ`. -/
theorem integrable_bruhatFiberAct_slice
    (α : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K))
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    Integrable (fun u : permutationUnipotentPlus r K w => α (bruhatFiberAct r K w u m)) μ := by
  let := borel (permutationUnipotentPlus r K w)
  let : BorelSpace (permutationUnipotentPlus r K w) := ⟨rfl⟩
  exact (continuous_bruhatFiberAct_slice r K w α m).integrable_of_hasCompactSupport
    (hasCompactSupport_bruhatFiberAct_slice r K w α m)

/-- The raw fiber integral `m ↦ ∫ α (u • m) dμ(u)` (the right side of Shalika's (1.11)),
as a complex linear map from test functions on `U × ((Fin r → Kˣ) × U)` to complex
functions on the same space. It is not descended to the cell. -/
def bruhatFiberAverage :
    SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) →ₗ[ℂ]
      (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K → ℂ) where
  toFun α m := ∫ u, α (bruhatFiberAct r K w u m) ∂μ
  map_add' α β := by
    funext m
    simp only [Submodule.coe_add, Pi.add_apply]
    exact integral_add (integrable_bruhatFiberAct_slice r K w μ α m)
      (integrable_bruhatFiberAct_slice r K w μ β m)
  map_smul' c α := by
    funext m
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

/-- The pointwise evaluation law. -/
theorem bruhatFiberAverage_apply
    (α : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K))
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    bruhatFiberAverage r K w μ α m = ∫ u, α (bruhatFiberAct r K w u m) ∂μ :=
  rfl

/-- At a point where the raw average is nonzero, some point of the orbit lies in the
support of the test function. -/
theorem exists_bruhatFiberAct_mem_support_of_mem_support
    {α : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K)}
    {m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K}
    (hm : m ∈ Function.support (bruhatFiberAverage r K w μ α)) :
    ∃ u : permutationUnipotentPlus r K w,
      bruhatFiberAct r K w u m ∈ Function.support (α : _ → ℂ) := by
  by_contra h
  apply hm
  rw [bruhatFiberAverage_apply]
  have hz : (fun u : permutationUnipotentPlus r K w => α (bruhatFiberAct r K w u m)) =
      fun _ => 0 := by
    funext u
    by_contra hu
    exact h ⟨u, hu⟩
  rw [hz, integral_zero]

/-- A point in the nonzero support of the raw average has an orbit point in the
topological support of the test function. -/
theorem exists_bruhatFiberAct_mem_tsupport_of_mem_support
    {α : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K)}
    {m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K}
    (hm : m ∈ Function.support (bruhatFiberAverage r K w μ α)) :
    ∃ u : permutationUnipotentPlus r K w,
      bruhatFiberAct r K w u m ∈ tsupport (α : _ → ℂ) := by
  obtain ⟨u, hu⟩ := exists_bruhatFiberAct_mem_support_of_mem_support r K w μ hm
  exact ⟨u, subset_tsupport _ hu⟩

/-- Invariance for a measure invariant under right multiplication on `U_w⁺`:
evaluating at `v • m` uses `u • (v • m) = (u * v) • m` and the change of variables
`u ↦ u * v`. -/
theorem bruhatFiberAverage_bruhatFiberAct
    (hμ : letI := borel (permutationUnipotentPlus r K w); μ.IsMulRightInvariant)
    (α : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K))
    (v : permutationUnipotentPlus r K w)
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    bruhatFiberAverage r K w μ α (bruhatFiberAct r K w v m) =
      bruhatFiberAverage r K w μ α m := by
  let := borel (permutationUnipotentPlus r K w)
  let : BorelSpace (permutationUnipotentPlus r K w) := ⟨rfl⟩
  have := hμ
  rw [bruhatFiberAverage_apply, bruhatFiberAverage_apply]
  simp only [bruhatFiberAct_bruhatFiberAct]
  exact integral_mul_right_eq_self (fun u => α (bruhatFiberAct r K w u m)) v

end Average

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ)
  (w : Equiv.Perm (Fin (n + 1)))

/-- The canonical topology of a p-adic field satisfies the topological hypotheses. -/
theorem padic_bruhatFiberAverage_hypotheses :
    letI := F.canonicalTopologicalData.topology
    IsTopologicalRing F.Carrier ∧ T2Space F.Carrier := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  exact ⟨inferInstance, F.canonicalTopologicalData.fieldT2⟩

/-- Specialization to the canonical topology of every p-adic field in rank `n + 1`:
for every Borel measure on `U_w⁺` finite on compact sets, the orbit maps are closed
embeddings, the slices are integrable, the raw average evaluates by the displayed Bochner
integral, its nonzero support is controlled by the topological support, and it is
invariant under the action when the measure is right invariant. -/
theorem padic_bruhatFiberAverage :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := F.canonicalTopologicalData.fieldT2
    letI := borel (permutationUnipotentPlus (n + 1) F.Carrier w)
    ∀ (μ : Measure (permutationUnipotentPlus (n + 1) F.Carrier w))
      [IsFiniteMeasureOnCompacts μ],
      (∀ m : upperUnipotent (n + 1) F.Carrier × (Fin (n + 1) → F.Carrierˣ) ×
          upperUnipotent (n + 1) F.Carrier,
        IsClosedEmbedding fun u : permutationUnipotentPlus (n + 1) F.Carrier w =>
          bruhatFiberAct (n + 1) F.Carrier w u m) ∧
      ∀ (α : SchwartzBruhat (upperUnipotent (n + 1) F.Carrier ×
          (Fin (n + 1) → F.Carrierˣ) × upperUnipotent (n + 1) F.Carrier))
        (m : upperUnipotent (n + 1) F.Carrier × (Fin (n + 1) → F.Carrierˣ) ×
          upperUnipotent (n + 1) F.Carrier),
        Integrable (fun u => α (bruhatFiberAct (n + 1) F.Carrier w u m)) μ ∧
        bruhatFiberAverage (n + 1) F.Carrier w μ α m =
          ∫ u, α (bruhatFiberAct (n + 1) F.Carrier w u m) ∂μ ∧
        (m ∈ Function.support (bruhatFiberAverage (n + 1) F.Carrier w μ α) →
          ∃ u, bruhatFiberAct (n + 1) F.Carrier w u m ∈ tsupport (α : _ → ℂ)) ∧
        (μ.IsMulRightInvariant → ∀ v,
          bruhatFiberAverage (n + 1) F.Carrier w μ α
              (bruhatFiberAct (n + 1) F.Carrier w v m) =
            bruhatFiberAverage (n + 1) F.Carrier w μ α m) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := F.canonicalTopologicalData.fieldT2
  intro μ _
  refine ⟨fun m => isClosedEmbedding_bruhatFiberAct_orbit (n + 1) F.Carrier w m,
    fun α m => ⟨integrable_bruhatFiberAct_slice (n + 1) F.Carrier w μ α m,
      bruhatFiberAverage_apply (n + 1) F.Carrier w μ α m,
      exists_bruhatFiberAct_mem_tsupport_of_mem_support (n + 1) F.Carrier w μ,
      fun hμ v => bruhatFiberAverage_bruhatFiberAct (n + 1) F.Carrier w μ hμ α v m⟩⟩

end Padic

end Langlands.Whittaker
