import Langlands.Group.GL.BlockDeterminant
import Langlands.HarmonicAnalysis.HaarConjugacy
import Langlands.Representation.Derivative.MirabolicProductMinusRightPsiZero
import Langlands.Representation.Induction.BinaryPositiveCompact

/-!
# Groups for the positive-rank `Ψ⁻` clause of BZ77 Proposition 4.13(c)
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MeasureTheory MeasureTheory.Measure
open scoped TensorProduct NNReal

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct
  HarmonicAnalysis

universe uF uV

/-! ## The two coordinate blocks of `Fin (m + r)` -/

section Indices

variable {m r : ℕ}

/-- The `j`-th of the first `r` coordinates of `Fin (m + r)`. -/
def rightPsiFirst (j : Fin r) : Fin (m + r) :=
  Fin.cast (Nat.add_comm r m) (Fin.castAdd m j)

/-- The `i`-th of the last `m` coordinates of `Fin (m + r)`. -/
def rightPsiSecond (i : Fin m) : Fin (m + r) :=
  Fin.cast (Nat.add_comm r m) (Fin.natAdd r i)

@[simp] theorem rightPsiFirst_val (j : Fin r) : (rightPsiFirst (m := m) j).val = j.val := rfl

@[simp] theorem rightPsiSecond_val (i : Fin m) :
    (rightPsiSecond (r := r) i).val = r + i.val := rfl

theorem rightIndex_inl_castSucc (j : Fin r) :
    rightIndex m r (Sum.inl j.castSucc) = (rightPsiFirst (m := m) j).castSucc :=
  Fin.ext (by simp)

theorem rightIndex_inr (i : Fin m) :
    rightIndex m r (Sum.inr i) = (rightPsiSecond (r := r) i).castSucc :=
  Fin.ext (by simp)

theorem rightPsiFirst_ne_second (j : Fin r) (i : Fin m) :
    rightPsiFirst (m := m) j ≠ rightPsiSecond i := by
  intro h
  have h' := congrArg Fin.val h
  simp only [rightPsiFirst_val, rightPsiSecond_val] at h'
  omega

theorem rightPsiFirst_injective : Function.Injective (rightPsiFirst (m := m) (r := r)) :=
  fun _ _ h => Fin.ext (by simpa using congrArg Fin.val h)

theorem rightPsiSecond_injective : Function.Injective (rightPsiSecond (m := m) (r := r)) :=
  fun _ _ h => Fin.ext (by simpa using congrArg Fin.val h)

/-- Every coordinate of `Fin (m + r)` is a first or a second one. -/
theorem rightPsi_cases (a : Fin (m + r)) :
    (∃ j, a = rightPsiFirst (m := m) j) ∨ (∃ i, a = rightPsiSecond (r := r) i) := by
  by_cases h : a.val < r
  · exact Or.inl ⟨⟨a.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨a.val - r, by omega⟩, Fin.ext (by simp only [rightPsiSecond_val]; omega)⟩

end Indices

/-! ## The parabolic `Q`, its preimage `P`, and the inducing subgroup -/

section Groups

variable {R : Type*} [CommRing R] {m r : ℕ} (hr : 0 < r) (hm : 0 < m)

/-- The entry-preserving identification `GL_(m+r) ≃ GL_(r+m)`. -/
abbrev rightPsiCast (m r : ℕ) (R : Type*) [CommRing R] :
    GeneralLinear (m + r) R ≃* GeneralLinear (r + m) R :=
  reindex (R := R) (finCongr (Nat.add_comm m r))

theorem rightPsiCast_apply (g : GeneralLinear (m + r) R) (a b : Fin (r + m)) :
    (rightPsiCast m r R g).val a b =
      g.val (Fin.cast (Nat.add_comm r m) a) (Fin.cast (Nat.add_comm r m) b) := rfl

/-- The cast is the explicit rank cast of the general linear group. -/
theorem rightPsiCast_eq (g : GeneralLinear (m + r) R) :
    rightPsiCast m r R g = generalLinearCastHom (Nat.add_comm r m) g := by
  apply Units.ext
  ext a b
  rw [generalLinearCastHom_apply]
  rfl

/-- `Q`: the parabolic of `GL_(m+r)` whose last `m` rows vanish on the first `r`
columns, the preimage of the binary parabolic of shape `(r, m)`. -/
def rightPsiParabolic : Subgroup (GeneralLinear (m + r) R) :=
  ((BlockShape.binary r m hr hm).parabolic R).comap (rightPsiCast m r R).toMonoidHom

theorem mem_rightPsiParabolic_iff (g : GeneralLinear (m + r) R) :
    g ∈ rightPsiParabolic (R := R) hr hm ↔
      ∀ (i : Fin m) (j : Fin r), g.val (rightPsiSecond i) (rightPsiFirst j) = 0 := by
  change rightPsiCast m r R g ∈ (BlockShape.binary r m hr hm).parabolic R ↔ _
  rw [BlockShape.mem_parabolic_iff]
  constructor
  · intro h i j
    have h' := h (1 : Fin 2) (0 : Fin 2) i j (show (0 : Fin 2) < 1 from by decide)
    rw [BlockShape.binary_index_one, BlockShape.binary_index_zero] at h'
    exact h'
  · intro h i j x y hij
    fin_cases i <;> fin_cases j
    · exact False.elim (lt_irrefl _ hij)
    · simp at hij
    · change (rightPsiCast m r R g).val ((BlockShape.binary r m hr hm).index (1 : Fin 2) x)
        ((BlockShape.binary r m hr hm).index (0 : Fin 2) y) = 0
      rw [BlockShape.binary_index_one, BlockShape.binary_index_zero]
      exact h x y
    · exact False.elim (lt_irrefl _ hij)

/-- `P`: the mirabolic elements whose Levi projection lies in `Q`. -/
def rightPsiStages : Subgroup (mirabolic (m + r) R) :=
  (rightPsiParabolic (R := R) hr hm).comap (projection (n := m + r) (F := R))

theorem mem_rightPsiStages_iff (g : mirabolic (m + r) R) :
    g ∈ rightPsiStages (R := R) hr hm ↔ projection g ∈ rightPsiParabolic (R := R) hr hm :=
  Iff.rfl

theorem ker_projection_le_rightPsiStages :
    (projection (n := m + r) (F := R)).ker ≤ rightPsiStages (R := R) hr hm := by
  intro g hg
  rw [mem_rightPsiStages_iff, (MonoidHom.mem_ker).mp hg]
  exact Subgroup.one_mem _

theorem rightSubgroup_le_rightPsiStages :
    rightSubgroup m r R ≤ rightPsiStages (R := R) hr hm := by
  intro g hg
  rw [mem_rightPsiStages_iff, mem_rightPsiParabolic_iff]
  intro i j
  rw [projection_apply, ← rightIndex_inr, ← rightIndex_inl_castSucc]
  exact (mem_rightSubgroup_iff_entry g).mp hg i j.castSucc

/-- The Levi embedding sends `Q` into the case (III) inducing subgroup. -/
theorem levi_mem_rightSubgroup {l : GeneralLinear (m + r) R}
    (hl : l ∈ rightPsiParabolic (R := R) hr hm) : levi l ∈ rightSubgroup m r R := by
  rw [mem_rightSubgroup_iff_entry]
  intro i j
  rw [rightIndex_inr]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [rightIndex_last]
    exact levi_last l _
  · rw [rightIndex_inl_castSucc, levi_first]
    exact (mem_rightPsiParabolic_iff hr hm l).mp hl i j

theorem levi_mem_rightPsiStages_iff (l : GeneralLinear (m + r) R) :
    levi l ∈ rightPsiStages (R := R) hr hm ↔ l ∈ rightPsiParabolic (R := R) hr hm := by
  rw [mem_rightPsiStages_iff, projection_levi]

/-- The section of `P` over `Q` takes values in the inducing subgroup. -/
theorem rightPsiStages_section_mem
    (l : (rightPsiStages (R := R) hr hm).comap (levi (n := m + r) (F := R))) :
    levi (l : GeneralLinear (m + r) R) ∈ rightSubgroup m r R :=
  levi_mem_rightSubgroup hr hm ((levi_mem_rightPsiStages_iff hr hm _).mp l.property)

end Groups

section GroupTopology

variable {R : Type*} [CommRing R] [TopologicalSpace R] [T2Space R] {m r : ℕ}
  (hr : 0 < r) (hm : 0 < m)

omit [T2Space R] in
theorem continuous_rightPsiCast : Continuous (rightPsiCast m r R) :=
  (reindexContinuous (R := R) (finCongr (Nat.add_comm m r))).continuous

theorem isClosed_rightPsiParabolic :
    IsClosed (rightPsiParabolic (R := R) hr hm : Set (GeneralLinear (m + r) R)) :=
  (BlockShape.isClosed_parabolic (B := BlockShape.binary r m hr hm) R).preimage
    (continuous_rightPsiCast (R := R))

theorem isClosed_rightPsiStages :
    IsClosed (rightPsiStages (R := R) hr hm : Set (mirabolic (m + r) R)) :=
  (isClosed_rightPsiParabolic hr hm).preimage continuous_projection

end GroupTopology

/-! ## The diagonal blocks of `Q` -/

section Blocks

variable {R : Type*} [CommRing R] {m r : ℕ} (hr : 0 < r) (hm : 0 < m)

/-- The diagonal `r × r` block `A` of an element `[[A, X], [0, D]]` of `Q`. -/
def rightPsiFirstBlock (l : GeneralLinear (m + r) R)
    (hl : l ∈ rightPsiParabolic (R := R) hr hm) : GeneralLinear r R :=
  (BlockShape.binary r m hr hm).leviProjection R ⟨rightPsiCast m r R l, hl⟩ (0 : Fin 2)

/-- The diagonal `m × m` block `D` of an element `[[A, X], [0, D]]` of `Q`. -/
def rightPsiSecondBlock (l : GeneralLinear (m + r) R)
    (hl : l ∈ rightPsiParabolic (R := R) hr hm) : GeneralLinear m R :=
  (BlockShape.binary r m hr hm).leviProjection R ⟨rightPsiCast m r R l, hl⟩ (1 : Fin 2)

theorem rightPsiFirstBlock_apply (l : GeneralLinear (m + r) R)
    (hl : l ∈ rightPsiParabolic (R := R) hr hm) (i j : Fin r) :
    (rightPsiFirstBlock hr hm l hl).val i j = l.val (rightPsiFirst i) (rightPsiFirst j) := by
  change (rightPsiCast m r R l).val ((BlockShape.binary r m hr hm).index (0 : Fin 2) i)
    ((BlockShape.binary r m hr hm).index (0 : Fin 2) j) = _
  rw [BlockShape.binary_index_zero, BlockShape.binary_index_zero]
  rfl

theorem rightPsiSecondBlock_apply (l : GeneralLinear (m + r) R)
    (hl : l ∈ rightPsiParabolic (R := R) hr hm) (i j : Fin m) :
    (rightPsiSecondBlock hr hm l hl).val i j = l.val (rightPsiSecond i) (rightPsiSecond j) := by
  change (rightPsiCast m r R l).val ((BlockShape.binary r m hr hm).index (1 : Fin 2) i)
    ((BlockShape.binary r m hr hm).index (1 : Fin 2) j) = _
  rw [BlockShape.binary_index_one, BlockShape.binary_index_one]
  rfl

/-- `det l = det A · det D` on `Q`. -/
theorem determinant_rightPsi (l : GeneralLinear (m + r) R)
    (hl : l ∈ rightPsiParabolic (R := R) hr hm) :
    determinant l = determinant (rightPsiFirstBlock hr hm l hl) *
      determinant (rightPsiSecondBlock hr hm l hl) := by
  have h1 : determinant (rightPsiCast m r R l) = determinant l := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    exact Matrix.det_reindex_self _ _
  rw [← h1]
  exact (determinant_blockParabolic (BlockShape.binary r m hr hm)
    ⟨rightPsiCast m r R l, hl⟩).trans (Fin.prod_univ_two _)

/-- The case (III) blocks of `diag(l, 1)` for `l ∈ Q` are `(diag(A, 1), D)`. -/
theorem rightProjection_levi (l : GeneralLinear (m + r) R)
    (hl : l ∈ rightPsiParabolic (R := R) hr hm) :
    rightProjection (⟨levi l, levi_mem_rightSubgroup hr hm hl⟩ : rightSubgroup m r R) =
      (levi (rightPsiFirstBlock hr hm l hl), rightPsiSecondBlock hr hm l hl) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Units.ext
    ext i j
    rw [rightProjection_mirabolic_apply]
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [rightIndex_last, levi_bottom, levi_bottom]
      simp
    · rw [rightIndex_last, rightIndex_inl_castSucc, levi_bottom, levi_bottom,
        ite_eq_right (Fin.castSucc_ne_last _), ite_eq_right (Fin.castSucc_ne_last _)]
    · rw [rightIndex_last, rightIndex_inl_castSucc, levi_last, levi_last]
    · rw [rightIndex_inl_castSucc, rightIndex_inl_castSucc, levi_first, levi_first,
        rightPsiFirstBlock_apply]
  · apply Units.ext
    ext i j
    rw [rightProjection_gl_apply, rightIndex_inr, rightIndex_inr, levi_first,
      rightPsiSecondBlock_apply]

end Blocks

/-! ## The inducing elements in the radical -/

section Kernel

variable {R : Type*} [CommRing R] {m r : ℕ}

/-- `N`: the elements of the case (III) inducing subgroup in the radical `ker projection`. -/
abbrev rightPsiKernel (m r : ℕ) (R : Type*) [CommRing R] : Subgroup (rightSubgroup m r R) :=
  (projection (n := m + r) (F := R)).ker.comap (rightSubgroup m r R).subtype

theorem projection_entry_of_eq_one {n : ℕ} {g : mirabolic n R} (hg : projection g = 1)
    (a b : Fin n) : g.val.val a.castSucc b.castSucc = if a = b then 1 else 0 := by
  rw [← projection_apply, hg, Units.val_one, Matrix.one_apply]

theorem rightProjection_fst_mem_radical (g : rightPsiKernel m r R) :
    (rightProjection g.val).1 ∈ radical r R := by
  rw [mem_radical]
  intro i j
  rw [rightProjection_mirabolic_apply, rightIndex_inl_castSucc]
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [rightIndex_last, g.val.val.property, ite_eq_right (Fin.castSucc_ne_last _),
      ite_eq_right (Fin.castSucc_ne_last _).symm]
  · rw [rightIndex_inl_castSucc, projection_entry_of_eq_one (g := g.val.val) g.property]
    simp only [rightPsiFirst_injective.eq_iff, Fin.castSucc_inj]

theorem rightProjection_snd_of_mem_kernel (g : rightPsiKernel m r R) :
    (rightProjection g.val).2 = 1 := by
  apply Units.ext
  ext i j
  rw [rightProjection_gl_apply, rightIndex_inr, rightIndex_inr,
    projection_entry_of_eq_one (g := g.val.val) g.property, Units.val_one, Matrix.one_apply]
  simp only [rightPsiSecond_injective.eq_iff]

theorem projection_rightSection_radical (u : radical r R) :
    projection ((rightSection ((u : mirabolic r R), (1 : GeneralLinear m R)) :
      rightSubgroup m r R) : mirabolic (m + r) R) = 1 := by
  apply Units.ext
  ext a b
  rw [projection_apply, Units.val_one, Matrix.one_apply]
  change (rightMatrix (u : mirabolic r R) (1 : GeneralLinear m R) 0).val.val.val
    a.castSucc b.castSucc = _
  rcases rightPsi_cases a with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    rcases rightPsi_cases b with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [← rightIndex_inl_castSucc i, ← rightIndex_inl_castSucc j, rightMatrix_apply,
      Matrix.fromBlocks_apply₁₁, u.property i.castSucc j]
    simp only [Fin.castSucc_inj, rightPsiFirst_injective.eq_iff]
  · rw [← rightIndex_inl_castSucc i, ← rightIndex_inr j, rightMatrix_apply,
      Matrix.fromBlocks_apply₁₂, ite_eq_right (rightPsiFirst_ne_second i j), extendRectangle_zero]
    rfl
  · rw [← rightIndex_inr i, ← rightIndex_inl_castSucc j, rightMatrix_apply,
      Matrix.fromBlocks_apply₂₁, ite_eq_right (rightPsiFirst_ne_second j i).symm]
    rfl
  · rw [← rightIndex_inr i, ← rightIndex_inr j, rightMatrix_apply,
      Matrix.fromBlocks_apply₂₂, Units.val_one, Matrix.one_apply]
    simp only [rightPsiSecond_injective.eq_iff]

theorem rightSection_of_mem_kernel (g : rightPsiKernel m r R) :
    rightSection ((rightProjection g.val).1, (1 : GeneralLinear m R)) = g.val := by
  have hX : rightOffDiagonal g.val = 0 := by
    ext i j
    change g.val.val.val.val (rightIndex m r (Sum.inl i.castSucc))
      (rightIndex m r (Sum.inr j)) = 0
    rw [rightIndex_inl_castSucc, rightIndex_inr,
      projection_entry_of_eq_one (g := g.val.val) g.property,
      ite_eq_right (rightPsiFirst_ne_second i j)]
  have h := rightMatrix_parts g.val
  rw [rightProjection_snd_of_mem_kernel g, hX] at h
  exact h

/-- `N ≃ V_(r+1)`: an element of `N` is determined by its mirabolic block, which lies
in the radical of `P_(r+1)`; the inverse is the case (III) section `u ↦ s(u, 1)`. -/
def rightPsiKernelEquiv : rightPsiKernel m r R ≃* radical r R where
  toFun g := ⟨(rightProjection g.val).1, rightProjection_fst_mem_radical g⟩
  invFun u := ⟨rightSection ((u : mirabolic r R), (1 : GeneralLinear m R)),
    projection_rightSection_radical u⟩
  left_inv g := Subtype.ext (rightSection_of_mem_kernel g)
  right_inv u := Subtype.ext
    (congrArg Prod.fst (rightProjection_section ((u : mirabolic r R), (1 : GeneralLinear m R))))
  map_mul' a b := Subtype.ext (congrArg Prod.fst (map_mul rightProjection a.val b.val))

@[simp] theorem rightPsiKernelEquiv_apply (g : rightPsiKernel m r R) :
    (rightPsiKernelEquiv g : mirabolic r R) = (rightProjection g.val).1 := rfl

@[simp] theorem rightPsiKernelEquiv_symm_apply (u : radical r R) :
    ((rightPsiKernelEquiv (m := m)).symm u : rightSubgroup m r R) =
      rightSection ((u : mirabolic r R), (1 : GeneralLinear m R)) := rfl

/-- On `N` the case (III) blocks are `(u, 1)` with `u` in the radical. -/
theorem rightProjection_of_mem_kernel (g : rightPsiKernel m r R) :
    rightProjection g.val = ((rightPsiKernelEquiv g : mirabolic r R), 1) :=
  Prod.ext rfl (rightProjection_snd_of_mem_kernel g)

variable [TopologicalSpace R]

/-- The identification `N ≃ V_(r+1)` is a homeomorphism. -/
def rightPsiKernelContinuousEquiv : rightPsiKernel m r R ≃ₜ* radical r R where
  toMulEquiv := rightPsiKernelEquiv
  continuous_toFun :=
    ((continuous_fst.comp (continuous_rightProjection.comp continuous_subtype_val))).subtype_mk _
  continuous_invFun :=
    (continuous_rightSection.comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _

@[simp] theorem rightPsiKernelContinuousEquiv_apply (g : rightPsiKernel m r R) :
    (rightPsiKernelContinuousEquiv g : mirabolic r R) = (rightProjection g.val).1 := rfl

end Kernel


/-! ## The split-stage data of the comparison -/

section Stages

variable {R : Type*} [CommRing R] {m r : ℕ} (hr : 0 < r) (hm : 0 < m)

/-- The retraction `P → K` of the two-stage comparison, `K = P.comap levi`. -/
abbrev rightPsiRetraction :
    rightPsiStages (R := R) hr hm →*
      (rightPsiStages (R := R) hr hm).comap (levi (n := m + r) (F := R)) :=
  Induction.splitStagesRetraction projection levi projection_levi _
    (ker_projection_le_rightPsiStages hr hm)

/-- The inducing subgroup inside `P`. -/
abbrev rightPsiInducing : Subgroup (rightPsiStages (R := R) hr hm) :=
  (rightSubgroup m r R).subgroupOf (rightPsiStages (R := R) hr hm)

theorem rightPsiSection_mem
    (l : (rightPsiStages (R := R) hr hm).comap (levi (n := m + r) (F := R))) :
    (levi (n := m + r) (F := R)).subgroupComap (rightPsiStages (R := R) hr hm) l ∈
      rightPsiInducing (R := R) hr hm :=
  rightPsiStages_section_mem hr hm l

theorem rightPsiLevi_mem
    (l : (rightPsiStages (R := R) hr hm).comap (levi (n := m + r) (F := R))) :
    (l : GeneralLinear (m + r) R) ∈ rightPsiParabolic (R := R) hr hm :=
  (levi_mem_rightPsiStages_iff hr hm _).mp l.property

theorem isClosed_rightPsiInducing [TopologicalSpace R] [T2Space R] :
    IsClosed (rightPsiInducing (R := R) hr hm : Set (rightPsiStages (R := R) hr hm)) :=
  rightSubgroup_isClosed.preimage continuous_subtype_val

end Stages

/-! ## The Haar ratio of the two kernels -/

section Haar

open Induction QuotientIntegration

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Conjugation by `diag(l, 1)⁻¹` on the radical `ker projection` of `P_(n+1)` scales
Haar measure by `|det l|⁻¹`. -/
theorem mulEquivHaarChar_splitKernelConjugation_levi (T : F.TopologicalData) (n : ℕ)
    (l : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (n + 1)
    letI := T.generalLinearLocallyCompactSpace (n + 1)
    letI := GeneralLinear.Mirabolic.locallyCompactSpace (n := n) (F := F.Carrier)
    ∀ [MeasurableSpace (projection (n := n) (F := F.Carrier)).ker]
      [BorelSpace (projection (n := n) (F := F.Carrier)).ker]
      [LocallyCompactSpace (projection (n := n) (F := F.Carrier)).ker],
      mulEquivHaarChar (splitKernelConjugation (projection (n := n) (F := F.Carrier)) levi l) =
        (T.determinantNorm n l : ℝ≥0)⁻¹ := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (n + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := n) (F := F.Carrier)
  intro _ _ _
  have hNr : (projection (n := n) (F := F.Carrier)).ker = radical n F.Carrier := ker_projection
  let : LocallyCompactSpace (radical n F.Carrier) := radical_isClosed.locallyCompactSpace
  let : MeasurableSpace (radical n F.Carrier) := borel _
  have : BorelSpace (radical n F.Carrier) := ⟨rfl⟩
  have hl : (levi l)⁻¹ ∈ Subgroup.normalizer
      (radical n F.Carrier : Set (mirabolic n F.Carrier)) := by
    rw [← hNr]
    simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]
  exact (mulEquivHaarChar_normalizerConj_congr hNr ((levi l)⁻¹)
    (by simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]) hl).trans
    (mulEquivHaarChar_conj_levi_inv T n l hl)

/-- `|det l| = |det A| |det D|` on `Q`. -/
theorem determinantNorm_rightPsi (T : F.TopologicalData) {m r : ℕ} (hr : 0 < r) (hm : 0 < m)
    (l : GeneralLinear (m + r) F.Carrier) (hl : l ∈ rightPsiParabolic (R := F.Carrier) hr hm) :
    T.determinantNorm (m + r) l = T.determinantNorm r (rightPsiFirstBlock hr hm l hl) *
      T.determinantNorm m (rightPsiSecondBlock hr hm l hl) := by
  change T.normalizedAbsUnits (determinant l) =
    T.normalizedAbsUnits (determinant (rightPsiFirstBlock hr hm l hl)) *
      T.normalizedAbsUnits (determinant (rightPsiSecondBlock hr hm l hl))
  rw [determinant_rightPsi hr hm l hl, map_mul]

/-- The Haar character of the two-stage comparison is `|det D|` at `[[A, X], [0, D]]`:
conjugation scales the kernel intersection `≅ V_(r+1)` by `|det A|⁻¹` and the kernel
`≅ V_(m+r+1)` by `|det l|⁻¹ = |det A|⁻¹ |det D|⁻¹`. -/
theorem rightPsiHaarRatio_apply (T : F.TopologicalData) {m r : ℕ} (hr : 0 < r) (hm : 0 < m)
    (l : (rightPsiStages (R := F.Carrier) hr hm).comap (levi (n := m + r) (F := F.Carrier))) :
    letI := T.topology
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (m + r + 1)
    letI := T.generalLinearLocallyCompactSpace (m + r + 1)
    letI := GeneralLinear.Mirabolic.locallyCompactSpace (n := m + r) (F := F.Carrier)
    ∀ [MeasurableSpace (rightPsiRetraction (R := F.Carrier) hr hm).ker]
      [BorelSpace (rightPsiRetraction (R := F.Carrier) hr hm).ker]
      [LocallyCompactSpace (rightPsiRetraction (R := F.Carrier) hr hm).ker]
      [MeasurableSpace ((rightPsiInducing (R := F.Carrier) hr hm).comap
        (rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype)]
      [BorelSpace ((rightPsiInducing (R := F.Carrier) hr hm).comap
        (rightPsiRetraction (R := F.Carrier) hr hm).ker.subtype)],
      (splitKernelHaarRatio (rightPsiRetraction (R := F.Carrier) hr hm)
          ((levi (n := m + r) (F := F.Carrier)).subgroupComap (rightPsiStages hr hm))
          (rightPsiInducing (R := F.Carrier) hr hm) (rightPsiSection_mem hr hm)
          (isClosed_rightPsiInducing hr hm) l : ℝ≥0) =
        T.determinantNorm m (rightPsiSecondBlock hr hm l.val (rightPsiLevi_mem hr hm l)) := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (m + r + 1)
  let := T.generalLinearLocallyCompactSpace (m + r + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := m + r) (F := F.Carrier)
  intro _ _ _ _ _
  let P := rightPsiStages (R := F.Carrier) hr hm
  let hker := ker_projection_le_rightPsiStages (R := F.Carrier) hr hm
  let rP := rightPsiRetraction (R := F.Carrier) hr hm
  let sP := (levi (n := m + r) (F := F.Carrier)).subgroupComap P
  let HP := rightPsiInducing (R := F.Carrier) hr hm
  let I := HP.comap rP.ker.subtype
  let : LocallyCompactSpace I :=
    (isClosed_splitKernelIntersection rP HP (isClosed_rightPsiInducing hr hm)).locallyCompactSpace
  have hl := rightPsiLevi_mem hr hm l
  set A := rightPsiFirstBlock hr hm l.val hl with hA
  set D := rightPsiSecondBlock hr hm l.val hl with hD
  -- The kernel: `ker rP ≃ ker projection`.
  have hNr : (projection (n := m + r) (F := F.Carrier)).ker = radical (m + r) F.Carrier :=
    ker_projection
  have hNc : IsClosed ((projection (n := m + r) (F := F.Carrier)).ker :
      Set (mirabolic (m + r) F.Carrier)) := by
    rw [hNr]
    exact radical_isClosed
  let : LocallyCompactSpace (projection (n := m + r) (F := F.Carrier)).ker :=
    hNc.locallyCompactSpace
  let : MeasurableSpace (projection (n := m + r) (F := F.Carrier)).ker := borel _
  have : BorelSpace (projection (n := m + r) (F := F.Carrier)).ker := ⟨rfl⟩
  have hN : mulEquivHaarChar (splitKernelConjugation rP sP l) =
      (T.determinantNorm (m + r) l.val : ℝ≥0)⁻¹ := by
    refine (Langlands.Geometric.haarChar_eq_of_conjugacy
      (splitStagesKernelContinuousEquiv projection levi projection_levi P hker)
      (splitKernelConjugation rP sP l)
      (splitKernelConjugation projection levi l.val) (fun g => Subtype.ext ?_)).trans
      (mulEquivHaarChar_splitKernelConjugation_levi T (m + r) l.val)
    change (((splitKernelConjugation rP sP l g : rP.ker) : P) : mirabolic (m + r) F.Carrier) =
      (splitKernelConjugation projection levi l.val
        (splitStagesKernelContinuousEquiv projection levi projection_levi P hker g) :
          mirabolic (m + r) F.Carrier)
    rw [splitKernelConjugation_apply, splitKernelConjugation_apply]
    rfl
  -- The intersection: `I ≃ N ≃ V_(r+1)`.
  let := T.generalLinearTopologicalGroup (r + 1)
  let := T.generalLinearLocallyCompactSpace (r + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := r) (F := F.Carrier)
  let : LocallyCompactSpace (radical r F.Carrier) := radical_isClosed.locallyCompactSpace
  let : MeasurableSpace (radical r F.Carrier) := borel _
  have : BorelSpace (radical r F.Carrier) := ⟨rfl⟩
  have hAn : (levi A)⁻¹ ∈ Subgroup.normalizer
      (radical r F.Carrier : Set (mirabolic r F.Carrier)) := by
    rw [← ker_projection]
    simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]
  have hlH : levi l.val ∈ rightSubgroup m r F.Carrier := levi_mem_rightSubgroup hr hm hl
  have hI : mulEquivHaarChar (subgroupAutomorphism I (splitKernelConjugation rP sP l)
      (splitKernelConjugation_mem rP sP HP (rightPsiSection_mem hr hm) l)) =
      (T.determinantNorm r A : ℝ≥0)⁻¹ := by
    refine (Langlands.Geometric.haarChar_eq_of_conjugacy
      ((splitStagesCoefficientIntersectionContinuousEquiv projection levi projection_levi P
        (rightSubgroup m r F.Carrier) hker (rightSubgroup_le_rightPsiStages hr hm)).trans
        rightPsiKernelContinuousEquiv)
      (subgroupAutomorphism I (splitKernelConjugation rP sP l)
        (splitKernelConjugation_mem rP sP HP (rightPsiSection_mem hr hm) l))
      (HaarModulus.normalizerConj (radical r F.Carrier) ⟨(levi A)⁻¹, hAn⟩)
      (fun i => Subtype.ext ?_)).trans (mulEquivHaarChar_conj_levi_inv T r A hAn)
    have hi : (i.val.val.val : mirabolic (m + r) F.Carrier) ∈ rightSubgroup m r F.Carrier :=
      i.property
    have key : (⟨(levi l.val)⁻¹ * i.val.val.val * levi l.val,
        (rightSubgroup m r F.Carrier).mul_mem
          ((rightSubgroup m r F.Carrier).mul_mem
            ((rightSubgroup m r F.Carrier).inv_mem hlH) hi) hlH⟩ :
          rightSubgroup m r F.Carrier) =
        (⟨levi l.val, hlH⟩ : rightSubgroup m r F.Carrier)⁻¹ * ⟨i.val.val.val, hi⟩ *
          ⟨levi l.val, hlH⟩ := rfl
    change (rightProjection (⟨(levi l.val)⁻¹ * i.val.val.val * levi l.val, _⟩ :
        rightSubgroup m r F.Carrier)).1 =
      (levi A)⁻¹ * (rightProjection (⟨i.val.val.val, hi⟩ : rightSubgroup m r F.Carrier)).1 *
        ((levi A)⁻¹)⁻¹
    rw [key, map_mul, map_mul, map_inv, rightProjection_levi hr hm l.val hl, inv_inv]
    rfl
  -- The ratio.
  simp only [splitKernelHaarRatio_apply]
  rw [hI, hN, determinantNorm_rightPsi T hr hm l.val hl, Units.val_mul, inv_div_inv]
  exact mul_div_cancel_left₀ _ (Units.ne_zero _)

end Haar

end Langlands.Derivative.MirabolicProductMinus
