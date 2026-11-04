import Langlands.Representation.Aubert.General.JacquetCutDiagram
import Langlands.Representation.Aubert.FilteredCutDiagram
import Langlands.Representation.Filtration.FiniteFilteredExactness

/-! The corrected support filtration on each actual homogeneous Jacquet degree. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General.JacquetComplex

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G))
  (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
  (hP : Monotone P) (hU : Antitone U)
variable (T : Subgroup G) [Fintype (Group.RelativeWeyl.Weyl T)]
  [DecidableEq (Group.RelativeWeyl.Weyl T)]
variable {Mx : CoxeterMatrix ι} (cs : CoxeterSystem Mx (Group.RelativeWeyl.Weyl T))
variable (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι)

/-- The actual support steps form subdiagrams of the actual Jacquet diagram. -/
def stepSubdiagram (i : ℕ) :
    (jacquetDiagram P M U h hclosed hδ hP hU A I).Subdiagram where
  obj s := (CorrectedFiltration.step P M U h hclosed T cs A I s i).toSubmodule
  map_mem hst _ hx := CorrectedFiltration.transition_mem_step A I hst i hx

/-- The homogeneous support filtration, indexed by the length-ordered prefix. -/
def degreeFiltration (k : ℕ) :
    ℕ → Submodule ℂ ((jacquetDiagram P M U h hclosed hδ hP hU A I).Degree k) :=
  fun i => (stepSubdiagram P M U h hclosed hδ hP hU T cs A I i).degreeSubmodule k

theorem degreeFiltration_monotone (k : ℕ) :
    Monotone (degreeFiltration P M U h hclosed hδ hP hU T cs A I k) := by
  intro i j hij x hx s
  exact CorrectedFiltration.step_monotone A I s.1 hij (hx s)

@[simp] theorem degreeFiltration_zero (k : ℕ) :
    degreeFiltration P M U h hclosed hδ hP hU T cs A I k 0 = ⊥ := by
  apply le_antisymm
  · intro x hx
    change x = 0
    funext s
    have hs := hx s
    change x s ∈ (CorrectedFiltration.step P M U h hclosed T cs A I s.1 0).toSubmodule at hs
    rw [CorrectedFiltration.step_zero] at hs
    exact hs
  · exact bot_le

theorem degreeFiltration_length
    (hcover : CorrectedFiltration.IsBruhatCover T (P ∅) (P I)) (k : ℕ) :
    degreeFiltration P M U h hclosed hδ hP hU T cs A I k
      (Support.rankOrderedList cs.length).length = ⊤ := by
  apply le_antisymm le_top
  intro x _ s
  change x s ∈ (CorrectedFiltration.step P M U h hclosed T cs A I s.1
    (Support.rankOrderedList cs.length).length).toSubmodule
  rw [CorrectedFiltration.step_length hcover]
  trivial

/-- The literal signed differential preserves every support step. -/
theorem degreeDifferential_preserves_degreeFiltration (k : ℕ) :
    FiniteFiltered.Preserves
      ((jacquetDiagram P M U h hclosed hδ hP hU A I).degreeDifferential k)
      (degreeFiltration P M U h hclosed hδ hP hU T cs A I k)
      (degreeFiltration P M U h hclosed hδ hP hU T cs A I (k + 1)) :=
  fun i x hx =>
    (stepSubdiagram P M U h hclosed hδ hP hU T cs A I i).degreeDifferential_mem k x hx

/-- The diagram of actual adjacent coordinate support quotients. -/
abbrev gradedDiagram (i : ℕ) : CutComplex.Diagram ι :=
  (stepSubdiagram P M U h hclosed hδ hP hU T cs A I i).quotientDiagram
    (stepSubdiagram P M U h hclosed hδ hP hU T cs A I (i + 1))

/-- The grade of a homogeneous support is the homogeneous product of the grades. -/
def gradedEquiv (i k : ℕ) :
    FiniteFiltered.Graded
        (degreeFiltration P M U h hclosed hδ hP hU T cs A I k) i ≃ₗ[ℂ]
      (gradedDiagram P M U h hclosed hδ hP hU T cs A I i).Degree k :=
  (stepSubdiagram P M U h hclosed hδ hP hU T cs A I i).degreeQuotientEquiv
    (stepSubdiagram P M U h hclosed hδ hP hU T cs A I (i + 1)) k

/-- The actual associated graded map, with its unchanged exterior signs. -/
abbrev gradedDifferential (i k : ℕ) :=
  FiniteFiltered.gradedMap
    ((jacquetDiagram P M U h hclosed hδ hP hU A I).degreeDifferential k)
    (degreeFiltration P M U h hclosed hδ hP hU T cs A I k)
    (degreeFiltration P M U h hclosed hδ hP hU T cs A I (k + 1))
    (degreeDifferential_preserves_degreeFiltration P M U h hclosed hδ hP hU T cs A I k) i

/-- The comparison intertwines the actual quotient differential and its signs. -/
theorem gradedEquiv_differential (i k : ℕ)
    (x : FiniteFiltered.Graded
      (degreeFiltration P M U h hclosed hδ hP hU T cs A I k) i) :
    gradedEquiv P M U h hclosed hδ hP hU T cs A I i (k + 1)
        (gradedDifferential P M U h hclosed hδ hP hU T cs A I i k x) =
      (gradedDiagram P M U h hclosed hδ hP hU T cs A I i).degreeDifferential k
        (gradedEquiv P M U h hclosed hδ hP hU T cs A I i k x) :=
  (stepSubdiagram P M U h hclosed hδ hP hU T cs A I i).degreeQuotientEquiv_differential
    (stepSubdiagram P M U h hclosed hδ hP hU T cs A I (i + 1)) k x

theorem gradedDifferential_injective_iff (i k : ℕ) :
    Function.Injective (gradedDifferential P M U h hclosed hδ hP hU T cs A I i k) ↔
      Function.Injective
        ((gradedDiagram P M U h hclosed hδ hP hU T cs A I i).degreeDifferential k) := by
  constructor
  · intro hf x y hxy
    apply (gradedEquiv P M U h hclosed hδ hP hU T cs A I i k).symm.injective
    apply hf
    apply (gradedEquiv P M U h hclosed hδ hP hU T cs A I i (k + 1)).injective
    simpa only [gradedEquiv_differential, LinearEquiv.apply_symm_apply] using hxy
  · intro hg x y hxy
    apply (gradedEquiv P M U h hclosed hδ hP hU T cs A I i k).injective
    apply hg
    rw [← gradedEquiv_differential, ← gradedEquiv_differential, hxy]

theorem gradedDifferential_exact_iff (i k : ℕ) :
    LinearMap.range (gradedDifferential P M U h hclosed hδ hP hU T cs A I i k) =
        LinearMap.ker (gradedDifferential P M U h hclosed hδ hP hU T cs A I i (k + 1)) ↔
      LinearMap.range
          ((gradedDiagram P M U h hclosed hδ hP hU T cs A I i).degreeDifferential k) =
        LinearMap.ker
          ((gradedDiagram P M U h hclosed hδ hP hU T cs A I i).degreeDifferential (k + 1)) := by
  constructor
  · intro hex
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (gradedDiagram P M U h hclosed hδ hP hU T cs A I i).degreeDifferential_square k x
    · intro y hy
      let x := (gradedEquiv P M U h hclosed hδ hP hU T cs A I i (k + 1)).symm y
      have hx : x ∈ LinearMap.ker
          (gradedDifferential P M U h hclosed hδ hP hU T cs A I i (k + 1)) := by
        apply (gradedEquiv P M U h hclosed hδ hP hU T cs A I i (k + 1 + 1)).injective
        rw [gradedEquiv_differential, map_zero, LinearEquiv.apply_symm_apply]
        exact hy
      obtain ⟨z, hz⟩ := hex ▸ hx
      refine ⟨gradedEquiv P M U h hclosed hδ hP hU T cs A I i k z, ?_⟩
      rw [← gradedEquiv_differential, hz]
      exact LinearEquiv.apply_symm_apply _ y
  · intro hex
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      apply (gradedEquiv P M U h hclosed hδ hP hU T cs A I i (k + 1 + 1)).injective
      rw [gradedEquiv_differential, gradedEquiv_differential, map_zero]
      exact (gradedDiagram P M U h hclosed hδ hP hU T cs A I i).degreeDifferential_square k _
    · intro x hx
      have hy : gradedEquiv P M U h hclosed hδ hP hU T cs A I i (k + 1) x ∈
          LinearMap.ker
            ((gradedDiagram P M U h hclosed hδ hP hU T cs A I i).degreeDifferential (k + 1)) := by
        rw [LinearMap.mem_ker, ← gradedEquiv_differential, hx, map_zero]
      obtain ⟨z, hz⟩ := hex ▸ hy
      refine ⟨(gradedEquiv P M U h hclosed hδ hP hU T cs A I i k).symm z, ?_⟩
      apply (gradedEquiv P M U h hclosed hδ hP hU T cs A I i (k + 1)).injective
      rw [gradedEquiv_differential, LinearEquiv.apply_symm_apply]
      exact hz

/-- Injectivity in every coordinate grade lifts through the full support filtration. -/
theorem degreeDifferential_injective_of_graded
    (hcover : CorrectedFiltration.IsBruhatCover T (P ∅) (P I)) (k : ℕ)
    (hinj : ∀ i < (Support.rankOrderedList cs.length).length, Function.Injective
      ((gradedDiagram P M U h hclosed hδ hP hU T cs A I i).degreeDifferential k)) :
    Function.Injective ((jacquetDiagram P M U h hclosed hδ hP hU A I).degreeDifferential k) :=
  FiniteFiltered.injective_of_graded_injective _
    (degreeFiltration P M U h hclosed hδ hP hU T cs A I k)
    (degreeFiltration P M U h hclosed hδ hP hU T cs A I (k + 1))
    (degreeDifferential_preserves_degreeFiltration P M U h hclosed hδ hP hU T cs A I k)
    (degreeFiltration_zero P M U h hclosed hδ hP hU T cs A I k)
    (Support.rankOrderedList cs.length).length
    (degreeFiltration_length P M U h hclosed hδ hP hU T cs A I hcover k)
    (fun i hi => (gradedDifferential_injective_iff P M U h hclosed hδ hP hU T cs A I i k).mpr
      (hinj i hi))

/-- Exactness in every coordinate grade lifts through the full support filtration. -/
theorem degreeDifferential_exact_of_graded
    (hcover : CorrectedFiltration.IsBruhatCover T (P ∅) (P I)) (k : ℕ)
    (hex : ∀ i < (Support.rankOrderedList cs.length).length,
      LinearMap.range
          ((gradedDiagram P M U h hclosed hδ hP hU T cs A I i).degreeDifferential k) =
        LinearMap.ker
          ((gradedDiagram P M U h hclosed hδ hP hU T cs A I i).degreeDifferential (k + 1))) :
    LinearMap.range ((jacquetDiagram P M U h hclosed hδ hP hU A I).degreeDifferential k) =
      LinearMap.ker ((jacquetDiagram P M U h hclosed hδ hP hU A I).degreeDifferential (k + 1)) :=
  FiniteFiltered.range_eq_ker_of_graded_exact _ _
    (degreeFiltration P M U h hclosed hδ hP hU T cs A I k)
    (degreeFiltration P M U h hclosed hδ hP hU T cs A I (k + 1))
    (degreeFiltration P M U h hclosed hδ hP hU T cs A I (k + 1 + 1))
    (degreeDifferential_preserves_degreeFiltration P M U h hclosed hδ hP hU T cs A I k)
    (degreeDifferential_preserves_degreeFiltration P M U h hclosed hδ hP hU T cs A I (k + 1))
    (degreeFiltration_monotone P M U h hclosed hδ hP hU T cs A I k)
    (degreeFiltration_zero P M U h hclosed hδ hP hU T cs A I (k + 1))
    ((jacquetDiagram P M U h hclosed hδ hP hU A I).degreeDifferential_square k)
    (Support.rankOrderedList cs.length).length
    (degreeFiltration_length P M U h hclosed hδ hP hU T cs A I hcover (k + 1))
    (fun i hi => (gradedDifferential_exact_iff P M U h hclosed hδ hP hU T cs A I i k).mpr
      (hex i hi))

end Langlands.Aubert.General.JacquetComplex
