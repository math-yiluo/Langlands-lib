import Langlands.Representation.Aubert.General.CorrectedDegreeFiltration
import Langlands.Representation.Aubert.General.CorrectedFiltrationNatural
import Langlands.Representation.Aubert.General.CorrectedGradedNatural
import Langlands.Representation.Aubert.General.AssociatedCokernelTransport
import Langlands.Representation.Aubert.General.RationalFixedLeviComparisonProof
import Langlands.Representation.Filtration.FiniteFilteredCokernel
import Langlands.Representation.Category.Abelian

/-! The surviving support step computes the actual retained Jacquet cokernel. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General.JacquetComplex

open CategoryTheory

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

/-- A step vanishes when its modified support is empty. -/
theorem step_eq_bot_of_modifiedSupport_eq_empty
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I s : Finset ι) (i : ℕ)
    (hθ : CorrectedFiltration.modifiedSupport cs (Finset.univ \ s) I i = ∅) :
    CorrectedFiltration.step P M U h hclosed T cs A I s i = ⊥ := by
  apply CorrectedFiltration.jacquetImage_eq_bot
  simp [CorrectedFiltration.inductionStep, CorrectedFiltration.groupSupport, hθ]

/-- The coordinate inclusion of one term into the actual homogeneous Jacquet
module, through the finite-product comparison. -/
def coordinateLinear (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι) (d : ℕ)
    (s : {s : Finset ι // s.card = d}) :
    (jacquetDiagram P M U h hclosed hδ hP hU A I).Obj s.1 →ₗ[ℂ]
      (jacquetFunctor (h I) (hclosed I)).obj
        (StandardComplex.degreeObject P M U h hclosed A d) :=
  (jacquetDegreeEquiv P M U h hclosed hδ hP hU A I d).symm.toLinearMap ∘ₗ
    LinearMap.single ℂ (fun s : {s : Finset ι // s.card = d} =>
      (jacquetDiagram P M U h hclosed hδ hP hU A I).Obj s.1) s

theorem jacquetDegreeEquiv_coordinateLinear (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I : Finset ι) (d : ℕ) (s : {s : Finset ι // s.card = d})
    (y : (jacquetDiagram P M U h hclosed hδ hP hU A I).Obj s.1) :
    jacquetDegreeEquiv P M U h hclosed hδ hP hU A I d
        (coordinateLinear P M U h hclosed hδ hP hU A I d s y) = Pi.single s y :=
  LinearEquiv.apply_symm_apply _ _

/-- The coordinate inclusion respects the actual normalized Levi actions. -/
theorem coordinateLinear_intertwining (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I : Finset ι) (d : ℕ) (s0 : {s : Finset ι // s.card = d}) (m : M I)
    (y : (jacquetDiagram P M U h hclosed hδ hP hU A I).Obj s0.1) :
    coordinateLinear P M U h hclosed hδ hP hU A I d s0
        (((jacquetFunctor (h I) (hclosed I)).obj
          (CorrectedFiltration.term P M U h hclosed A s0.1)).representation m y) =
      ((jacquetFunctor (h I) (hclosed I)).obj
          (StandardComplex.degreeObject P M U h hclosed A d)).representation m
        (coordinateLinear P M U h hclosed hδ hP hU A I d s0 y) := by
  apply (jacquetDegreeEquiv P M U h hclosed hδ hP hU A I d).injective
  rw [jacquetDegreeEquiv_intertwining, jacquetDegreeEquiv_coordinateLinear,
    jacquetDegreeEquiv_coordinateLinear]
  funext s
  change _ = ((jacquetFunctor (h I) (hclosed I)).obj
    (CorrectedFiltration.term P M U h hclosed A s.1)).representation m
      (Pi.single (M := fun s : {s : Finset ι // s.card = d} =>
        (jacquetDiagram P M U h hclosed hδ hP hU A I).Obj s.1) s0 y s)
  by_cases hs : s = s0
  · subst hs
    simp
  · simp only [Pi.single_eq_of_ne hs]
    exact (map_zero _).symm

/-- The finite-product comparison is natural in the ambient representation. -/
theorem jacquetDegreeEquiv_natural {A B : SmoothRep.{0, uG, max uG uV} ℂ G} (φ : A ⟶ B)
    (I : Finset ι) (k : ℕ)
    (x : (jacquetFunctor (h I) (hclosed I)).obj
      (StandardComplex.degreeObject P M U h hclosed A k))
    (s : {s : Finset ι // s.card = k}) :
    jacquetDegreeEquiv P M U h hclosed hδ hP hU B I k
        (SmoothRep.hom ((jacquetFunctor (h I) (hclosed I)).map
          ((StandardComplex.degreeFunctor P M U h hclosed hδ hP hU k).map φ)) x) s =
      SmoothRep.hom ((jacquetFunctor (h I) (hclosed I)).map
          (CorrectedFiltration.termMap P M U h hclosed φ s.1))
        (jacquetDegreeEquiv P M U h hclosed hδ hP hU A I k x s) := by
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective
    (StandardComplex.degreeObject P M U h hclosed A k).representation (U I) 1 x
  change jacquetDegreeEquiv P M U h hclosed hδ hP hU B I k
    (Jacquet.Localization.mk (StandardComplex.degreeObject P M U h hclosed B k).representation
      (U I) 1 (SmoothRep.hom ((StandardComplex.degreeFunctor P M U h hclosed hδ hP hU k).map φ)
        v)) s = _
  rw [jacquetDegreeEquiv_mk, jacquetDegreeEquiv_mk]
  rfl

/-- The coordinate inclusion is natural in the ambient representation. -/
theorem coordinateLinear_natural {A B : SmoothRep.{0, uG, max uG uV} ℂ G} (φ : A ⟶ B)
    (I : Finset ι) (d : ℕ) (s0 : {s : Finset ι // s.card = d})
    (y : (jacquetDiagram P M U h hclosed hδ hP hU A I).Obj s0.1) :
    SmoothRep.hom ((jacquetFunctor (h I) (hclosed I)).map
        ((StandardComplex.degreeFunctor P M U h hclosed hδ hP hU d).map φ))
        (coordinateLinear P M U h hclosed hδ hP hU A I d s0 y) =
      coordinateLinear P M U h hclosed hδ hP hU B I d s0
        (SmoothRep.hom ((jacquetFunctor (h I) (hclosed I)).map
          (CorrectedFiltration.termMap P M U h hclosed φ s0.1)) y) := by
  apply (jacquetDegreeEquiv P M U h hclosed hδ hP hU B I d).injective
  rw [jacquetDegreeEquiv_coordinateLinear]
  funext s
  rw [jacquetDegreeEquiv_natural, jacquetDegreeEquiv_coordinateLinear]
  by_cases hs : s = s0
  · subst hs
    simp
  · simp only [Pi.single_eq_of_ne hs]
    exact map_zero _

/-- A homogeneous family in the surviving step, with every other coordinate step
zero, is concentrated in the coordinate `s0`. -/
theorem single_eq_of_mem_degreeFiltration (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I : Finset ι) (d : ℕ) (s0 : {s : Finset ι // s.card = d}) (i : ℕ)
    (hconc : ∀ s : {s : Finset ι // s.card = d}, s ≠ s0 →
      CorrectedFiltration.modifiedSupport cs (Finset.univ \ s.1) I i = ∅)
    (x : (jacquetDiagram P M U h hclosed hδ hP hU A I).Degree d)
    (hx : x ∈ degreeFiltration P M U h hclosed hδ hP hU T cs A I d i) :
    Pi.single s0 (x s0) = x := by
  funext s
  by_cases hs : s = s0
  · subst hs
    simp
  · rw [Pi.single_eq_of_ne hs]
    have hxs := hx s
    change x s ∈ (CorrectedFiltration.step P M U h hclosed T cs A I s.1 i).toSubmodule at hxs
    rw [step_eq_bot_of_modifiedSupport_eq_empty P M U h hclosed T cs A I s.1 i (hconc s hs)] at hxs
    exact hxs.symm


/-- A homogeneous support step vanishes when every coordinate modified support is empty. -/
theorem degreeFiltration_eq_bot (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι)
    (k i : ℕ)
    (hθ : ∀ s : {s : Finset ι // s.card = k},
      CorrectedFiltration.modifiedSupport cs (Finset.univ \ s.1) I i = ∅) :
    degreeFiltration P M U h hclosed hδ hP hU T cs A I k i = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  funext s
  have hxs := hx s
  change x s ∈ (CorrectedFiltration.step P M U h hclosed T cs A I s.1 i).toSubmodule at hxs
  rw [step_eq_bot_of_modifiedSupport_eq_empty P M U h hclosed T cs A I s.1 i (hθ s)] at hxs
  exact hxs

/-- A single coordinate in the surviving step lies in the homogeneous step. -/
theorem single_mem_degreeFiltration (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I : Finset ι) (d : ℕ) (s0 : {s : Finset ι // s.card = d}) (i : ℕ)
    (y : (jacquetDiagram P M U h hclosed hδ hP hU A I).Obj s0.1)
    (hy : y ∈ (CorrectedFiltration.step P M U h hclosed T cs A I s0.1 i).toSubmodule) :
    (Pi.single s0 y : (jacquetDiagram P M U h hclosed hδ hP hU A I).Degree d) ∈
      degreeFiltration P M U h hclosed hδ hP hU T cs A I d i := by
  intro s
  by_cases hs : s = s0
  · subst hs
    change Pi.single (M := fun s : {s : Finset ι // s.card = d} =>
      (jacquetDiagram P M U h hclosed hδ hP hU A I).Obj s.1) s y s ∈
        (CorrectedFiltration.step P M U h hclosed T cs A I s.1 i).toSubmodule
    rw [Pi.single_eq_same]
    exact hy
  · change Pi.single (M := fun s : {s : Finset ι // s.card = d} =>
      (jacquetDiagram P M U h hclosed hδ hP hU A I).Obj s.1) s0 y s ∈
        (CorrectedFiltration.step P M U h hclosed T cs A I s.1 i).toSubmodule
    rw [Pi.single_eq_of_ne hs]
    exact Submodule.zero_mem _

/-- The actual incoming differential after the normalized Jacquet functor. -/
def incomingJacquet (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι) (d : ℕ) :
    (jacquetFunctor (h I) (hclosed I)).obj
        (StandardComplex.degreeObject P M U h hclosed A (d - 1)) →ₗ[ℂ]
      (jacquetFunctor (h I) (hclosed I)).obj
        (StandardComplex.degreeObject P M U h hclosed A d) :=
  (SmoothRep.hom ((jacquetFunctor (h I) (hclosed I)).map
    ((StandardComplex.incomingDifferentialNat P M U h hclosed hδ hP hU d).app A))).toLinearMap

theorem incomingJacquet_apply (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι) (d : ℕ)
    (z : (jacquetFunctor (h I) (hclosed I)).obj
      (StandardComplex.degreeObject P M U h hclosed A (d - 1))) :
    incomingJacquet P M U h hclosed hδ hP hU A I d z =
      SmoothRep.hom ((jacquetFunctor (h I) (hclosed I)).map
        ((StandardComplex.incomingDifferentialNat P M U h hclosed hδ hP hU d).app A)) z :=
  rfl

theorem incomingJacquet_zero_apply (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι)
    (z : (jacquetFunctor (h I) (hclosed I)).obj
      (StandardComplex.degreeObject P M U h hclosed A (0 - 1))) :
    incomingJacquet P M U h hclosed hδ hP hU A I 0 z = 0 := by
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective
    (StandardComplex.degreeObject P M U h hclosed A (0 - 1)).representation (U I) 1 z
  exact map_zero (Jacquet.Localization.mk
    (StandardComplex.degreeObject P M U h hclosed A 0).representation (U I) 1)

theorem jacquetDegreeEquiv_incoming (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι)
    (k : ℕ)
    (z : (jacquetFunctor (h I) (hclosed I)).obj
      (StandardComplex.degreeObject P M U h hclosed A k)) :
    jacquetDegreeEquiv P M U h hclosed hδ hP hU A I (k + 1)
        (incomingJacquet P M U h hclosed hδ hP hU A I (k + 1) z) =
      (jacquetDiagram P M U h hclosed hδ hP hU A I).degreeDifferential k
        (jacquetDegreeEquiv P M U h hclosed hδ hP hU A I k z) :=
  jacquetDegreeEquiv_differential P M U h hclosed hδ hP hU A I k z

/-- The surviving step of `s0`, followed by the coordinate inclusion and the actual
cokernel projection of the incoming Jacquet differential. -/
def cokernelCoordinate (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι) (d : ℕ)
    (s0 : {s : Finset ι // s.card = d}) (i : ℕ) :
    (CorrectedFiltration.step P M U h hclosed T cs A I s0.1 i).toSubmodule →ₗ[ℂ]
      _ ⧸ LinearMap.range (incomingJacquet P M U h hclosed hδ hP hU A I d) :=
  (LinearMap.range (incomingJacquet P M U h hclosed hδ hP hU A I d)).mkQ ∘ₗ
    coordinateLinear P M U h hclosed hδ hP hU A I d s0 ∘ₗ
      (CorrectedFiltration.step P M U h hclosed T cs A I s0.1 i).toSubmodule.subtype

/-- Graded exactness above `i0` and vanishing of the previous degree at `i0 + 1`
make the surviving coordinate step inject into the actual cokernel. -/
theorem cokernelCoordinate_injective (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I : Finset ι) (d : ℕ) (s0 : {s : Finset ι // s.card = d}) (i0 : ℕ)
    (hcover : CorrectedFiltration.IsBruhatCover T (P ∅) (P I))
    (hlow : ∀ s : Finset ι, s.card + 1 = d →
      CorrectedFiltration.modifiedSupport cs (Finset.univ \ s) I (i0 + 1) = ∅)
    (hinj : d = 1 → ∀ i, i0 < i → i < (Support.rankOrderedList cs.length).length →
      Function.Injective (gradedDifferential P M U h hclosed hδ hP hU T cs A I i 0))
    (hex : ∀ k, k + 2 = d → ∀ i, i0 < i → i < (Support.rankOrderedList cs.length).length →
      LinearMap.range (gradedDifferential P M U h hclosed hδ hP hU T cs A I i k) =
        LinearMap.ker (gradedDifferential P M U h hclosed hδ hP hU T cs A I i (k + 1))) :
    Function.Injective
      (cokernelCoordinate P M U h hclosed hδ hP hU T cs A I d s0 (i0 + 1)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hy
  suffices hy0 : (Pi.single s0 y.1 : (jacquetDiagram P M U h hclosed hδ hP hU A I).Degree d) =
      0 by
    have := congrFun hy0 s0
    rw [Pi.single_eq_same] at this
    exact Subtype.ext this
  have he := congrArg (jacquetDegreeEquiv P M U h hclosed hδ hP hU A I d) hz
  change jacquetDegreeEquiv P M U h hclosed hδ hP hU A I d
      (incomingJacquet P M U h hclosed hδ hP hU A I d z) =
    jacquetDegreeEquiv P M U h hclosed hδ hP hU A I d
      (coordinateLinear P M U h hclosed hδ hP hU A I d s0 y.1) at he
  rw [jacquetDegreeEquiv_coordinateLinear] at he
  rw [← he]
  cases d with
  | zero =>
    rw [incomingJacquet_zero_apply, map_zero]
  | succ k =>
    rw [jacquetDegreeEquiv_incoming]
    rw [jacquetDegreeEquiv_incoming] at he
    have hgb := he ▸ single_mem_degreeFiltration P M U h hclosed hδ hP hU T cs A I (k + 1) s0
      (i0 + 1) y.1 y.2
    have hTbot : degreeFiltration P M U h hclosed hδ hP hU T cs A I k (i0 + 1) = ⊥ :=
      degreeFiltration_eq_bot P M U h hclosed hδ hP hU T cs A I k (i0 + 1)
        (fun s => hlow s.1 (by rw [s.2]))
    have hbtop : jacquetDegreeEquiv P M U h hclosed hδ hP hU A I k z ∈
        degreeFiltration P M U h hclosed hδ hP hU T cs A I k
          (Support.rankOrderedList cs.length).length := by
      rw [degreeFiltration_length P M U h hclosed hδ hP hU T cs A I hcover]
      trivial
    cases k with
    | zero =>
      have hf : FiniteFiltered.Preserves (0 : (jacquetDiagram P M U h hclosed hδ hP hU A I).Degree 0
          →ₗ[ℂ] (jacquetDiagram P M U h hclosed hδ hP hU A I).Degree 0)
          (degreeFiltration P M U h hclosed hδ hP hU T cs A I 0)
          (degreeFiltration P M U h hclosed hδ hP hU T cs A I 0) :=
        fun _ _ _ => Submodule.zero_mem _
      refine FiniteFiltered.map_eq_zero_of_graded_exact _ _ _ _ _ hf
        (degreeDifferential_preserves_degreeFiltration P M U h hclosed hδ hP hU T cs A I 0)
        (degreeFiltration_monotone P M U h hclosed hδ hP hU T cs A I 0)
        (degreeFiltration_monotone P M U h hclosed hδ hP hU T cs A I 1)
        (fun _ => by rw [LinearMap.zero_apply, map_zero]) i0
        (Support.rankOrderedList cs.length).length hTbot ?_ _ le_rfl _ hbtop hgb
      intro i hi0 hiN
      rw [LinearMap.ker_eq_bot.mpr (hinj rfl i hi0 hiN), LinearMap.range_eq_bot]
      apply LinearMap.ext
      intro q
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ q
      rw [FiniteFiltered.gradedMap_mk]
      have ha : FiniteFiltered.stepMap 0 _ _ hf i a = 0 := Subtype.ext rfl
      rw [ha, map_zero, LinearMap.zero_apply]
    | succ k =>
      exact FiniteFiltered.map_eq_zero_of_graded_exact _ _ _ _ _
        (degreeDifferential_preserves_degreeFiltration P M U h hclosed hδ hP hU T cs A I k)
        (degreeDifferential_preserves_degreeFiltration P M U h hclosed hδ hP hU T cs A I (k + 1))
        (degreeFiltration_monotone P M U h hclosed hδ hP hU T cs A I (k + 1))
        (degreeFiltration_monotone P M U h hclosed hδ hP hU T cs A I (k + 2))
        ((jacquetDiagram P M U h hclosed hδ hP hU A I).degreeDifferential_square k) i0
        (Support.rankOrderedList cs.length).length hTbot (hex k rfl) _ le_rfl _ hbtop hgb

/-- Graded surjectivity above `i0`, and concentration of the step `i0 + 1` in
`s0`, make the surviving coordinate step surject onto the actual cokernel. -/
theorem cokernelCoordinate_surjective (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I : Finset ι) (d : ℕ) (s0 : {s : Finset ι // s.card = d}) (i0 : ℕ)
    (hcover : CorrectedFiltration.IsBruhatCover T (P ∅) (P I))
    (hconc : ∀ s : {s : Finset ι // s.card = d}, s ≠ s0 →
      CorrectedFiltration.modifiedSupport cs (Finset.univ \ s.1) I (i0 + 1) = ∅)
    (htop : d = 0 → (Support.rankOrderedList cs.length).length ≤ i0 + 1)
    (hsurj : ∀ k, k + 1 = d → ∀ i, i0 < i → i < (Support.rankOrderedList cs.length).length →
      Function.Surjective (gradedDifferential P M U h hclosed hδ hP hU T cs A I i k)) :
    Function.Surjective
      (cokernelCoordinate P M U h hclosed hδ hP hU T cs A I d s0 (i0 + 1)) := by
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  have htopd : jacquetDegreeEquiv P M U h hclosed hδ hP hU A I d x ∈
      degreeFiltration P M U h hclosed hδ hP hU T cs A I d
        (Support.rankOrderedList cs.length).length := by
    rw [degreeFiltration_length P M U h hclosed hδ hP hU T cs A I hcover]
    trivial
  obtain ⟨w, hw⟩ : ∃ w, jacquetDegreeEquiv P M U h hclosed hδ hP hU A I d x -
      jacquetDegreeEquiv P M U h hclosed hδ hP hU A I d
        (incomingJacquet P M U h hclosed hδ hP hU A I d w) ∈
      degreeFiltration P M U h hclosed hδ hP hU T cs A I d (i0 + 1) := by
    cases d with
    | zero =>
      refine ⟨0, ?_⟩
      rw [map_zero, map_zero, sub_zero]
      exact degreeFiltration_monotone P M U h hclosed hδ hP hU T cs A I 0 (htop rfl) htopd
    | succ k =>
      obtain ⟨b, hb⟩ := FiniteFiltered.exists_sub_mem_of_graded_surjective _ _ _
        (degreeDifferential_preserves_degreeFiltration P M U h hclosed hδ hP hU T cs A I k)
        (degreeFiltration_monotone P M U h hclosed hδ hP hU T cs A I (k + 1)) i0
        (Support.rankOrderedList cs.length).length (hsurj k rfl) _ le_rfl _ htopd
      refine ⟨(jacquetDegreeEquiv P M U h hclosed hδ hP hU A I k).symm b, ?_⟩
      rw [jacquetDegreeEquiv_incoming, LinearEquiv.apply_symm_apply]
      exact hb
  refine ⟨⟨_, hw s0⟩, ?_⟩
  have hcl : coordinateLinear P M U h hclosed hδ hP hU A I d s0
      ((jacquetDegreeEquiv P M U h hclosed hδ hP hU A I d x -
        jacquetDegreeEquiv P M U h hclosed hδ hP hU A I d
          (incomingJacquet P M U h hclosed hδ hP hU A I d w)) s0) =
      x - incomingJacquet P M U h hclosed hδ hP hU A I d w := by
    apply (jacquetDegreeEquiv P M U h hclosed hδ hP hU A I d).injective
    rw [jacquetDegreeEquiv_coordinateLinear,
      single_eq_of_mem_degreeFiltration P M U h hclosed hδ hP hU T cs A I d s0 (i0 + 1)
        hconc _ hw, map_sub]
  have hq : Submodule.mkQ (LinearMap.range (incomingJacquet P M U h hclosed hδ hP hU A I d))
      (x - incomingJacquet P M U h hclosed hδ hP hU A I d w) =
        Submodule.mkQ (LinearMap.range (incomingJacquet P M U h hclosed hδ hP hU A I d)) x := by
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, sub_sub_cancel_left]
    exact neg_mem (LinearMap.mem_range_self _ w)
  rw [← hcl] at hq
  exact hq

section Categorical

/-- A bijective smooth intertwiner is an isomorphism. -/
theorem isIso_of_bijective {X : Type uG} [Group X] [TopologicalSpace X]
    {A B : SmoothRep.{0, uG, uV} ℂ X} (f : A ⟶ B)
    (hf : Function.Bijective (SmoothRep.hom f)) : IsIso f := by
  have : Mono f := (SmoothRep.mono_iff_injective f).mpr hf.1
  have : Epi f := (SmoothRep.epi_iff_surjective f).mpr hf.2
  exact isIso_of_mono_of_epi f

/-- The filtration step `i` of `r_I(E_{S \ s})`, as a functor of the ambient
representation `E`, with the actual step maps. -/
def stepFunctor (I s : Finset ι) (i : ℕ) :
    SmoothRep.{0, uG, max uI uG uV} ℂ G ⥤ SmoothRep.{0, uG, max uI uG uV} ℂ (M I) where
  obj A := SmoothRep.subrepresentation
    ((jacquetFunctor.{uG, max uI uG uV} (h I) (hclosed I)).obj
      (CorrectedFiltration.term.{uI, uG, max uI uV} P M U h hclosed A s))
    (CorrectedFiltration.step.{uI, uG, max uI uV} P M U h hclosed T cs A I s i)
  map φ := CorrectedFiltration.stepMap.{uI, uG, max uI uV} T cs φ I s i
  map_id A := by
    apply ObjectProperty.hom_ext
    ext x
    apply Subtype.ext
    change SmoothRep.hom ((jacquetFunctor.{uG, max uI uG uV} (h I) (hclosed I)).map
      (CorrectedFiltration.termMap.{uI, uG, max uI uV} P M U h hclosed (𝟙 A) s)) x.1 = x.1
    rw [CorrectedFiltration.termMap_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp φ ψ := by
    apply ObjectProperty.hom_ext
    ext x
    apply Subtype.ext
    change SmoothRep.hom ((jacquetFunctor.{uG, max uI uG uV} (h I) (hclosed I)).map
      (CorrectedFiltration.termMap.{uI, uG, max uI uV} P M U h hclosed (φ ≫ ψ) s)) x.1 =
        SmoothRep.hom ((jacquetFunctor.{uG, max uI uG uV} (h I) (hclosed I)).map
          (CorrectedFiltration.termMap.{uI, uG, max uI uV} P M U h hclosed ψ s))
          (SmoothRep.hom ((jacquetFunctor.{uG, max uI uG uV} (h I) (hclosed I)).map
            (CorrectedFiltration.termMap.{uI, uG, max uI uV} P M U h hclosed φ s)) x.1)
    rw [CorrectedFiltration.termMap_comp, CategoryTheory.Functor.map_comp]
    rfl

/-- The actual incoming differential of degree `d` after the normalized Jacquet
functor `r_I`. -/
abbrev incomingJacquetNat (I : Finset ι) (d : ℕ) :=
  Functor.whiskerRight
    (StandardComplex.incomingDifferentialNat.{uI, uG, max uI uV} P M U h hclosed hδ hP hU d)
    (jacquetFunctor.{uG, max uI uG uV} (h I) (hclosed I))

/-- The actual natural cokernel of the incoming differential of degree `d` after the
normalized Jacquet functor `r_I`. -/
abbrev jacquetCokernel (I : Finset ι) (d : ℕ) :=
  SmoothNatCokernel.functor (incomingJacquetNat.{uI, uG, uV} P M U h hclosed hδ hP hU I d)

/-- The coordinate inclusion of the step of `s0` into the actual homogeneous Jacquet
module of degree `d`. -/
def coordinateMorphism (I : Finset ι) (d : ℕ) (s0 : {s : Finset ι // s.card = d}) (i : ℕ)
    (A : SmoothRep.{0, uG, max uI uG uV} ℂ G) :
    (stepFunctor.{uI, uG, uV} P M U h hclosed T cs I s0.1 i).obj A ⟶
      (jacquetFunctor.{uG, max uI uG uV} (h I) (hclosed I)).obj
        (StandardComplex.degreeObject.{uI, uG, max uI uV} P M U h hclosed A d) :=
  SmoothRep.ofHom
    { toLinearMap :=
        coordinateLinear.{uI, uG, max uI uV} P M U h hclosed hδ hP hU A I d s0 ∘ₗ
          (CorrectedFiltration.step.{uI, uG, max uI uV} P M U h hclosed T cs A I
            s0.1 i).toSubmodule.subtype
      isIntertwining' := fun m => LinearMap.ext fun x =>
        coordinateLinear_intertwining.{uI, uG, max uI uV} P M U h hclosed hδ hP hU
          A I d s0 m x.1 }

theorem coordinateMorphism_apply (I : Finset ι) (d : ℕ) (s0 : {s : Finset ι // s.card = d})
    (i : ℕ) (A : SmoothRep.{0, uG, max uI uG uV} ℂ G)
    (x : (stepFunctor.{uI, uG, uV} P M U h hclosed T cs I s0.1 i).obj A) :
    SmoothRep.hom
        (coordinateMorphism.{uI, uG, uV} P M U h hclosed hδ hP hU T cs I d s0 i A) x =
      coordinateLinear.{uI, uG, max uI uV} P M U h hclosed hδ hP hU A I d s0 x.1 :=
  rfl

theorem coordinateMorphism_natural (I : Finset ι) (d : ℕ)
    (s0 : {s : Finset ι // s.card = d}) (i : ℕ)
    {A B : SmoothRep.{0, uG, max uI uG uV} ℂ G} (φ : A ⟶ B) :
    (stepFunctor.{uI, uG, uV} P M U h hclosed T cs I s0.1 i).map φ ≫
        coordinateMorphism.{uI, uG, uV} P M U h hclosed hδ hP hU T cs I d s0 i B =
      coordinateMorphism.{uI, uG, uV} P M U h hclosed hδ hP hU T cs I d s0 i A ≫
        (jacquetFunctor.{uG, max uI uG uV} (h I) (hclosed I)).map
          ((StandardComplex.degreeFunctor.{uI, uG, max uI uV} P M U h hclosed hδ hP hU d).map
            φ) := by
  apply ObjectProperty.hom_ext
  ext x
  exact (coordinateLinear_natural.{uI, uG, max uI uV} P M U h hclosed hδ hP hU φ I d s0
    x.1).symm

/-- The natural map from the step of the coordinate `s0` to the actual Jacquet
cokernel: coordinate inclusion followed by the cokernel projection. -/
def canonicalMap (I : Finset ι) (d : ℕ) (s0 : {s : Finset ι // s.card = d}) (i : ℕ) :
    stepFunctor.{uI, uG, uV} P M U h hclosed T cs I s0.1 i ⟶
      jacquetCokernel.{uI, uG, uV} P M U h hclosed hδ hP hU I d where
  app A := coordinateMorphism.{uI, uG, uV} P M U h hclosed hδ hP hU T cs I d s0 i A ≫
    (SmoothNatCokernel.projection
      (incomingJacquetNat.{uI, uG, uV} P M U h hclosed hδ hP hU I d)).app A
  naturality A B φ := by
    rw [← Category.assoc, coordinateMorphism_natural.{uI, uG, uV}]
    exact (Category.assoc _ _ _).trans (congrArg
      (coordinateMorphism.{uI, uG, uV} P M U h hclosed hδ hP hU T cs I d s0 i A ≫ ·)
      ((SmoothNatCokernel.projection
        (incomingJacquetNat.{uI, uG, uV} P M U h hclosed hδ hP hU I d)).naturality φ))

theorem canonicalMap_app_apply (I : Finset ι) (d : ℕ) (s0 : {s : Finset ι // s.card = d})
    (i : ℕ) (A : SmoothRep.{0, uG, max uI uG uV} ℂ G)
    (x : (stepFunctor.{uI, uG, uV} P M U h hclosed T cs I s0.1 i).obj A) :
    SmoothRep.hom ((canonicalMap.{uI, uG, uV} P M U h hclosed hδ hP hU T cs I d s0 i).app A) x =
      cokernelCoordinate.{uI, uG, max uI uV} P M U h hclosed hδ hP hU T cs A I d s0 i x :=
  rfl

/-- If the surviving coordinate step maps bijectively to the actual Jacquet cokernel
on every object of a diagram, and a natural map from that step to `Q` is bijective,
then the actual Jacquet cokernel on the diagram is naturally isomorphic to `Q`. -/
theorem jacquetCokernel_nonempty_iso {D : Type*} [Category D]
    (F : D ⥤ SmoothRep.{0, uG, max uI uG uV} ℂ G) (I : Finset ι)
    (Q : D ⥤ SmoothRep.{0, uG, max uI uG uV} ℂ (M I)) (d : ℕ)
    (s0 : {s : Finset ι // s.card = d}) (i : ℕ)
    (β : F ⋙ stepFunctor.{uI, uG, uV} P M U h hclosed T cs I s0.1 i ⟶ Q)
    (hβ : ∀ X, Function.Bijective (SmoothRep.hom (β.app X)))
    (hcan : ∀ X, Function.Bijective
      (cokernelCoordinate.{uI, uG, max uI uV} P M U h hclosed hδ hP hU T cs (F.obj X)
        I d s0 i)) :
    Nonempty (F ⋙ jacquetCokernel.{uI, uG, uV} P M U h hclosed hδ hP hU I d ≅ Q) := by
  have hcanIso : ∀ X, IsIso ((Functor.whiskerLeft F
      (canonicalMap.{uI, uG, uV} P M U h hclosed hδ hP hU T cs I d s0 i)).app X) :=
    fun X => isIso_of_bijective _ (hcan X)
  have hβIso : ∀ X, IsIso (β.app X) := fun X => isIso_of_bijective _ (hβ X)
  have : IsIso (Functor.whiskerLeft F
      (canonicalMap.{uI, uG, uV} P M U h hclosed hδ hP hU T cs I d s0 i)) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso β := NatIso.isIso_of_isIso_app _
  exact ⟨(asIso (Functor.whiskerLeft F
    (canonicalMap.{uI, uG, uV} P M U h hclosed hδ hP hU T cs I d s0 i))).symm ≪≫ asIso β⟩

end Categorical

section Graded

variable [SigmaCompactSpace G] [T2Space G]
  [∀ J, CompactSpace (Induction.LeftQuotient (P J))]
  (hPc : ∀ J, IsClosed (P J : Set G))

/-- The graded maps `β_s` of the step `i + 1` of the coordinate `s`, for a natural
family of orbit Jacquet data on a diagram, as a natural transformation to
`Ad(m)(r_K)`. -/
def gradedNat {D : Type*} [Category D] (F : D ⥤ SmoothRep.{0, uG, max uI uG uV} ℂ G)
    {I s : Finset ι} {i : ℕ} {m : G}
    (H : CorrectedFiltration.SurvivingSupportHypotheses P T cs I s i m)
    (hNc : Jacquet.Localization.IsLimitOfCompactSubgroups ((U I).subgroupOf (P I)))
    {w : Group.RelativeWeyl.Weyl T} {K : Finset ι}
    (hK : ∀ x : G, x ∈ M I ↔ m⁻¹ * x * m ∈ M K)
    (DE : ∀ X, CorrectedFiltration.OrbitJacquetData.{uI, uG, max uI uV} P M U h hclosed hU
      T cs I (F.obj X) w m K hK)
    (hnat : ∀ {X Y : D} (f : X ⟶ Y), (DE X).IsNatural (DE Y) (F.map f))
    (hKs : K ⊆ Finset.univ \ s)
    (hs : Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I w) :
    F ⋙ stepFunctor.{uI, uG, uV} P M U h hclosed T cs I s (i + 1) ⟶
      F ⋙ jacquetFunctor.{uG, max uI uG uV} (h K) (hclosed K) ⋙ conjugationFunctor m hK where
  app X := CorrectedFiltration.stepGradedMap.{uI, uG, max uI uV} P M U h hclosed hδ T cs hPc
    H (F.obj X) hNc hU hK (DE X) hKs hs
  naturality X Y f := CorrectedFiltration.stepGradedMap_natural.{uI, uG, max uI uV} P M U h
    hclosed hδ T cs hPc H (F.map f) hNc hU hK (DE X) (DE Y) hKs hs (hnat f)

/-- At a grade whose lower step of the coordinate `s` vanishes, the graded maps are
bijective. -/
theorem gradedNat_app_bijective {D : Type*} [Category D]
    (F : D ⥤ SmoothRep.{0, uG, max uI uG uV} ℂ G)
    {I s : Finset ι} {i : ℕ} {m : G}
    (H : CorrectedFiltration.SurvivingSupportHypotheses P T cs I s i m)
    (hNc : Jacquet.Localization.IsLimitOfCompactSubgroups ((U I).subgroupOf (P I)))
    {w : Group.RelativeWeyl.Weyl T} {K : Finset ι}
    (hK : ∀ x : G, x ∈ M I ↔ m⁻¹ * x * m ∈ M K)
    (DE : ∀ X, CorrectedFiltration.OrbitJacquetData.{uI, uG, max uI uV} P M U h hclosed hU
      T cs I (F.obj X) w m K hK)
    (hnat : ∀ {X Y : D} (f : X ⟶ Y), (DE X).IsNatural (DE Y) (F.map f))
    (hKs : K ⊆ Finset.univ \ s)
    (hs : Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I w)
    (hθ : CorrectedFiltration.modifiedSupport cs (Finset.univ \ s) I i = ∅) (X : D) :
    Function.Bijective (SmoothRep.hom ((gradedNat.{uI, uG, uV} P M U h hclosed hδ hU T cs hPc
      F H hNc hK DE hnat hKs hs).app X)) := by
  refine ⟨?_, CorrectedFiltration.stepGradedMap_surjective.{uI, uG, max uI uV} P M U h hclosed
    hδ T cs hPc H (F.obj X) hNc hU hK (DE X) hKs hs⟩
  intro a b hab
  have h0 : SmoothRep.hom ((gradedNat.{uI, uG, uV} P M U h hclosed hδ hU T cs hPc
      F H hNc hK DE hnat hKs hs).app X) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hmem := (CorrectedFiltration.stepGradedMap_eq_zero_iff.{uI, uG, max uI uV} P M U h
    hclosed hδ T cs hPc H (F.obj X) hNc hU hK (DE X) hKs hs (a - b)).mp h0
  rw [step_eq_bot_of_modifiedSupport_eq_empty.{uI, uG, max uI uV} P M U h hclosed T cs
    (F.obj X) I s i hθ] at hmem
  exact sub_eq_zero.mp (Subtype.ext hmem)

include hPc in
/-- The associated-Levi comparison on a full subcategory `C`, from the surviving
coordinate step `s0` of the terminal degree: graded exactness above `i0`, the
vanishing and concentration of the step `i0 + 1`, and a natural family of orbit
Jacquet data whose graded maps at `i0` are bijective. -/
theorem associatedLeviComparison_of_survivingStep
    (C : ObjectProperty (SmoothRep.{0, uG, max uI uG uV} ℂ G)) (I : Finset ι)
    (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups (U I))
    (s0 : {s : Finset ι // s.card = Complex.terminalDegree I}) (i0 : ℕ)
    {m : G} {K : Finset ι} (hK : ∀ x : G, x ∈ M I ↔ m⁻¹ * x * m ∈ M K)
    (hMK : IsClosed (M K : Set G))
    (hLeviK : ∀ L : Finset K,
      IsSemidirectDecomposition ((P (leviIndex K L)).subgroupOf (M K))
        ((M (leviIndex K L)).subgroupOf (M K)) ((U (leviIndex K L)).subgroupOf (M K)))
    (hLeviδK : letI := hMK.locallyCompactSpace
      ∀ L : Finset K, IsUnimodularModulus ((U (leviIndex K L)).subgroupOf (M K))
        ((hclosed (leviIndex K L)).preimage continuous_subtype_val))
    (hcover : CorrectedFiltration.IsBruhatCover T (P ∅) (P I))
    (hlow : ∀ s : Finset ι, s.card + 1 = Complex.terminalDegree I →
      CorrectedFiltration.modifiedSupport cs (Finset.univ \ s) I (i0 + 1) = ∅)
    (hconc : ∀ s : {s : Finset ι // s.card = Complex.terminalDegree I}, s ≠ s0 →
      CorrectedFiltration.modifiedSupport cs (Finset.univ \ s.1) I (i0 + 1) = ∅)
    (htop : Complex.terminalDegree I = 0 →
      (Support.rankOrderedList cs.length).length ≤ i0 + 1)
    (hsurj : ∀ E, C E → ∀ k, k + 1 = Complex.terminalDegree I → ∀ i, i0 < i →
      i < (Support.rankOrderedList cs.length).length →
      Function.Surjective
        (gradedDifferential.{uI, uG, max uI uV} P M U h hclosed hδ hP hU T cs E I i k))
    (hinj : ∀ E, C E → Complex.terminalDegree I = 1 → ∀ i, i0 < i →
      i < (Support.rankOrderedList cs.length).length →
      Function.Injective
        (gradedDifferential.{uI, uG, max uI uV} P M U h hclosed hδ hP hU T cs E I i 0))
    (hex : ∀ E, C E → ∀ k, k + 2 = Complex.terminalDegree I → ∀ i, i0 < i →
      i < (Support.rankOrderedList cs.length).length →
      LinearMap.range
          (gradedDifferential.{uI, uG, max uI uV} P M U h hclosed hδ hP hU T cs E I i k) =
        LinearMap.ker
          (gradedDifferential.{uI, uG, max uI uV} P M U h hclosed hδ hP hU T cs E I i (k + 1)))
    (H : CorrectedFiltration.SurvivingSupportHypotheses P T cs I s0.1 i0 m)
    (hNc : Jacquet.Localization.IsLimitOfCompactSubgroups ((U I).subgroupOf (P I)))
    {w : Group.RelativeWeyl.Weyl T}
    (DE : ∀ X : C.FullSubcategory, CorrectedFiltration.OrbitJacquetData.{uI, uG, max uI uV}
      P M U h hclosed hU T cs I (C.ι.obj X) w m K hK)
    (hnat : ∀ {X Y : C.FullSubcategory} (f : X ⟶ Y), (DE X).IsNatural (DE Y) (C.ι.map f))
    (hKs : K ⊆ Finset.univ \ s0.1)
    (hs : Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s0.1) I w)
    (hθ : CorrectedFiltration.modifiedSupport cs (Finset.univ \ s0.1) I i0 = ∅) :
    Nonempty ((C.ι ⋙ StandardComplex.sharpFunctor.{uI, uG, max uI uV}
          P M U h hclosed hδ hP hU I ⋙ jacquetFunctor.{uG, max uI uG uV} (h I) (hclosed I)) ≅
        (C.ι ⋙ jacquetFunctor.{uG, max uI uG uV} (h K) (hclosed K) ⋙
          LeviComplex.sharpFunctor.{uI, uG, uV} P M U hclosed hP hU K hMK hLeviK hLeviδK
            Finset.univ ⋙
          conjugationFunctor.{uG, max uI uG uV} m hK)) := by
  obtain ⟨e⟩ := jacquetCokernel_nonempty_iso.{uI, uG, uV} P M U h hclosed hδ hP hU T cs C.ι I
    (C.ι ⋙ jacquetFunctor.{uG, max uI uG uV} (h K) (hclosed K) ⋙
      conjugationFunctor.{uG, max uI uG uV} m hK)
    (Complex.terminalDegree I) s0 (i0 + 1)
    (gradedNat.{uI, uG, uV} P M U h hclosed hδ hU T cs hPc C.ι H hNc hK DE hnat hKs hs)
    (gradedNat_app_bijective.{uI, uG, uV} P M U h hclosed hδ hU T cs hPc C.ι H hNc hK DE
      hnat hKs hs hθ)
    (fun X => ⟨cokernelCoordinate_injective.{uI, uG, max uI uV} P M U h hclosed hδ hP hU T cs
        X.obj I _ s0 i0 hcover hlow (hinj X.obj X.property) (hex X.obj X.property),
      cokernelCoordinate_surjective.{uI, uG, max uI uV} P M U h hclosed hδ hP hU T cs
        X.obj I _ s0 i0 hcover hconc htop (hsurj X.obj X.property)⟩)
  exact ⟨StandardComplex.jacquetSharpCokernelIsoOn.{uI, uG, uV} P M U h hclosed hδ hP hU C I
      hUc ≪≫ e ≪≫
    (Functor.isoWhiskerLeft C.ι (Functor.isoWhiskerLeft
      (jacquetFunctor.{uG, max uI uG uV} (h K) (hclosed K))
      (Functor.isoWhiskerRight (LeviComplex.sharpFunctorUnivIso.{uI, uG, uV} P M U hclosed hP hU
          K hMK hLeviK hLeviδK) (conjugationFunctor.{uG, max uI uG uV} m hK) ≪≫
        Functor.leftUnitor _))).symm⟩

end Graded

end Langlands.Aubert.General.JacquetComplex
