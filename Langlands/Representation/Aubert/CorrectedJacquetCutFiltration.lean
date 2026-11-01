import Langlands.Representation.Aubert.FilteredCutDiagram
import Langlands.Representation.Aubert.JacquetCutComplex
import Langlands.Representation.Aubert.CorrectedSupportTransitions
import Langlands.Representation.Filtration.FiniteFilteredExactness
import Mathlib.Algebra.Exact.Basic

/-! Corrected support filtrations on the actual homogeneous Jacquet cut complex. -/

noncomputable section

set_option maxHeartbeats 800000

namespace Langlands.Aubert.ActualCutComplex

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}

variable (A : letI := T.topology
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier))
  (C : BlockShape n)

private def bundledCoordinateSupport (θ : Set (Equiv.Perm (Fin n))) (s : Finset (Fin (n - 1))) :
    letI := T.topology
    Submodule ℂ (Support.cutJacquetObject T A (shape s) C) :=
  letI := T.topology
  ((Support.correctedJacquetSupport.{uF,uV} T (shape s) C θ).obj
    ((T.normalizedJacquetFunctor.{uF,uV} (shape s)).obj A)).toSubmodule

set_option maxHeartbeats 400000 in
/-- The actual corrected support in a coordinate Jacquet module. -/
def correctedCoordinateSupport (θ : Set (Equiv.Perm (Fin n))) (s : Finset (Fin (n - 1))) :
    Submodule ℂ ((jacquetDiagram T C A.obj.ρ).Obj s) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := T.generalLinearTopologicalGroup n
  have H := bundledCoordinateSupport T A C θ s
  dsimp (config := { instances := true }) only [jacquetDiagram, EquivariantDiagram.jacquetDiagram, diagram, Term,
    Support.cutJacquetObject, Support.cutTermObject,
    PadicField.TopologicalData.normalizedJacquetFunctor,
    PadicField.TopologicalData.normalizedParabolicInductionFunctor,
    BlockShape.normalizedJacquetFunctorOf, BlockShape.normalizedJacquetObjectOf,
    BlockShape.normalizedInductionFunctorOf, SmoothRep.of, Rep.of,
    SmoothRep.instAddCommGroupVObjRepSmoothRepProperty,
    SmoothRep.instModuleVObjRepSmoothRepProperty,
    SmoothRep.representation, Transition.term, Transition.inducing,
    BlockShape.inducingRepresentation, BlockShape.inflateCharacter,
    PadicField.TopologicalData.leviHalfCharacter,
    PadicField.TopologicalData.parabolicHalfModulus,
    PadicField.TopologicalData.normalizedJacquet,
    PadicField.TopologicalData.normalizedParabolicInduced,
    BlockShape.normalizedInducedOf, Induction.normalizedSmoothInduced] at H ⊢
  with_reducible exact H

local macro "normalize_cut_carriers" : tactic =>
  `(tactic| dsimp (config := { instances := true }) only [jacquetDiagram, EquivariantDiagram.jacquetDiagram, diagram, Term,
    Support.cutJacquetObject, Support.cutTermObject,
    PadicField.TopologicalData.normalizedJacquetFunctor,
    PadicField.TopologicalData.normalizedParabolicInductionFunctor,
    BlockShape.normalizedJacquetFunctorOf, BlockShape.normalizedJacquetObjectOf,
    BlockShape.normalizedInductionFunctorOf, SmoothRep.of, Rep.of,
    SmoothRep.instAddCommGroupVObjRepSmoothRepProperty,
    SmoothRep.instModuleVObjRepSmoothRepProperty,
    SmoothRep.representation, Transition.term, Transition.inducing,
    BlockShape.inducingRepresentation, BlockShape.inflateCharacter,
    PadicField.TopologicalData.leviHalfCharacter,
    PadicField.TopologicalData.parabolicHalfModulus,
    PadicField.TopologicalData.normalizedJacquet,
    PadicField.TopologicalData.normalizedParabolicInduced,
    BlockShape.normalizedInducedOf, Induction.normalizedSmoothInduced,
    id, Geometric.jacquetInductionFunctor, SmoothRep.toRep,
    Support.cutJacquetMap, transition, correctedCoordinateSupport, bundledCoordinateSupport] at *)

private theorem bundledMapMem (θ : Set (Equiv.Perm (Fin n)))
    {s t : Finset (Fin (n - 1))} (h : s ⊆ t) :
    letI := T.topology
    ∀ x : Support.cutJacquetObject T A (shape s) C,
      x ∈ bundledCoordinateSupport T A C θ s →
      Support.cutJacquetMap T A C (B := shape s) (D := shape t)
          (by simpa using h) x ∈ bundledCoordinateSupport T A C θ t := by
  let := T.topology
  intro x hx
  exact Support.cutJacquetMap_mem_correctedJacquetSupport T A C
    (B := shape s) (D := shape t) (by simpa using h) θ x hx

def correctedSupportSubdiagram (θ : Set (Equiv.Perm (Fin n))) :
    (jacquetDiagram T C A.obj.ρ).Subdiagram := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  exact {
    obj s := correctedCoordinateSupport T A C θ s
    map_mem := by
      simp only [jacquetDiagram_map]
      normalize_cut_carriers
      intro s t h
      have H := bundledMapMem T A C θ h
      normalize_cut_carriers
      intro x hx
      have hx' := H x hx
      exact hx' }

private theorem bundledMono {θ η : Set (Equiv.Perm (Fin n))}
    (h : θ ⊆ η) (s : Finset (Fin (n - 1))) :
    letI := T.topology
    bundledCoordinateSupport T A C θ s ≤ bundledCoordinateSupport T A C η s := by
  let := T.topology
  exact Support.correctedJacquetSupport_mono T (shape s) C h _

private theorem bundledEmpty (s : Finset (Fin (n - 1))) :
    letI := T.topology
    bundledCoordinateSupport T A C ∅ s = ⊥ := by
  let := T.topology
  unfold bundledCoordinateSupport
  rw [Support.correctedJacquetSupport_empty]
  rfl

private theorem bundledUniv (s : Finset (Fin (n - 1))) :
    letI := T.topology
    bundledCoordinateSupport T A C Set.univ s = ⊤ := by
  let := T.topology
  unfold bundledCoordinateSupport
  rw [Support.correctedJacquetSupport_univ]
  rfl

theorem correctedCoordinateSupport_mono {θ η : Set (Equiv.Perm (Fin n))}
    (h : θ ⊆ η) (s : Finset (Fin (n - 1))) :
    correctedCoordinateSupport T A C θ s ≤ correctedCoordinateSupport T A C η s := by
  have H := bundledMono T A C h s
  normalize_cut_carriers
  exact H

@[simp] theorem correctedCoordinateSupport_empty (s : Finset (Fin (n - 1))) :
    correctedCoordinateSupport T A C ∅ s = ⊥ := by
  have H := bundledEmpty T A C s
  normalize_cut_carriers
  with_reducible exact H

@[simp] theorem correctedCoordinateSupport_univ (s : Finset (Fin (n - 1))) :
    correctedCoordinateSupport T A C Set.univ s = ⊤ := by
  have H := bundledUniv T A C s
  normalize_cut_carriers
  with_reducible exact H

/-- The actual homogeneous coordinate support submodule. -/
abbrev correctedDegreeSupport (θ : Set (Equiv.Perm (Fin n))) (k : ℕ) :
    Submodule ℂ ((jacquetDiagram T C A.obj.ρ).Degree k) :=
  (correctedSupportSubdiagram T A C θ).degreeSubmodule k

theorem mem_correctedDegreeSupport_iff (θ : Set (Equiv.Perm (Fin n))) (k : ℕ)
    (x : (jacquetDiagram T C A.obj.ρ).Degree k) :
    x ∈ correctedDegreeSupport T A C θ k ↔
      ∀ s, x s ∈ (correctedSupportSubdiagram T A C θ).obj s.1 := Iff.rfl

theorem correctedDegreeSupport_mono {θ η : Set (Equiv.Perm (Fin n))}
    (h : θ ⊆ η) (k : ℕ) :
    correctedDegreeSupport T A C θ k ≤ correctedDegreeSupport T A C η k := by
  intro x hx s
  exact correctedCoordinateSupport_mono T A C h s.1 (hx s)

@[simp] theorem correctedDegreeSupport_empty (k : ℕ) :
    correctedDegreeSupport T A C (∅ : Set (Equiv.Perm (Fin n))) k = ⊥ := by
  apply le_antisymm
  · intro x hx
    change x = 0
    funext s
    have hs := hx s
    change x s ∈ correctedCoordinateSupport T A C ∅ s.1 at hs
    rw [correctedCoordinateSupport_empty] at hs
    exact hs
  · exact bot_le

@[simp] theorem correctedDegreeSupport_univ (k : ℕ) :
    correctedDegreeSupport T A C (Set.univ : Set (Equiv.Perm (Fin n))) k = ⊤ := by
  apply le_antisymm le_top
  intro x _ s
  change x s ∈ correctedCoordinateSupport T A C Set.univ s.1
  rw [correctedCoordinateSupport_univ]
  trivial

theorem degreeDifferential_mem_correctedDegreeSupport
    (θ : Set (Equiv.Perm (Fin n))) (k : ℕ)
    (x : (jacquetDiagram T C A.obj.ρ).Degree k)
    (hx : x ∈ correctedDegreeSupport T A C θ k) :
    (jacquetDiagram T C A.obj.ρ).degreeDifferential k x ∈
      correctedDegreeSupport T A C θ (k + 1) :=
  (correctedSupportSubdiagram T A C θ).degreeDifferential_mem k x hx

/-- The diagram of actual corrected support quotients. -/
abbrev correctedSupportQuotientDiagram (θ η : Set (Equiv.Perm (Fin n))) :
    CutComplex.Diagram (Fin (n - 1)) :=
  (correctedSupportSubdiagram T A C θ).quotientDiagram
    (correctedSupportSubdiagram T A C η)

/-- Its coordinate modules are the existing actual support quotients. -/
theorem correctedSupportQuotientDiagram_obj
    (θ η : Set (Equiv.Perm (Fin n))) (s : Finset (Fin (n - 1))) :
    letI := T.topology
    (correctedSupportQuotientDiagram T A C θ η).Obj s =
      Support.cutSupportQuotient T A C (shape s) θ η := by
  let := T.topology
  dsimp (config := { instances := true }) only [correctedSupportQuotientDiagram,
    CutComplex.Diagram.Subdiagram.quotientDiagram,
    CutComplex.Diagram.Subdiagram.denominator, correctedSupportSubdiagram,
    Support.cutSupportQuotient, RepSubfunctor.quotientObj, RepSubfunctor.lowerInUpper,
    RepSubfunctor.representation, Rep.quotient, Rep.of]
  normalize_cut_carriers
  dsimp (config := { instances := true }) only [Complex.instSemiring,
    Complex.instCommSemiring, Complex.commRing, CommRing.toCommSemiring,
    Submodule.addCommMonoid, Submodule.addCommGroup, AddSubmonoidClass.toAddCommMonoid,
    AddSubmonoidClass.toAddMonoid, AddSubgroupClass.toAddCommGroup,
    AddSubgroupClass.toAddGroup, AddCommGroup.toAddCommMonoid]
  with_reducible congr 3
  all_goals with_reducible (funext x; congr 1)

/-- A sequence of Weyl supports gives actual support submodules in each
homogeneous Jacquet degree. -/
def correctedDegreeFiltration (θ : ℕ → Set (Equiv.Perm (Fin n))) (k : ℕ) :
    ℕ → Submodule ℂ ((jacquetDiagram T C A.obj.ρ).Degree k) :=
  fun i => correctedDegreeSupport T A C (θ i) k

theorem correctedDegreeFiltration_monotone
    (θ : ℕ → Set (Equiv.Perm (Fin n))) (hθ : Monotone θ) (k : ℕ) :
    Monotone (correctedDegreeFiltration T A C θ k) :=
  fun _ _ hij => correctedDegreeSupport_mono T A C (hθ hij) k

theorem correctedDegreeFiltration_zero
    (θ : ℕ → Set (Equiv.Perm (Fin n))) (hθ : θ 0 = ∅) (k : ℕ) :
    correctedDegreeFiltration T A C θ k 0 = ⊥ := by
  change correctedDegreeSupport T A C (θ 0) k = ⊥
  rw [hθ, correctedDegreeSupport_empty]

theorem correctedDegreeFiltration_top
    (θ : ℕ → Set (Equiv.Perm (Fin n))) (m : ℕ)
    (hθ : θ m = Set.univ) (k : ℕ) :
    correctedDegreeFiltration T A C θ k m = ⊤ := by
  change correctedDegreeSupport T A C (θ m) k = ⊤
  rw [hθ, correctedDegreeSupport_univ]

theorem degreeDifferential_preserves_correctedDegreeFiltration
    (θ : ℕ → Set (Equiv.Perm (Fin n))) (k : ℕ) :
    FiniteFiltered.Preserves ((jacquetDiagram T C A.obj.ρ).degreeDifferential k)
      (correctedDegreeFiltration T A C θ k)
      (correctedDegreeFiltration T A C θ (k + 1)) :=
  fun i x hx => degreeDifferential_mem_correctedDegreeSupport T A C (θ i) k x hx

/-- The actual associated grade of the homogeneous support filtration is the
homogeneous product of the existing actual coordinate support quotients. -/
def correctedGradedEquiv (θ : ℕ → Set (Equiv.Perm (Fin n))) (i k : ℕ) :
    FiniteFiltered.Graded (correctedDegreeFiltration T A C θ k) i ≃ₗ[ℂ]
      (correctedSupportQuotientDiagram T A C (θ i) (θ (i + 1))).Degree k :=
  (correctedSupportSubdiagram T A C (θ i)).degreeQuotientEquiv
    (correctedSupportSubdiagram T A C (θ (i + 1))) k

/-- The comparison uses the actual descended homogeneous differential and
retains every exterior insertion sign. -/
theorem correctedGradedEquiv_differential
    (θ : ℕ → Set (Equiv.Perm (Fin n))) (i k : ℕ)
    (x : FiniteFiltered.Graded (correctedDegreeFiltration T A C θ k) i) :
    correctedGradedEquiv T A C θ i (k + 1)
        (FiniteFiltered.gradedMap
          ((jacquetDiagram T C A.obj.ρ).degreeDifferential k)
          (correctedDegreeFiltration T A C θ k)
          (correctedDegreeFiltration T A C θ (k + 1))
          (degreeDifferential_preserves_correctedDegreeFiltration T A C θ k) i x) =
      (correctedSupportQuotientDiagram T A C (θ i) (θ (i + 1))).degreeDifferential k
        (correctedGradedEquiv T A C θ i k x) :=
  (correctedSupportSubdiagram T A C (θ i)).degreeQuotientEquiv_differential
    (correctedSupportSubdiagram T A C (θ (i + 1))) k x

theorem correctedGradedMap_injective_iff
    (θ : ℕ → Set (Equiv.Perm (Fin n))) (i k : ℕ) :
    Function.Injective (FiniteFiltered.gradedMap
      ((jacquetDiagram T C A.obj.ρ).degreeDifferential k)
      (correctedDegreeFiltration T A C θ k)
      (correctedDegreeFiltration T A C θ (k + 1))
      (degreeDifferential_preserves_correctedDegreeFiltration T A C θ k) i) ↔
    Function.Injective
      ((correctedSupportQuotientDiagram T A C (θ i) (θ (i + 1))).degreeDifferential k) := by
  constructor
  · intro hf x y hxy
    apply (correctedGradedEquiv T A C θ i k).symm.injective
    apply hf
    apply (correctedGradedEquiv T A C θ i (k + 1)).injective
    simpa only [correctedGradedEquiv_differential, LinearEquiv.apply_symm_apply] using hxy
  · intro hg x y hxy
    apply (correctedGradedEquiv T A C θ i k).injective
    apply hg
    rw [← correctedGradedEquiv_differential, ← correctedGradedEquiv_differential, hxy]

theorem correctedGradedMap_exact_iff
    (θ : ℕ → Set (Equiv.Perm (Fin n))) (i k : ℕ) :
    LinearMap.range (FiniteFiltered.gradedMap
      ((jacquetDiagram T C A.obj.ρ).degreeDifferential k)
      (correctedDegreeFiltration T A C θ k)
      (correctedDegreeFiltration T A C θ (k + 1))
      (degreeDifferential_preserves_correctedDegreeFiltration T A C θ k) i) =
    LinearMap.ker (FiniteFiltered.gradedMap
      ((jacquetDiagram T C A.obj.ρ).degreeDifferential (k + 1))
      (correctedDegreeFiltration T A C θ (k + 1))
      (correctedDegreeFiltration T A C θ (k + 1 + 1))
      (degreeDifferential_preserves_correctedDegreeFiltration T A C θ (k + 1)) i) ↔
    LinearMap.range
      ((correctedSupportQuotientDiagram T A C (θ i) (θ (i + 1))).degreeDifferential k) =
    LinearMap.ker
      ((correctedSupportQuotientDiagram T A C (θ i) (θ (i + 1))).degreeDifferential (k + 1)) := by
  have h := LinearMap.exact_iff_of_surjective_of_bijective_of_injective
    (FiniteFiltered.gradedMap
      ((jacquetDiagram T C A.obj.ρ).degreeDifferential k)
      (correctedDegreeFiltration T A C θ k)
      (correctedDegreeFiltration T A C θ (k + 1))
      (degreeDifferential_preserves_correctedDegreeFiltration T A C θ k) i)
    (FiniteFiltered.gradedMap
      ((jacquetDiagram T C A.obj.ρ).degreeDifferential (k + 1))
      (correctedDegreeFiltration T A C θ (k + 1))
      (correctedDegreeFiltration T A C θ (k + 1 + 1))
      (degreeDifferential_preserves_correctedDegreeFiltration T A C θ (k + 1)) i)
    ((correctedSupportQuotientDiagram T A C (θ i) (θ (i + 1))).degreeDifferential k)
    ((correctedSupportQuotientDiagram T A C (θ i) (θ (i + 1))).degreeDifferential (k + 1))
    (correctedGradedEquiv T A C θ i k).toLinearMap
    (correctedGradedEquiv T A C θ i (k + 1)).toLinearMap
    (correctedGradedEquiv T A C θ i (k + 1 + 1)).toLinearMap
    (LinearMap.ext (fun x => (correctedGradedEquiv_differential T A C θ i k x).symm))
    (LinearMap.ext (fun x => (correctedGradedEquiv_differential T A C θ i (k + 1) x).symm))
    (correctedGradedEquiv T A C θ i k).surjective
    (correctedGradedEquiv T A C θ i (k + 1)).bijective
    (correctedGradedEquiv T A C θ i (k + 1 + 1)).injective
  constructor
  · intro hex
    exact (LinearMap.exact_iff.mp (h.mp (LinearMap.exact_iff.mpr hex.symm))).symm
  · intro hex
    exact (LinearMap.exact_iff.mp (h.mpr (LinearMap.exact_iff.mpr hex.symm))).symm

/-- Injectivity of the actual coordinate quotient differentials lifts through
an empty-to-full finite corrected support filtration. -/
theorem degreeDifferential_injective_of_correctedGraded
    (θ : ℕ → Set (Equiv.Perm (Fin n))) (hzero : θ 0 = ∅)
    (m : ℕ) (htop : θ m = Set.univ) (k : ℕ)
    (hinj : ∀ i < m, Function.Injective
      ((correctedSupportQuotientDiagram T A C (θ i) (θ (i + 1))).degreeDifferential k)) :
    Function.Injective ((jacquetDiagram T C A.obj.ρ).degreeDifferential k) :=
  FiniteFiltered.injective_of_graded_injective _
    (correctedDegreeFiltration T A C θ k)
    (correctedDegreeFiltration T A C θ (k + 1))
    (degreeDifferential_preserves_correctedDegreeFiltration T A C θ k)
    (correctedDegreeFiltration_zero T A C θ hzero k) m
    (correctedDegreeFiltration_top T A C θ m htop k)
    (fun i hi => (correctedGradedMap_injective_iff T A C θ i k).mpr (hinj i hi))

/-- Middle exactness of the actual coordinate quotient differentials lifts
through a monotone empty-to-full finite corrected support filtration. -/
theorem degreeDifferential_exact_of_correctedGraded
    (θ : ℕ → Set (Equiv.Perm (Fin n))) (hmono : Monotone θ) (hzero : θ 0 = ∅)
    (m : ℕ) (htop : θ m = Set.univ) (k : ℕ)
    (hex : ∀ i < m,
      LinearMap.range
        ((correctedSupportQuotientDiagram T A C (θ i) (θ (i + 1))).degreeDifferential k) =
      LinearMap.ker
        ((correctedSupportQuotientDiagram T A C (θ i) (θ (i + 1))).degreeDifferential (k + 1))) :
    LinearMap.range ((jacquetDiagram T C A.obj.ρ).degreeDifferential k) =
      LinearMap.ker ((jacquetDiagram T C A.obj.ρ).degreeDifferential (k + 1)) :=
  FiniteFiltered.range_eq_ker_of_graded_exact _ _
    (correctedDegreeFiltration T A C θ k)
    (correctedDegreeFiltration T A C θ (k + 1))
    (correctedDegreeFiltration T A C θ (k + 1 + 1))
    (degreeDifferential_preserves_correctedDegreeFiltration T A C θ k)
    (degreeDifferential_preserves_correctedDegreeFiltration T A C θ (k + 1))
    (correctedDegreeFiltration_monotone T A C θ hmono k)
    (correctedDegreeFiltration_zero T A C θ hzero (k + 1))
    ((jacquetDiagram T C A.obj.ρ).degreeDifferential_square k)
    m (correctedDegreeFiltration_top T A C θ m htop (k + 1))
    (fun i hi => (correctedGradedMap_exact_iff T A C θ i k).mpr (hex i hi))

end Langlands.Aubert.ActualCutComplex
