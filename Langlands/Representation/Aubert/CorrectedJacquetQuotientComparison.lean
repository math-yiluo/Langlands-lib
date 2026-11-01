import Langlands.Representation.Aubert.CorrectedJacquetCutFiltration

/-! Typed comparisons of the actual coordinate support quotients. -/

noncomputable section

set_option maxHeartbeats 800000

namespace Langlands.Aubert.ActualCutComplex

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  (A : letI := T.topology
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier))
  (C : BlockShape n)

local macro "normalize_coordinate_carriers" : tactic =>
  `(tactic| dsimp (config := { instances := true }) only
    [jacquetDiagram, EquivariantDiagram.jacquetDiagram, diagram, Term,
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
    Rep.V, Rep.hV1, Rep.hV2, inferInstance,
    Complex.instSemiring, Complex.instCommSemiring, Complex.commRing,
    CommRing.toCommSemiring] at *)

/-- Compare the unbundled and bundled actual coordinate Jacquet carriers. -/
def cutCoordinateEquiv (s : Finset (Fin (n - 1))) :
    letI := T.topology
    (jacquetDiagram T C A.obj.ρ).Obj s ≃ₗ[ℂ]
      Support.cutJacquetObject T A (shape s) C := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := T.generalLinearTopologicalGroup n
  normalize_coordinate_carriers
  with_reducible exact LinearEquiv.refl ℂ _

theorem cutCoordinateEquiv_map {s t : Finset (Fin (n - 1))} (h : s ⊆ t) :
    letI := T.topology
    ∀ x : (jacquetDiagram T C A.obj.ρ).Obj s,
      cutCoordinateEquiv T A C t ((jacquetDiagram T C A.obj.ρ).map h x) =
        Support.cutJacquetMap T A C (B := shape s) (D := shape t)
          (by simpa using h) (cutCoordinateEquiv T A C s x) := by
  let := T.topology
  simp only [jacquetDiagram_map]
  dsimp (config := { instances := true }) only [cutCoordinateEquiv, Support.cutJacquetMap,
    transition]
  normalize_coordinate_carriers
  intro x
  simp only [LinearEquiv.refl_apply]
  rfl

theorem cutCoordinateEquiv_mem_support
    (θ : Set (Equiv.Perm (Fin n))) (s : Finset (Fin (n - 1))) :
    letI := T.topology
    ∀ x : (jacquetDiagram T C A.obj.ρ).Obj s,
      cutCoordinateEquiv T A C s x ∈
        (Support.correctedJacquetSupport T (shape s) C θ).obj
          ((T.normalizedJacquetFunctor (shape s)).obj A) ↔
        x ∈ correctedCoordinateSupport T A C θ s := by
  let := T.topology
  dsimp (config := { instances := true }) only [cutCoordinateEquiv,
    correctedCoordinateSupport]
  normalize_coordinate_carriers
  intro x
  simp only [LinearEquiv.refl_apply]
  rfl

/-- The actual upper support submodules have a typed carrier equivalence. -/
def cutCoordinateSupportEquiv
    (θ : Set (Equiv.Perm (Fin n))) (s : Finset (Fin (n - 1))) :
    letI := T.topology
    (correctedSupportSubdiagram T A C θ).obj s ≃ₗ[ℂ]
      (Support.correctedJacquetSupport T (shape s) C θ).representation
        ((T.normalizedJacquetFunctor (shape s)).obj A) := by
  letI := T.topology
  exact
    { toFun := fun x => ⟨cutCoordinateEquiv T A C s x.1,
        (cutCoordinateEquiv_mem_support T A C θ s x.1).mpr x.property⟩
      invFun := fun y => ⟨(cutCoordinateEquiv T A C s).symm y.1,
        (cutCoordinateEquiv_mem_support T A C θ s _).mp (by
          rw [(cutCoordinateEquiv T A C s).apply_symm_apply y.1]
          exact y.property)⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact (cutCoordinateEquiv T A C s).symm_apply_apply x.1
      right_inv := by
        intro y
        apply Subtype.ext
        exact (cutCoordinateEquiv T A C s).apply_symm_apply y.1
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add (cutCoordinateEquiv T A C s) x.1 y.1
      map_smul' := by
        intro a x
        apply Subtype.ext
        exact map_smul (cutCoordinateEquiv T A C s) a x.1 }

theorem cutCoordinateSupportEquiv_coe
    (θ : Set (Equiv.Perm (Fin n))) (s : Finset (Fin (n - 1))) :
    letI := T.topology
    ∀ x : (correctedSupportSubdiagram T A C θ).obj s,
      (cutCoordinateSupportEquiv T A C θ s x).1 = cutCoordinateEquiv T A C s x.1 := by
  intros
  rfl

theorem cutCoordinateSupportEquiv_mem_lower
    (θ η : Set (Equiv.Perm (Fin n))) (s : Finset (Fin (n - 1))) :
    letI := T.topology
    ∀ x : (correctedSupportSubdiagram T A C η).obj s,
      cutCoordinateSupportEquiv T A C η s x ∈
        ((Support.correctedJacquetSupport T (shape s) C θ).lowerInUpper
          (Support.correctedJacquetSupport T (shape s) C η)
          ((T.normalizedJacquetFunctor (shape s)).obj A)).toSubmodule ↔
      x ∈ (correctedSupportSubdiagram T A C θ).denominator
        (correctedSupportSubdiagram T A C η) s := by
  let := T.topology
  intro x
  dsimp only [RepSubfunctor.lowerInUpper,
    CutComplex.Diagram.Subdiagram.denominator]
  simp only [Submodule.mem_comap, Submodule.subtype_apply]
  dsimp only [correctedSupportSubdiagram]
  exact cutCoordinateEquiv_mem_support T A C θ s x.1

private theorem cutCoordinateSupportEquiv_map_lower
    (θ η : Set (Equiv.Perm (Fin n))) (s : Finset (Fin (n - 1))) :
    letI := T.topology
    ((correctedSupportSubdiagram T A C θ).denominator
        (correctedSupportSubdiagram T A C η) s).map
      (cutCoordinateSupportEquiv T A C η s).toLinearMap =
        ((Support.correctedJacquetSupport T (shape s) C θ).lowerInUpper
          (Support.correctedJacquetSupport T (shape s) C η)
          ((T.normalizedJacquetFunctor (shape s)).obj A)).toSubmodule := by
  let := T.topology
  apply Submodule.ext
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (cutCoordinateSupportEquiv_mem_lower T A C θ η s x).mpr hx
  · intro hy
    obtain ⟨x, rfl⟩ := (cutCoordinateSupportEquiv T A C η s).surjective y
    exact ⟨x, (cutCoordinateSupportEquiv_mem_lower T A C θ η s x).mp hy, rfl⟩

/-- The actual coordinate quotient, compared by a linear equivalence. -/
def cutCoordinateQuotientEquiv
    (θ η : Set (Equiv.Perm (Fin n))) (s : Finset (Fin (n - 1))) :
    letI := T.topology
    (correctedSupportQuotientDiagram T A C θ η).Obj s ≃ₗ[ℂ]
      Support.cutSupportQuotient T A C (shape s) θ η := by
  letI := T.topology
  exact Submodule.Quotient.equiv _ _ (cutCoordinateSupportEquiv T A C η s)
    (cutCoordinateSupportEquiv_map_lower T A C θ η s)

theorem cutCoordinateQuotientEquiv_mk
    (θ η : Set (Equiv.Perm (Fin n))) (s : Finset (Fin (n - 1))) :
    letI := T.topology
    ∀ x : (correctedSupportSubdiagram T A C η).obj s,
      cutCoordinateQuotientEquiv T A C θ η s
        (((correctedSupportSubdiagram T A C θ).denominator
          (correctedSupportSubdiagram T A C η) s).mkQ x) =
      ((Support.correctedJacquetSupport T (shape s) C θ).quotientProjection
        (Support.correctedJacquetSupport T (shape s) C η)
        ((T.normalizedJacquetFunctor (shape s)).obj A)).hom
          (cutCoordinateSupportEquiv T A C η s x) := by
  intros
  rfl

theorem cutCoordinateSupportEquiv_map
    (η : Set (Equiv.Perm (Fin n))) {s t : Finset (Fin (n - 1))} (h : s ⊆ t) :
    letI := T.topology
    ∀ x : (correctedSupportSubdiagram T A C η).obj s,
      cutCoordinateSupportEquiv T A C η t
        ⟨(jacquetDiagram T C A.obj.ρ).map h x.1,
          (correctedSupportSubdiagram T A C η).map_mem h x.1 x.property⟩ =
      (Support.cutJacquetSupportMap T A C (B := shape s) (D := shape t)
        (by simpa using h) η).hom (cutCoordinateSupportEquiv T A C η s x) := by
  let := T.topology
  intro x
  apply Subtype.ext
  dsimp only [Support.cutJacquetSupportMap, Rep.Hom.hom, Rep.ofHom]
  simp only [CategoryTheory.ConcreteCategory.hom_ofHom]
  exact cutCoordinateEquiv_map T A C h x.1

/-- The typed quotient comparison intertwines the actual descended cut maps. -/
theorem cutCoordinateQuotientEquiv_map
    (θ η : Set (Equiv.Perm (Fin n))) {s t : Finset (Fin (n - 1))} (h : s ⊆ t) :
    letI := T.topology
    ∀ q : (correctedSupportQuotientDiagram T A C θ η).Obj s,
      cutCoordinateQuotientEquiv T A C θ η t
          ((correctedSupportQuotientDiagram T A C θ η).map h q) =
        (Support.cutSupportQuotientMap T A C (B := shape s) (D := shape t)
          (by simpa using h) θ η).hom (cutCoordinateQuotientEquiv T A C θ η s q) := by
  let := T.topology
  intro q
  obtain ⟨x, rfl⟩ := ((correctedSupportSubdiagram T A C θ).denominator
    (correctedSupportSubdiagram T A C η) s).mkQ_surjective q
  rw [CutComplex.Diagram.Subdiagram.quotientDiagram_map_mk,
    cutCoordinateQuotientEquiv_mk, cutCoordinateQuotientEquiv_mk,
    Support.cutSupportQuotientMap_projection, cutCoordinateSupportEquiv_map]

end Langlands.Aubert.ActualCutComplex
