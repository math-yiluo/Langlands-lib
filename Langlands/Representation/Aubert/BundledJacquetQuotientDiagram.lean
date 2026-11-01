import Langlands.Representation.Aubert.CutDiagramEquivalence
import Langlands.Representation.Aubert.CorrectedJacquetQuotientComparison

/-! Signed diagrams of the actual bundled corrected support quotients. -/

noncomputable section

namespace Langlands.Aubert.ActualCutComplex

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  (A : letI := T.topology
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier))
  (C : BlockShape n)

/-- The objects are the actual bundled support quotients and the maps are
exactly the existing descended actual cut maps. -/
def bundledSupportQuotientDiagram (θ η : Set (Equiv.Perm (Fin n))) :
    CutComplex.Diagram (Fin (n - 1)) := by
  letI := T.topology
  exact {
    Obj s := Support.cutSupportQuotient T A C (shape s) θ η
    add _ := inferInstance
    module _ := inferInstance
    map {s t} h := (Support.cutSupportQuotientMap T A C
      (B := shape s) (D := shape t) (by simpa using h) θ η).hom.toLinearMap
    map_refl s := by
      apply LinearMap.ext
      intro q
      obtain ⟨x, rfl⟩ := (cutCoordinateQuotientEquiv T A C θ η s).surjective q
      simp only [Representation.IntertwiningMap.toLinearMap_apply, LinearMap.id_apply]
      rw [← cutCoordinateQuotientEquiv_map T A C θ η (s := s) (t := s) Finset.Subset.rfl,
        (correctedSupportQuotientDiagram T A C θ η).map_refl]
      rfl
    map_comp {s t u} hst htu := by
      apply LinearMap.ext
      intro q
      obtain ⟨x, rfl⟩ := (cutCoordinateQuotientEquiv T A C θ η s).surjective q
      simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply]
      rw [← cutCoordinateQuotientEquiv_map T A C θ η hst,
        ← cutCoordinateQuotientEquiv_map T A C θ η htu,
        ← cutCoordinateQuotientEquiv_map T A C θ η (hst.trans htu),
        CutComplex.Diagram.map_map] }

/-- The bundled diagram uses the genuine quotient map on every class. -/
theorem bundledSupportQuotientDiagram_map
    (θ η : Set (Equiv.Perm (Fin n))) {s t : Finset (Fin (n - 1))} (h : s ⊆ t) :
    letI := T.topology
    (bundledSupportQuotientDiagram T A C θ η).map h =
      (Support.cutSupportQuotientMap T A C
        (B := shape s) (D := shape t) (by simpa using h) θ η).hom.toLinearMap := rfl

/-- The typed coordinate quotient equivalences are natural for actual cut maps. -/
def bundledSupportQuotientDiagramEquivalence
    (θ η : Set (Equiv.Perm (Fin n))) :
    CutComplex.Diagram.Equivalence (correctedSupportQuotientDiagram T A C θ η)
      (bundledSupportQuotientDiagram T A C θ η) where
  obj := cutCoordinateQuotientEquiv T A C θ η
  natural h x := cutCoordinateQuotientEquiv_map T A C θ η h x

/-- The homogeneous comparison with the actual bundled support quotients. -/
def bundledSupportQuotientDegreeEquiv
    (θ η : Set (Equiv.Perm (Fin n))) (k : ℕ) :
    (correctedSupportQuotientDiagram T A C θ η).Degree k ≃ₗ[ℂ]
      (bundledSupportQuotientDiagram T A C θ η).Degree k :=
  (bundledSupportQuotientDiagramEquivalence T A C θ η).degreeEquiv k

theorem bundledSupportQuotientDegreeEquiv_apply
    (θ η : Set (Equiv.Perm (Fin n))) (k : ℕ)
    (x : (correctedSupportQuotientDiagram T A C θ η).Degree k)
    (s : {s : Finset (Fin (n - 1)) // s.card = k}) :
    bundledSupportQuotientDegreeEquiv T A C θ η k x s =
      cutCoordinateQuotientEquiv T A C θ η s.1 (x s) := rfl

/-- Summing actual quotient cut maps retains the original exterior signs. -/
theorem bundledSupportQuotientDegreeEquiv_differential
    (θ η : Set (Equiv.Perm (Fin n))) (k : ℕ)
    (x : (correctedSupportQuotientDiagram T A C θ η).Degree k) :
    bundledSupportQuotientDegreeEquiv T A C θ η (k + 1)
        ((correctedSupportQuotientDiagram T A C θ η).degreeDifferential k x) =
      (bundledSupportQuotientDiagram T A C θ η).degreeDifferential k
        (bundledSupportQuotientDegreeEquiv T A C θ η k x) :=
  (bundledSupportQuotientDiagramEquivalence T A C θ η).degreeEquiv_differential k x

theorem bundledSupportQuotient_injective_iff
    (θ η : Set (Equiv.Perm (Fin n))) (k : ℕ) :
    Function.Injective
        ((correctedSupportQuotientDiagram T A C θ η).degreeDifferential k) ↔
      Function.Injective
        ((bundledSupportQuotientDiagram T A C θ η).degreeDifferential k) :=
  (bundledSupportQuotientDiagramEquivalence T A C θ η).degreeDifferential_injective_iff k

theorem bundledSupportQuotient_exact_iff
    (θ η : Set (Equiv.Perm (Fin n))) (k : ℕ) :
    LinearMap.range
        ((correctedSupportQuotientDiagram T A C θ η).degreeDifferential k) =
      LinearMap.ker
        ((correctedSupportQuotientDiagram T A C θ η).degreeDifferential (k + 1)) ↔
    LinearMap.range
        ((bundledSupportQuotientDiagram T A C θ η).degreeDifferential k) =
      LinearMap.ker
        ((bundledSupportQuotientDiagram T A C θ η).degreeDifferential (k + 1)) :=
  (bundledSupportQuotientDiagramEquivalence T A C θ η).degreeDifferential_exact_iff k

/-- The genuine associated grade compares directly with the bundled diagram. -/
def correctedBundledGradedEquiv
    (θ : ℕ → Set (Equiv.Perm (Fin n))) (i k : ℕ) :
    FiniteFiltered.Graded (correctedDegreeFiltration T A C θ k) i ≃ₗ[ℂ]
      (bundledSupportQuotientDiagram T A C (θ i) (θ (i + 1))).Degree k :=
  (correctedGradedEquiv T A C θ i k).trans
    (bundledSupportQuotientDegreeEquiv T A C (θ i) (θ (i + 1)) k)

/-- The associated-grade differential is the sum of the genuine quotient maps
with the original signed cut coefficients. -/
theorem correctedBundledGradedEquiv_differential
    (θ : ℕ → Set (Equiv.Perm (Fin n))) (i k : ℕ)
    (x : FiniteFiltered.Graded (correctedDegreeFiltration T A C θ k) i) :
    correctedBundledGradedEquiv T A C θ i (k + 1)
        (FiniteFiltered.gradedMap
          ((jacquetDiagram T C A.obj.ρ).degreeDifferential k)
          (correctedDegreeFiltration T A C θ k)
          (correctedDegreeFiltration T A C θ (k + 1))
          (degreeDifferential_preserves_correctedDegreeFiltration T A C θ k) i x) =
      (bundledSupportQuotientDiagram T A C (θ i) (θ (i + 1))).degreeDifferential k
        (correctedBundledGradedEquiv T A C θ i k x) := by
  simp only [correctedBundledGradedEquiv, LinearEquiv.trans_apply,
    correctedGradedEquiv_differential, bundledSupportQuotientDegreeEquiv_differential]

/-- Bundled graded injectivity lifts through the actual support filtration. -/
theorem degreeDifferential_injective_of_bundledGraded
    (θ : ℕ → Set (Equiv.Perm (Fin n))) (hzero : θ 0 = ∅)
    (m : ℕ) (htop : θ m = Set.univ) (k : ℕ)
    (hinj : ∀ i < m, Function.Injective
      ((bundledSupportQuotientDiagram T A C (θ i) (θ (i + 1))).degreeDifferential k)) :
    Function.Injective ((jacquetDiagram T C A.obj.ρ).degreeDifferential k) :=
  degreeDifferential_injective_of_correctedGraded T A C θ hzero m htop k
    (fun i hi => (bundledSupportQuotient_injective_iff T A C _ _ k).mpr (hinj i hi))

/-- Bundled graded exactness lifts through the actual support filtration. -/
theorem degreeDifferential_exact_of_bundledGraded
    (θ : ℕ → Set (Equiv.Perm (Fin n))) (hmono : Monotone θ) (hzero : θ 0 = ∅)
    (m : ℕ) (htop : θ m = Set.univ) (k : ℕ)
    (hex : ∀ i < m,
      LinearMap.range
        ((bundledSupportQuotientDiagram T A C (θ i) (θ (i + 1))).degreeDifferential k) =
      LinearMap.ker
        ((bundledSupportQuotientDiagram T A C (θ i) (θ (i + 1))).degreeDifferential (k + 1))) :
    LinearMap.range ((jacquetDiagram T C A.obj.ρ).degreeDifferential k) =
      LinearMap.ker ((jacquetDiagram T C A.obj.ρ).degreeDifferential (k + 1)) :=
  degreeDifferential_exact_of_correctedGraded T A C θ hmono hzero m htop k
    (fun i hi => (bundledSupportQuotient_exact_iff T A C _ _ k).mpr (hex i hi))

end Langlands.Aubert.ActualCutComplex
