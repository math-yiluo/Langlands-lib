import Langlands.Global.ProjectiveAffineChart
import Langlands.AlgebraicGeometry.ProjectiveSpace.PointComparison
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Perfect

/-! # Dense standard affine charts of actual projective point spaces -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

@[reducible]
local instance projectiveChartAlgebraStructure (R : Type u) [CommRing R]
    (n : ℕ) (j : Fin (n + 1)) : Algebra R (projectiveChartAlgebra R n j) :=
  _root_.AlgebraicGeometry.ProjSpace.algebraAway R n j

/-- Actual relative projective points with selected homogeneous coordinate one. -/
def projectiveAffinePoint (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (n : ℕ) (j : Fin (n + 1)) (a : {i : Fin (n + 1) // i ≠ j} → A) :
    RingPoint R (projectivePointScheme R n) A :=
  ringTestMap R (MvPolynomial.aeval a) ≫ projectiveAffineChart R n j

theorem projectiveAffinePoint_changeRing (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (n : ℕ) (j : Fin (n + 1)) (f : A →ₐ[R] B)
    (a : {i : Fin (n + 1) // i ≠ j} → A) :
    (projectiveAffinePoint R A n j a).changeRing f =
      projectiveAffinePoint R B n j (f ∘ a) := by
  change ringTestMap R f ≫
    (ringTestMap R (MvPolynomial.aeval a) ≫ projectiveAffineChart R n j) =
    ringTestMap R (MvPolynomial.aeval (f ∘ a)) ≫ projectiveAffineChart R n j
  rw [← Category.assoc, ← ringTestMap_comp]
  congr 1
  apply congrArg (ringTestMap R)
  apply MvPolynomial.algHom_ext
  intro i
  simp

theorem isOpenEmbedding_projectiveAffinePoint (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLocalRing A] [IsOpenUnits A]
    (n : ℕ) (j : Fin (n + 1)) :
    @IsOpenEmbedding ({i : Fin (n + 1) // i ≠ j} → A)
      (RingPoint R (projectivePointScheme R n) A) inferInstance
      (schemePointTopology R (projectivePointScheme R n) A)
      (projectiveAffinePoint R A n j) := by
  let P := MvPolynomial {i : Fin (n + 1) // i ≠ j} R
  let e := (spectrumAlgebraPointHomeomorph R A P).trans
    (AlgPoint.polynomialPointHomeomorph (R := R) (S := A) {i : Fin (n + 1) // i ≠ j})
  let e0 : RingPoint R (ringTest R P) A ≃ ({i : Fin (n + 1) // i ≠ j} → A) :=
    e.toEquiv
  have he : @IsHomeomorph (RingPoint R (ringTest R P) A)
      ({i : Fin (n + 1) // i ≠ j} → A)
      (schemePointTopology R (ringTest R P) A) inferInstance e0 := by
    rw [schemePointTopology_eq_affine]
    exact e.isHomeomorph
  let := schemePointTopology R (ringTest R P) A
  let := schemePointTopology R (projectivePointScheme R n) A
  let h : RingPoint R (ringTest R P) A ≃ₜ ({i : Fin (n + 1) // i ≠ j} → A) :=
    { toEquiv := e0
      continuous_toFun := he.continuous
      continuous_invFun := e0.continuous_symm_iff.2 he.isOpenMap }
  exact (isOpenEmbedding_schemePointMap R A (projectiveAffineChart R n j)).comp
    h.symm.isOpenEmbedding

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every field-valued relative projective point belongs to a standard affine chart. -/
theorem exists_projectiveAffinePoint (R A : Type u)
    [CommRing R] [Field A] [Algebra R A] (n : ℕ)
    (p : RingPoint R (projectivePointScheme R n) A) :
    ∃ (j : Fin (n + 1)) (a : {i : Fin (n + 1) // i ≠ j} → A),
      projectiveAffinePoint R A n j a = p := by
  let C := Langlands.AlgebraicGeometry.ProjectiveSpace.affineOpenCover R n
  have hcov : p.left (IsLocalRing.closedPoint A) ∈
      (⨆ j, Langlands.AlgebraicGeometry.projectiveSpaceCoordinateOpen R n j) := by
    rw [Langlands.AlgebraicGeometry.iSup_projectiveSpaceCoordinateOpen]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  have htop : p.left ⁻¹ᵁ
      Langlands.AlgebraicGeometry.projectiveSpaceCoordinateOpen R n j = ⊤ :=
    (IsLocalRing.closedPoint_mem_iff _).mp hj
  have hrange : Set.range p.left ⊆ Set.range (C.openCover.f j) := by
    rintro x ⟨y, rfl⟩
    change p.left y ∈ (C.openCover.f j).opensRange
    rw [Langlands.AlgebraicGeometry.ProjectiveSpace.affineOpenCover_opensRange]
    have hy : y ∈ p.left ⁻¹ᵁ
        Langlands.AlgebraicGeometry.projectiveSpaceCoordinateOpen R n j := by
      rw [htop]
      trivial
    exact hy
  let χ := IsOpenImmersion.lift (C.openCover.f j) p.left hrange
  have hχ : χ ≫ C.openCover.f j = p.left := IsOpenImmersion.lift_fac _ _ _
  have hbase : χ ≫ (ringTest R (projectiveChartAlgebra R n j)).hom =
      (ringTest R A).hom := by
    calc
      _ = χ ≫ (C.openCover.f j ≫ (projectivePointScheme R n).hom) :=
        congrArg (fun g => χ ≫ g)
          (Langlands.AlgebraicGeometry.ProjectiveSpace.affineOpenCover_comp_toSpec R n j).symm
      _ = p.left ≫ (projectivePointScheme R n).hom := by rw [← Category.assoc, hχ]
      _ = _ := p.w
  let q : RingPoint R (ringTest R (projectiveChartAlgebra R n j)) A :=
    Over.homMk χ hbase
  let φ := (spectrumAlgebraPointEquiv R A (projectiveChartAlgebra R n j) q).toAlgHom
  let ψ := φ.comp (P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace.awayChartEquiv (S := R) n j).toAlgHom
  let a (i : {i : Fin (n + 1) // i ≠ j}) := ψ (MvPolynomial.X i)
  have ha : MvPolynomial.aeval a = ψ := by
    apply MvPolynomial.algHom_ext
    intro i
    exact MvPolynomial.aeval_X a i
  have hq : ringTestMap R φ = q := by
    exact (spectrumAlgebraPointEquiv R A (projectiveChartAlgebra R n j)).symm_apply_apply q
  refine ⟨j, a, ?_⟩
  apply RingPoint.ext
  change (ringTestMap R (MvPolynomial.aeval a) ≫
    ringTestMap R (P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace.awayChartEquiv (S := R) n j).symm.toAlgHom).left ≫
      C.openCover.f j = p.left
  rw [← ringTestMap_comp, ha]
  have hφ : ψ.comp (P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace.awayChartEquiv (S := R) n j).symm.toAlgHom = φ := by
    ext x
    exact congrArg φ ((P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace.awayChartEquiv (S := R) n j).apply_symm_apply x)
  rw [hφ, hq]
  exact hχ

/-- The homogeneous coordinates of a standard affine-chart point. -/
def projectiveAffineCoordinates {A : Type u} [One A] (n : ℕ) (j : Fin (n + 1))
    (a : {i : Fin (n + 1) // i ≠ j} → A) (i : Fin (n + 1)) : A :=
  if h : i = j then 1 else a ⟨i, h⟩

@[simp]
theorem projectiveAffineCoordinates_self {A : Type u} [One A]
    (n : ℕ) (j : Fin (n + 1)) (a : {i : Fin (n + 1) // i ≠ j} → A) :
    projectiveAffineCoordinates n j a j = 1 := by
  simp [projectiveAffineCoordinates]

/-- Evaluation on the homogeneous chart, retaining the original base algebra. -/
def projectiveAffineChartEvaluation (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) (j : Fin (n + 1))
    (a : {i : Fin (n + 1) // i ≠ j} → A) :
    projectiveChartAlgebra R n j →ₐ[R] A :=
  (MvPolynomial.aeval a).comp (P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace.awayChartEquiv (S := R) n j).symm.toAlgHom

@[simp]
theorem projectiveAffineChartEvaluation_ratio (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) (j i : Fin (n + 1))
    (a : {i : Fin (n + 1) // i ≠ j} → A) :
    projectiveAffineChartEvaluation R A n j a
      (_root_.AlgebraicGeometry.ProjSpace.ratio R n j i) =
      projectiveAffineCoordinates n j a i := by
  by_cases h : i = j
  · subst i
    rw [_root_.AlgebraicGeometry.ProjSpace.ratio_self, projectiveAffineCoordinates_self]
    exact map_one (projectiveAffineChartEvaluation R A n j a)
  · rw [← P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace.awayChartEquiv_X (S := R) n j ⟨i, h⟩]
    simp only [projectiveAffineCoordinates, dite_eq_right h]
    change MvPolynomial.aeval a
      ((P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace.awayChartEquiv (S := R) n j).symm
        (P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace.awayChartEquiv (S := R) n j (MvPolynomial.X ⟨i, h⟩))) = _
    rw [AlgEquiv.symm_apply_apply, MvPolynomial.aeval_X]

theorem projectiveAffinePoint_left (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) (j : Fin (n + 1))
    (a : {i : Fin (n + 1) // i ≠ j} → A) :
    (projectiveAffinePoint R A n j a).left =
      Spec.map (CommRingCat.ofHom (projectiveAffineChartEvaluation R A n j a).toRingHom) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)
          (_root_.AlgebraicGeometry.ProjSpace.X_mem_one R n j) Nat.one_pos := by
  unfold projectiveAffinePoint projectiveAffineChart
  rw [← Category.assoc, ← ringTestMap_comp]
  rfl

/-- Switching charts divides all homogeneous coordinates by the new coordinate. -/
theorem projectiveAffinePoint_changeChart (R A : Type u)
    [CommRing R] [Field A] [Algebra R A] (n : ℕ) (i j : Fin (n + 1))
    (a : {k : Fin (n + 1) // k ≠ i} → A)
    (hj : projectiveAffineCoordinates n i a j ≠ 0) :
    projectiveAffinePoint R A n i a =
      projectiveAffinePoint R A n j
        (fun k => projectiveAffineCoordinates n i a k.val /
          projectiveAffineCoordinates n i a j) := by
  apply RingPoint.ext
  rw [projectiveAffinePoint_left, projectiveAffinePoint_left]
  have hi : IsUnit (projectiveAffineCoordinates n i a i) := by simp
  have hψi (k : Fin (n + 1)) :
      projectiveAffineChartEvaluation R A n i a
        (_root_.AlgebraicGeometry.ProjSpace.ratio R n i k) *
          projectiveAffineCoordinates n i a i = projectiveAffineCoordinates n i a k := by
    rw [projectiveAffineChartEvaluation_ratio, projectiveAffineCoordinates_self, mul_one]
  have hψj (k : Fin (n + 1)) :
      projectiveAffineChartEvaluation R A n j
        (fun k => projectiveAffineCoordinates n i a k.val /
          projectiveAffineCoordinates n i a j)
        (_root_.AlgebraicGeometry.ProjSpace.ratio R n j k) *
          projectiveAffineCoordinates n i a j = projectiveAffineCoordinates n i a k := by
    rw [projectiveAffineChartEvaluation_ratio]
    by_cases h : k = j
    · subst k
      simp
    · simp only [projectiveAffineCoordinates, dite_eq_right h]
      exact div_mul_cancel₀ _ hj
  exact _root_.AlgebraicGeometry.ProjSpace.specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq
    R n A (projectiveAffineCoordinates n i a) i j hi (isUnit_iff_ne_zero.mpr hj)
    (projectiveAffineChartEvaluation R A n i a)
    (projectiveAffineChartEvaluation R A n j
      (fun k => projectiveAffineCoordinates n i a k.val /
        projectiveAffineCoordinates n i a j)) hψi hψj

theorem denseRange_projectiveAffinePoint (R A : Type u)
    [CommRing R] [Field A] [Algebra R A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsOpenUnits A] [PerfectSpace A]
    (n : ℕ) (j : Fin (n + 1)) :
    letI := schemePointTopology R (projectivePointScheme R n) A
    DenseRange (projectiveAffinePoint R A n j) := by
  let := schemePointTopology R (projectivePointScheme R n) A
  intro p
  obtain ⟨i, a, rfl⟩ := exists_projectiveAffinePoint R A n p
  let D : Set ({k : Fin (n + 1) // k ≠ i} → A) :=
    Set.pi Set.univ (fun _ => ({0}ᶜ : Set A))
  have hD : Dense D := dense_pi Set.univ (fun _ _ => dense_compl_singleton (0 : A))
  have hc : Continuous (projectiveAffinePoint R A n i) :=
    (isOpenEmbedding_projectiveAffinePoint R A n i).continuous
  have hm : projectiveAffinePoint R A n i '' D ⊆
      Set.range (projectiveAffinePoint R A n j) := by
    rintro _ ⟨b, hb, rfl⟩
    have hj : projectiveAffineCoordinates n i b j ≠ 0 := by
      by_cases h : j = i
      · subst j
        simp
      · simpa only [projectiveAffineCoordinates, dite_eq_right h,
          Set.mem_compl_iff, Set.mem_singleton_iff] using hb ⟨j, h⟩ (Set.mem_univ _)
    exact ⟨_, (projectiveAffinePoint_changeChart R A n i j b hj).symm⟩
  exact closure_mono hm (mem_closure_image hc.continuousAt (hD a))

end Langlands.Global
