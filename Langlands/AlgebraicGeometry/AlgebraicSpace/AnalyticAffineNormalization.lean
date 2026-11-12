import Langlands.AlgebraicGeometry.AlgebraicSpace.AnalyticPointFunctoriality
import Langlands.AlgebraicGeometry.PointTopology.AffineProofs
import Langlands.AlgebraicGeometry.PointManifold.PolynomialCalculus

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Set Filter Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped ContDiff Manifold

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]

/-- The canonical analytic structure agrees with the regular affine-scheme structure. -/
def affineSchemePointDiffeomorph
    (n : ℕ) (U : Over (Spec (CommRingCat.of K))) [IsAffine U.left]
    (hU : SmoothOfRelativeDimension n U.hom)
    (hX : IsSmoothPureDimensional K n ((schemeToSpace _).obj U)) :
    letI := PointManifold.Analytic.smoothAffineChartedSpace K U n hU
    letI := etaleChartTopology K ((schemeToSpace _).obj U)
    letI := smoothSpaceChartedSpace K n ((schemeToSpace _).obj U) hX
    Diffeomorph 𝓘(K, Fin n → K) 𝓘(K, Fin n → K)
      (RingPoint K U K) (RingPoints K ((schemeToSpace _).obj U) K) ω := by
  let := PointManifold.Analytic.smoothAffineChartedSpace K U n hU
  let := etaleChartTopology K ((schemeToSpace _).obj U)
  let := smoothSpaceChartedSpace K n ((schemeToSpace _).obj U) hX
  have hf : IsLocalDiffeomorph 𝓘(K, Fin n → K) 𝓘(K, Fin n → K) ω
      (schemeRingPointsEquiv K U K).symm := by
    intro u
    let c : SmoothPureDimensionalAffineChart K n ((schemeToSpace _).obj U)
        ((schemeRingPointsEquiv K U K).symm u) := {
      scheme := U
      isAffine := inferInstance
      hom := 𝟙 _
      isEtale := by
        change IsEtale (𝟙 ((schemeYoneda _).obj U))
        simpa using isEtale_map (𝟙 U) (by change Etale (𝟙 U.left); infer_instance)
      smooth := hU
      point := u
      map_point := rfl }
    exact c.isLocalDiffeomorphAt_pointMap hX
  exact hf.diffeomorphOfBijective (schemeRingPointsEquiv K U K).symm.bijective

/-- The affine scheme comparison has the specified actual point map. -/
theorem affineSchemePointDiffeomorph_apply
    (n : ℕ) (U : Over (Spec (CommRingCat.of K))) [IsAffine U.left]
    (hU : SmoothOfRelativeDimension n U.hom)
    (hX : IsSmoothPureDimensional K n ((schemeToSpace _).obj U))
    (u : RingPoint K U K) :
    affineSchemePointDiffeomorph n U hU hX u = (schemeRingPointsEquiv K U K).symm u := rfl

/-- Polynomial coordinates as a homeomorphism on actual affine scheme points. -/
def affinePolynomialPointHomeomorph (n : ℕ) :
    RingPoint K (affineSpaceOver K n) K ≃ₜ (Fin n → K) :=
  ((affineSchemePointHomeomorph K (affineSpaceOver K n) K).trans
    (AlgPoint.congr (spectrumCoordinateAlgEquiv K (MvPolynomial (Fin n) K)))).trans
      (AlgPoint.polynomialPointHomeomorph (Fin n))

omit [CompleteSpace K] in
/-- Coordinate functions are evaluations of the corresponding actual global sections. -/
theorem affinePolynomialPointHomeomorph_apply (n : ℕ)
    (p : RingPoint K (affineSpaceOver K n) K) (i : Fin n) :
    affinePolynomialPointHomeomorph n p i =
      PointManifold.Analytic.regularEvaluation p
        ((spectrumCoordinateAlgEquiv K (MvPolynomial (Fin n) K)).symm (MvPolynomial.X i)) := rfl

omit [CompleteSpace K] in
/-- Evaluations along the inverse coordinate map are polynomial evaluations. -/
theorem affinePolynomialPointHomeomorph_symm_evaluation (n : ℕ) (v : Fin n → K)
    (a : AffineCoordinateRing K (affineSpaceOver K n)) :
    PointManifold.Analytic.regularEvaluation ((affinePolynomialPointHomeomorph n).symm v) a =
      MvPolynomial.eval v (spectrumCoordinateAlgEquiv K (MvPolynomial (Fin n) K) a) := by
  change (affineSchemePointEquiv K (affineSpaceOver K n) K
    ((affineSchemePointEquiv K (affineSpaceOver K n) K).symm _)).toAlgHom a = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Actual affine scheme coordinates are a diffeomorphism for every regular analytic atlas. -/
def affinePolynomialPointDiffeomorph (n : ℕ)
    (A : PointManifold.Analytic.RegularAtlas K (affineSpaceOver K n) n) :
    letI := A.chartedSpace
    Diffeomorph 𝓘(K, Fin n → K) 𝓘(K, Fin n → K)
      (RingPoint K (affineSpaceOver K n) K) (Fin n → K) ω := by
  let := A.chartedSpace
  refine {
    toEquiv := (affinePolynomialPointHomeomorph n).toEquiv
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · apply contMDiff_pi_space.2
    intro i
    exact A.contMDiff_regularEvaluation
      ((spectrumCoordinateAlgEquiv K (MvPolynomial (Fin n) K)).symm (MvPolynomial.X i))
  · apply (A.contMDiff_iff_regularAnalytic 𝓘(K, Fin n → K) _).2
    intro a
    have h := PointManifold.contDiff_polynomial_eval
      (spectrumCoordinateAlgEquiv K (MvPolynomial (Fin n) K) a) ω
    apply contMDiff_iff_contDiff.mpr
    convert h using 1
    funext v
    exact affinePolynomialPointHomeomorph_symm_evaluation n v a

omit [CompleteSpace K] in
/-- The constructed coordinates are the original variable-value coordinates. -/
theorem affinePolynomialPointHomeomorph_eq_coordinates (n : ℕ)
    (p : RingPoint K (affineSpaceOver K n) K) :
    affinePolynomialPointHomeomorph n p =
      fun i => affineRingPointEquiv K (MvPolynomial (Fin n) K) K p (MvPolynomial.X i) := by
  funext i
  rw [affinePolynomialPointHomeomorph_apply]
  unfold PointManifold.Analytic.regularEvaluation
  rw [affineSchemePointEquiv_spectrum]
  change affineRingPointEquiv K (MvPolynomial (Fin n) K) K p
    ((spectrumCoordinateAlgEquiv K (MvPolynomial (Fin n) K))
      ((spectrumCoordinateAlgEquiv K (MvPolynomial (Fin n) K)).symm (MvPolynomial.X i))) = _
  rw [AlgEquiv.apply_symm_apply]

/-- The actual coordinate map on space points of affine space is an analytic diffeomorphism. -/
def affineSpaceCoordinateDiffeomorph (n : ℕ)
    (h : IsSmoothPureDimensional K n ((schemeToSpace _).obj (affineSpaceOver K n))) :
    letI := etaleChartTopology K ((schemeToSpace _).obj (affineSpaceOver K n))
    letI := smoothSpaceChartedSpace K n ((schemeToSpace _).obj (affineSpaceOver K n)) h
    Diffeomorph 𝓘(K, Fin n → K) 𝓘(K, Fin n → K)
      (RingPoints K ((schemeToSpace _).obj (affineSpaceOver K n)) K) (Fin n → K) ω := by
  let U := affineSpaceOver K n
  let := etaleChartTopology K ((schemeToSpace _).obj U)
  let := smoothSpaceChartedSpace K n ((schemeToSpace _).obj U) h
  have hid : IsEtale (𝟙 ((schemeYoneda _).obj U)) := by
    simpa using isEtale_map (𝟙 U) (by change Etale (𝟙 U.left); infer_instance)
  have hU : SmoothOfRelativeDimension n U.hom :=
    smoothRelativeDimension_of_isEtale n h.2 (𝟙 ((schemeYoneda _).obj U)) hid
  let := PointManifold.Analytic.smoothAffineChartedSpace K U n hU
  exact (affineSchemePointDiffeomorph n U hU h).symm.trans
    (affinePolynomialPointDiffeomorph n
      (PointManifold.Analytic.smoothAffineRegularAtlas K U n hU))

/-- The normalization diffeomorphism is exactly the target's coordinate function. -/
theorem affineSpaceCoordinateDiffeomorph_apply (n : ℕ)
    (h : IsSmoothPureDimensional K n ((schemeToSpace _).obj (affineSpaceOver K n)))
    (z : RingPoints K ((schemeToSpace _).obj (affineSpaceOver K n)) K) :
    affineSpaceCoordinateDiffeomorph n h z = affineSpaceCoordinates K n z := by
  let U := affineSpaceOver K n
  let := etaleChartTopology K ((schemeToSpace _).obj U)
  let := smoothSpaceChartedSpace K n ((schemeToSpace _).obj U) h
  have hid : IsEtale (𝟙 ((schemeYoneda _).obj U)) := by
    simpa using isEtale_map (𝟙 U) (by change Etale (𝟙 U.left); infer_instance)
  let hU : SmoothOfRelativeDimension n U.hom :=
    smoothRelativeDimension_of_isEtale n h.2 (𝟙 ((schemeYoneda _).obj U)) hid
  let := PointManifold.Analytic.smoothAffineChartedSpace K U n hU
  let D := affineSchemePointDiffeomorph n U hU h
  have hD : D.symm z = schemeRingPointsEquiv K U K z := by
    apply (schemeRingPointsEquiv K U K).symm.injective
    change D (D.symm z) = (schemeRingPointsEquiv K U K).symm (schemeRingPointsEquiv K U K z)
    rw [D.apply_symm_apply, Equiv.symm_apply_apply]
  change affinePolynomialPointHomeomorph n (D.symm z) = _
  rw [hD, affinePolynomialPointHomeomorph_eq_coordinates]
  rfl

/-- The canonical family has the prescribed affine-space normalization. -/
theorem canonicalAnalyticPointStructure_agreesWithAffineSpace (K : Type u)
    [NontriviallyNormedField K] [CompleteSpace K] :
    (canonicalAnalyticPointStructure K).AgreesWithAffineSpace :=
  fun n h => ⟨affineSpaceCoordinateDiffeomorph n h, affineSpaceCoordinateDiffeomorph_apply n h⟩

/-- The constructed family satisfies all admissibility conditions. -/
theorem canonicalAnalyticPointStructure_isAdmissible (K : Type u)
    [NontriviallyNormedField K] [CompleteSpace K] :
    (canonicalAnalyticPointStructure K).IsAdmissible :=
  ⟨canonicalAnalyticPointStructure_isAnalytic K, canonicalAnalyticPointStructure_isFunctorial K,
    canonicalAnalyticPointStructure_isEtaleLocalIso K,
    canonicalAnalyticPointStructure_agreesWithAffineSpace K⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
