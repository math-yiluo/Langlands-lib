import Langlands.AlgebraicGeometry.AlgebraicSpace.AnalyticAffineNormalization
import Mathlib.RingTheory.RingHom.StandardSmooth

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Set Filter Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped ContDiff Manifold

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K]

/-- Every smooth pure-dimensional scheme gives a space in the same family. -/
theorem isSmoothPureDimensional_scheme (n : ℕ)
    (U : Over (Spec (CommRingCat.of K))) (hU : SmoothOfRelativeDimension n U.hom) :
    IsSmoothPureDimensional K n ((schemeToSpace _).obj U) := by
  let := hU
  let : Smooth U.hom := SmoothOfRelativeDimension.smooth n U.hom
  exact ⟨isLocallySeparatedLocallyFiniteType_schemeToSpace U,
    HasAtlasProperty.of_scheme U hU⟩

/-- Polynomial affine space has its actual polynomial relative dimension. -/
theorem smoothOfRelativeDimension_affineSpace (n : ℕ) :
    SmoothOfRelativeDimension n (affineSpaceOver K n).hom := by
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)).2
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := n)).2 inferInstance

/-- Affine space is an object on which the normalization clause applies. -/
theorem isSmoothPureDimensional_affineSpace (n : ℕ) :
    IsSmoothPureDimensional K n ((schemeToSpace _).obj (affineSpaceOver K n)) :=
  isSmoothPureDimensional_scheme n _ (smoothOfRelativeDimension_affineSpace n)

namespace AnalyticPointStructure

/-- Analyticity of the identity from one family's structure to another's on one object. -/
def AnalyticIdentity (σ τ : AnalyticPointStructure K) (n : ℕ)
    (X : AlgebraicSpace (Spec (CommRingCat.of K))) (hX : IsSmoothPureDimensional K n X) : Prop :=
  @ContMDiff K _ (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) (RingPoints K X K)
    (etaleChartTopology K X) (σ.chartedSpace n X hX) (Fin n → K) _ _ (Fin n → K) _
    𝓘(K, Fin n → K) (RingPoints K X K) (etaleChartTopology K X) (τ.chartedSpace n X hX) ω id

/-- Normalization forces the identity to be analytic on affine space. -/
theorem analyticIdentity_affineSpace (σ τ : AnalyticPointStructure K)
    (hσ : σ.IsAdmissible) (hτ : τ.IsAdmissible) (n : ℕ) :
    σ.AnalyticIdentity τ n _ (isSmoothPureDimensional_affineSpace n) := by
  let X := (schemeToSpace _).obj (affineSpaceOver K n)
  let hX := isSmoothPureDimensional_affineSpace (K := K) n
  let := etaleChartTopology K X
  obtain ⟨⟨Φ, hΦan, hΦinv⟩, hΦ⟩ := hσ.2.2.2 n hX
  obtain ⟨⟨Ψ, hΨan, hΨinv⟩, hΨ⟩ := hτ.2.2.2 n hX
  have heq : (Ψ.symm ∘ Φ) = id := by
    funext x
    apply Ψ.injective
    change Ψ (Ψ.symm (Φ x)) = Ψ x
    rw [Ψ.apply_symm_apply]
    exact (hΦ x).trans (hΨ x).symm
  change @ContMDiff K _ (Fin n → K) _ _ (Fin n → K) _ _ _ _ (σ.chartedSpace n X hX)
    (Fin n → K) _ _ (Fin n → K) _ _ _ _ (τ.chartedSpace n X hX) ω id
  rw [← heq]
  exact @ContMDiff.comp K _ (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) _ _
    (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) _ _
    (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) _ _
    (σ.chartedSpace n X hX) (inferInstance) (τ.chartedSpace n X hX) _ ω _
    (hΨinv) (hΦan)

/-- Comparison pulls back through an etale map, using its local inverse in the target family. -/
theorem analyticIdentity_of_etale_to (σ τ : AnalyticPointStructure K)
    (hσ : σ.IsAdmissible) (hτ : τ.IsAdmissible) (n : ℕ)
    (X Y : AlgebraicSpace (Spec (CommRingCat.of K)))
    (hX : IsSmoothPureDimensional K n X) (hY : IsSmoothPureDimensional K n Y)
    (f : X ⟶ Y) (hf : IsEtaleMorphism f) (h : σ.AnalyticIdentity τ n Y hY) :
    σ.AnalyticIdentity τ n X hX := by
  let := etaleChartTopology K X
  let := etaleChartTopology K Y
  change @ContMDiff K _ (Fin n → K) _ _ (Fin n → K) _ _ _ _ (σ.chartedSpace n X hX)
    (Fin n → K) _ _ (Fin n → K) _ _ _ _ (τ.chartedSpace n X hX) ω id
  intro x
  have hcomp : @ContMDiffAt K _ (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) _ _
      (σ.chartedSpace n X hX) (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) _ _
      (τ.chartedSpace n Y hY) ω (RingPoints.map (A := K) f) x := by
    exact @ContMDiffAt.comp K _ (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) _ _
      (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) _ _
      (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) _ _
      (σ.chartedSpace n X hX) (σ.chartedSpace n Y hY) (τ.chartedSpace n Y hY) _ ω _ x
      (h (RingPoints.map (A := K) f x)) (hσ.2.1 n n X Y hX hY f x)
  have hi := hτ.2.2.1 n X Y hX hY f hf x
  let := τ.chartedSpace n X hX
  let := τ.chartedSpace n Y hY
  have han := @ContMDiffAt.comp K _ (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) _ _
    (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) _ _
    (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) _ _
    (σ.chartedSpace n X hX) (τ.chartedSpace n Y hY) (τ.chartedSpace n X hX) _ ω _ x
    (hi.localInverse_contMDiffAt) (hcomp)
  exact @ContMDiffAt.congr_of_eventuallyEq K _
    (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) _ _ (σ.chartedSpace n X hX)
    (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) _ _ (τ.chartedSpace n X hX)
    _ _ x ω han hi.localInverse_eventuallyEq_left.symm

/-- Comparison descends at the image of an etale source on which the families agree. -/
theorem analyticIdentityAt_of_etale_from (σ τ : AnalyticPointStructure K)
    (hσ : σ.IsAdmissible) (hτ : τ.IsAdmissible) (n : ℕ)
    (U X : AlgebraicSpace (Spec (CommRingCat.of K)))
    (hU : IsSmoothPureDimensional K n U) (hX : IsSmoothPureDimensional K n X)
    (f : U ⟶ X) (hf : IsEtaleMorphism f) (h : σ.AnalyticIdentity τ n U hU)
    (u : RingPoints K U K) :
    @ContMDiffAt K _ (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) (RingPoints K X K)
      (etaleChartTopology K X) (σ.chartedSpace n X hX) (Fin n → K) _ _ (Fin n → K) _
      𝓘(K, Fin n → K) (RingPoints K X K) (etaleChartTopology K X) (τ.chartedSpace n X hX) ω
      id (RingPoints.map (A := K) f u) := by
  let := etaleChartTopology K U
  let := etaleChartTopology K X
  have hcomp : @ContMDiffAt K _ (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) _ _
      (σ.chartedSpace n U hU) (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) _ _
      (τ.chartedSpace n X hX) ω (RingPoints.map (A := K) f) u := by
    exact @ContMDiffAt.comp K _ (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) _ _
      (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) _ _
      (Fin n → K) _ _ (Fin n → K) _ 𝓘(K, Fin n → K) _ _
      (σ.chartedSpace n U hU) (τ.chartedSpace n U hU) (τ.chartedSpace n X hX) _ ω _ u
      (hτ.2.1 n n U X hU hX f u) (h u)
  exact @Langlands.Geometry.Manifold.contMDiffAt_of_comp_localDiffeomorph K _
    (Fin n → K) (Fin n → K) (Fin n → K) _ _ _ _ _ _
    (Fin n → K) (Fin n → K) (Fin n → K) _ _ _
    𝓘(K, Fin n → K) 𝓘(K, Fin n → K) 𝓘(K, Fin n → K)
    _ _ _ _ (σ.chartedSpace n X hX) _ (τ.chartedSpace n X hX) _ (σ.chartedSpace n U hU)
    ω (RingPoints.map (A := K) f) id u (hσ.2.2.1 n U X hU hX f hf u) hcomp

/-- The two families agree on every affine standard-smooth scheme. -/
theorem analyticIdentity_standardSmooth (σ τ : AnalyticPointStructure K)
    (hσ : σ.IsAdmissible) (hτ : τ.IsAdmissible) (n : ℕ)
    (U : Over (Spec (CommRingCat.of K))) [IsAffine U.left]
    [Algebra.IsStandardSmoothOfRelativeDimension n K (AffineCoordinateRing K U)]
    (hU : IsSmoothPureDimensional K n ((schemeToSpace _).obj U)) :
    σ.AnalyticIdentity τ n _ hU := by
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n K
      (AffineCoordinateRing K U)
  let j : U ⟶ affineSpaceOver K n := (affineSchemeOverIso K U).hom ≫ ringTestMap K g
  have hj : Etale j.left := by
    let : Etale (ringTestMap K g).left :=
      (HasRingHomProperty.Spec_iff (P := @Etale)).2 hg
    dsimp only [j, Over.comp_left]
    infer_instance
  have hf : IsEtaleMorphism ((schemeToSpace _).map j) :=
    fun _ _ hφ => hφ.comp (isEtale_map j hj)
  exact analyticIdentity_of_etale_to σ τ hσ hτ n _ _ hU
    (isSmoothPureDimensional_affineSpace n) ((schemeToSpace _).map j) hf
    (analyticIdentity_affineSpace σ τ hσ hτ n)

/-- The identity is analytic on every space in the family. -/
theorem analyticIdentity (σ τ : AnalyticPointStructure K)
    (hσ : σ.IsAdmissible) (hτ : τ.IsAdmissible) (n : ℕ)
    (X : AlgebraicSpace (Spec (CommRingCat.of K))) (hX : IsSmoothPureDimensional K n X) :
    σ.AnalyticIdentity τ n X hX := by
  let := etaleChartTopology K X
  intro x
  let c := smoothPureDimensionalAffineChart K n X hX x
  let := c.isAffine
  let := c.smooth
  obtain ⟨f, hf, hss⟩ := PointManifold.General.exists_standardSmooth_basicOpen K c.scheme n
    (c.point.left (IsLocalRing.closedPoint K))
  let D := c.scheme.left.basicOpen (U := ⊤) f
  let : IsAffine D := (isAffineOpen_top c.scheme.left).basicOpen f
  let V := openOver K c.scheme D
  let i : V ⟶ c.scheme := openOverι K c.scheme D
  have hV : SmoothOfRelativeDimension n V.hom := by
    change SmoothOfRelativeDimension n (D.ι ≫ c.scheme.hom)
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (D.ι ≫ c.scheme.hom))
  let hVs := isSmoothPureDimensional_scheme n V hV
  let := hss
  have hident := analyticIdentity_standardSmooth σ τ hσ hτ n V hVs
  let v : RingPoint K V K := openPointLift K c.scheme K D c.point
    ((range_subset_open_iff_closedPoint K c.scheme K D c.point).2 hf)
  let F : (schemeToSpace _).obj V ⟶ X := (schemeToSpace _).map i ≫ c.hom
  have hiEt : Etale i.left := by
    change Etale D.ι
    infer_instance
  have hF : IsEtaleMorphism F := by
    intro T φ hφ
    exact (hφ.comp (isEtale_map i hiEt)).comp c.isEtale
  have hv : RingPoints.map F ((schemeRingPointsEquiv K V K).symm v) = x := by
    rw [RingPoints.map_comp]
    have hi : RingPoints.map ((schemeToSpace _).map i)
        ((schemeRingPointsEquiv K V K).symm v) =
        (schemeRingPointsEquiv K c.scheme K).symm c.point := by
      apply (schemeRingPointsEquiv K c.scheme K).injective
      change openPointMap K c.scheme K D v = c.point
      exact openPointMap_lift K c.scheme K D c.point _
    rw [hi]
    exact c.map_point
  have h := analyticIdentityAt_of_etale_from σ τ hσ hτ n _ X hVs hX F hF hident
    ((schemeRingPointsEquiv K V K).symm v)
  rw [hv] at h
  exact h

/-- Any two admissible families are analytically equivalent. -/
theorem equivalent_of_isAdmissible (σ τ : AnalyticPointStructure K)
    (hσ : σ.IsAdmissible) (hτ : τ.IsAdmissible) : σ.Equivalent τ := by
  intro n X hX
  exact ⟨analyticIdentity σ τ hσ hτ n X hX, analyticIdentity τ σ hτ hσ n X hX⟩

end AnalyticPointStructure

end Langlands.AlgebraicGeometry.AlgebraicSpace
