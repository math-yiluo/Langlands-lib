import Langlands.Global.AdelicIntertwiningIntegrability
import Langlands.Global.AdelicSquareIntegrableInducedForms
import Langlands.Global.AdelicRootHyperplaneReduction

/-! # Absolute integrability of the scalar Iwasawa kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct Manifold ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global InfiniteAdelicGroupPoints Langlands.Geometry.Manifold

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {d : ℕ}
  (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)

private def constantInfiniteSlice (z : ℂ) : InfinitePlotSmoothFunctions F G :=
  ⟨fun _ => z, by
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    exact (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr contMDiff_const⟩

private def adelicEnvelopingAugmentation : AdelicEnvelopingAlgebra F G hsmooth →ₐ[ℂ] ℂ := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
    LieGroup.of_le (n := ∞) (by simp)
  let L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)
  exact UniversalEnvelopingAlgebra.lift ℂ (0 : L →ₗ⁅ℂ⁆ ℂ)

include hcalc in
private theorem plotSmoothEnvelopingAction_constant (a : AdelicEnvelopingAlgebra F G hsmooth) (z : ℂ) :
    plotSmoothEnvelopingAction F G hsmooth hcalc a (constantInfiniteSlice F G hsmooth z) =
      constantInfiniteSlice F G hsmooth (adelicEnvelopingAugmentation F G hsmooth a * z) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3) (InfiniteAdelicGroupPoints F G) :=
    LieGroup.of_le (n := ∞) (by simp)
  let L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)
  have hderiv (X : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) (z : ℂ) :
      plotSmoothDifferential F G hsmooth X (constantInfiniteSlice F G hsmooth z) = 0 := by
    apply Subtype.ext
    funext g
    rw [plotSmoothDifferential_apply]
    change mvfderiv 𝓘(ℝ, smoothModel F d) (fun _ : InfiniteAdelicGroupPoints F G => z) 1 X = 0
    rw [mvfderiv_const]
    rfl
  have hcomplex (X : L) (z : ℂ) : complexPlotSmoothLieAction F G hsmooth hcalc X
      (constantInfiniteSlice F G hsmooth z) = 0 := by
    induction X using TensorProduct.inductionOn with
    | tmul r X => simp only [complexPlotSmoothLieAction_tmul, LinearMap.smul_apply, hderiv, smul_zero]
    | add X Y hX hY => simp only [map_add, LinearMap.add_apply, hX, hY, add_zero]
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ) (UniversalEnvelopingAlgebra.ringCon ℂ L) a
  change plotSmoothEnvelopingAction F G hsmooth hcalc (UniversalEnvelopingAlgebra.mkAlgHom ℂ L t)
      (constantInfiniteSlice F G hsmooth z) = constantInfiniteSlice F G hsmooth
        (adelicEnvelopingAugmentation F G hsmooth (UniversalEnvelopingAlgebra.mkAlgHom ℂ L t) * z)
  induction t using TensorAlgebra.induction generalizing z with
  | algebraMap w =>
    rw [AlgHom.commutes]
    change plotSmoothEnvelopingAction F G hsmooth hcalc (algebraMap ℂ (AdelicEnvelopingAlgebra F G hsmooth) w)
        (constantInfiniteSlice F G hsmooth z) =
      constantInfiniteSlice F G hsmooth
        (adelicEnvelopingAugmentation F G hsmooth (algebraMap ℂ (AdelicEnvelopingAlgebra F G hsmooth) w) * z)
    rw [(plotSmoothEnvelopingAction F G hsmooth hcalc).commutes,
      (adelicEnvelopingAugmentation F G hsmooth).commutes, Module.algebraMap_end_apply]
    rfl
  | «ι» X =>
    change plotSmoothEnvelopingAction F G hsmooth hcalc (UniversalEnvelopingAlgebra.ι ℂ X) _ = _
    rw [plotSmoothEnvelopingAction_generator, hcomplex]
    have hε : adelicEnvelopingAugmentation F G hsmooth (UniversalEnvelopingAlgebra.ι ℂ X) = 0 := by
      unfold adelicEnvelopingAugmentation
      simp
    rw [← show UniversalEnvelopingAlgebra.ι ℂ X = UniversalEnvelopingAlgebra.mkAlgHom ℂ L
      (TensorAlgebra.ι ℂ X) from rfl, hε, zero_mul]
    rfl
  | mul x y hx hy => simp only [map_mul, Module.End.mul_apply, hy, hx, mul_assoc]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy, add_mul]
    rfl

/-- A constant function satisfies the published automorphy conditions for every left subgroup
and specified infinite compact subgroup. -/
theorem isAutomorphicFunctionOn_constant
    (Γ : Subgroup (AdelicGroupPoints F G)) (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    {N : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N)) (z : ℂ) :
    IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho (fun _ => z) := by
  refine ⟨fun _ _ _ => rfl, ⟨continuous_const, fun _ => (constantInfiniteSlice F G hsmooth z).property,
    ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩⟩, ?_, ?_, ?_⟩
  · unfold IsInfiniteSubgroupFiniteFunction
    exact FiniteDimensional.span_of_finite _ ((Set.finite_singleton (fun _ : AdelicGroupPoints F G => z)).subset
      (by rintro _ ⟨k, rfl⟩; exact Set.mem_singleton _))
  · let ε := (adelicEnvelopingAugmentation F G hsmooth).comp
      (Subalgebra.center ℂ (AdelicEnvelopingAlgebra F G hsmooth)).val
    let J := RingHom.ker ε.toRingHom
    have hsurj : Function.Surjective ε := fun t => ⟨algebraMap ℂ _ t, by simp⟩
    refine ⟨J, ?_, ?_⟩
    · let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
      exact Module.Finite.of_injective e.toLinearMap e.injective
    · intro a ha b hb
      change ε a = 0 at ha
      change plotSmoothEnvelopingAction F G hsmooth hcalc a.val (constantInfiniteSlice F G hsmooth z) = 0
      rw [plotSmoothEnvelopingAction_constant, show adelicEnvelopingAugmentation F G hsmooth a.val = 0 from ha,
        zero_mul]
      rfl
  · exact ⟨‖z‖ + 1, by positivity, 0, fun _ => by rw [Real.rpow_zero, mul_one]; exact le_add_of_nonneg_right zero_le_one⟩

end Langlands.Automorphic.GroupSchemeFunctions

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- The scalar kernel occurring in the normalized square-norm estimate has finite absolute
mass on a sufficiently regular region. -/
theorem intertwiningScalarKernelIntegrable
    {F : Type u} [Field F] [NumberField F]
    {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
    {A : CommGroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine V.X.left]
    {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
    {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    {q : Q ⟶ G} {iV : V ⟶ Q} {l' : M' ⟶ Q} [IsClosedImmersion (iV ≫ q).hom.hom.left]
    {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M}
    (hG : IsConnectedReductive G) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hq : IsParabolicSubgroup q) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hl' : IsRationalLeviSubgroup l') (hmul : IsIso (subgroupMultiplication l' iV))
    (hw : IsWeylConjugation p l q l' w c)
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (hKmax : IsMaximalCompactSubgroup F G K) (hrho : IsClosedSubgroup rho) :
    ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
      Integrable (fun v : LeftCosetSpace (intertwiningRationalSubgroup F p iU (iV ≫ q)
          (innerAdelicPoint F G w)) =>
        hK.heightPower (lam + halfModulusParameter F P) ((innerAdelicPoint F G w)⁻¹ *
          ((v.out : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) :
            AdelicGroupPoints F G)))
        (intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w)) := by
  have hconst := isAutomorphicFunctionOn_constant F G hsmooth hcalc
    (parabolicQuotientSubgroup F p iU l) (K.comap (ofInfinite F G).toMonoidHom) rho 1
  obtain ⟨R, hR⟩ := intertwiningIntegrability F G P M U Q M' V A p iU l a r hA hT
    q iV l' w c hG hU hq hV hl' hmul hw K hK rho hsmooth hcalc (fun _ => 1) hKmax hrho hconst
  let test (lam : ComplexCharacterParameter F P) (α : characterLattice A) :=
    Langlands.Plancherel.weylInducedCharacterForm hA hT r.data.f r.data.i
      (realParameterRestriction (a ≫ l) (parameterRealPart F P lam)) ((1 : ℝ) ⊗ₜ[ℤ] α)
  obtain ⟨b, hb⟩ := ((r.finite_unipotentRoots hT).image (test (halfModulusParameter F P))).bddBelow
  refine ⟨R - b, fun lam hlam => ?_⟩
  have hshift : r.IsRegularParameter hA hT R (lam + halfModulusParameter F P) := by
    intro α hα
    have hlamα : R - b < test lam α := hlam α hα
    have h := hb (Set.mem_image_of_mem _ hα)
    change b ≤ test (halfModulusParameter F P) α at h
    change R < test (lam + halfModulusParameter F P) α
    change R < Langlands.Plancherel.weylInducedCharacterForm hA hT r.data.f r.data.i
      (realParameterRestriction (a ≫ l) (parameterRealPart F P (lam + halfModulusParameter F P))) _
    rw [map_add, map_add, map_add, LinearMap.add_apply]
    change R < test lam α + test (halfModulusParameter F P) α
    linarith
  refine (hR (lam + halfModulusParameter F P) hshift 1).congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [IsIwasawaCompact.intertwiningIntegrand, IsIwasawaCompact.parameterTwist, one_mul, mul_one]

end Langlands.Global
