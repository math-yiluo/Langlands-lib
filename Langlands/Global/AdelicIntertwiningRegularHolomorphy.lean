import Langlands.Global.AdelicIntertwiningIntegrability
import Langlands.Global.AdelicEisensteinContinuationReduction
import Langlands.Analysis.SeveralComplex.ParametricIntegral

/-! # Holomorphy of the actual intertwining integral in the regular region -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
open Langlands.Analysis.SeveralComplex

/-- The regular-region holomorphy of the normalized adelic intertwining integral, in every
complex linear coordinate system on the character parameter space. -/
def IntertwiningRegularHolomorphyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left]
    (iV : V ⟶ Q) (l' : M' ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (π' : Q ⟶ M') (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsParabolicSubgroup q → LeviSubgroup.IsGeometricUnipotentRadical iV →
    IsRationalLeviSubgroup l' → IsIso (subgroupMultiplication l' iV) →
    IsWeylConjugation p l q l' w c →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact q K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho φ →
      ∃ R : ℝ, ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
        (g : AdelicGroupPoints F G),
        DifferentiableOn ℂ (fun s => hK.intertwiningOperator hK' iU l iV c π' w φ (e s) g)
          {s | r.IsRegularParameter hA hT R (e s)}

private theorem differentiableOn_integral_of_integrable_majorants
    {n : ℕ} {X : Type*} [MeasurableSpace X] (measure : Measure X)
    (f : (Fin n → ℂ) → X → ℂ) {W : Set (Fin n → ℂ)} (hW : IsOpen W)
    (hf : ∀ x, Differentiable ℂ fun s => f s x)
    (hmeas : ∀ s ∈ W, AEStronglyMeasurable (f s) measure)
    (hbd : ∀ C ⊆ W, IsCompact C →
      ∃ b : X → ℝ, Integrable b measure ∧ ∀ s ∈ C, ∀ x, ‖f s x‖ ≤ b x) :
    DifferentiableOn ℂ (fun s => ∫ x, f s x ∂measure) W := by
  intro s₀ hs₀
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW s₀ hs₀
  let r := ε / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hball : Metric.closedBall s₀ (2 * r) ⊆ W :=
    (Metric.closedBall_subset_ball (by dsimp [r]; linarith)).trans hεW
  obtain ⟨b, hb, hfb⟩ := hbd _ hball (isCompact_closedBall _ _)
  have hball' : Metric.ball s₀ r ⊆ W :=
    Metric.ball_subset_closedBall.trans
      ((Metric.closedBall_subset_closedBall (by linarith)).trans hball)
  have hsub (s : Fin n → ℂ) (hs : s ∈ Metric.ball s₀ r) :
      Metric.closedBall s r ⊆ Metric.closedBall s₀ (2 * r) := by
    intro t ht
    rw [Metric.mem_closedBall] at ht ⊢
    rw [Metric.mem_ball] at hs
    exact (dist_triangle t s s₀).trans (by linarith)
  have hd : HasFDerivAt (fun s => ∫ x, f s x ∂measure)
      (∫ x, fderiv ℂ (fun s => f s x) s₀ ∂measure) s₀ := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F' := fun s x => fderiv ℂ (fun t => f t x) s) (bound := fun x => b x / r)
      (Metric.ball_mem_nhds s₀ hr) ?_ ?_ ?_ ?_ (hb.div_const r) ?_
    · exact Filter.Eventually.mono (hW.mem_nhds hs₀) hmeas
    · exact hb.mono' (hmeas s₀ hs₀) (Filter.Eventually.of_forall fun x =>
        hfb s₀ (Metric.mem_closedBall_self (by linarith)) x)
    · exact aestronglyMeasurable_fderiv f hr (fun s hs => hmeas s (hball' hs))
        (fun x => (hf x).differentiableAt)
    · exact Filter.Eventually.of_forall fun x s hs =>
        norm_fderiv_le isOpen_univ (hf x).differentiableOn hr (Set.subset_univ _)
          (fun t ht => hfb t (hsub s hs ht) x)
    · exact Filter.Eventually.of_forall fun x s _ => (hf x s).hasFDerivAt
  exact hd.differentiableAt.differentiableWithinAt

section Height

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {K : Subgroup (AdelicGroupPoints F G)}

private theorem differentiable_heightPower (hK : IsIwasawaCompact p K) {n : ℕ}
    (L : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    Differentiable ℂ fun s => hK.heightPower (L s) g :=
  ((LinearMap.toContinuousLinearMap
    (((complexParameterPairing F P).flip (hK.height g)).comp L)).differentiable).cexp

end Height

/-- A local uniform majorant for the entire integrands bounds their complex derivatives by
Cauchy's estimate. Differentiation under the quotient integral proves regular holomorphy. -/
theorem intertwiningRegularHolomorphy : IntertwiningRegularHolomorphyStatement.{u} := by
  intro F _ _ G P M U Q M' V A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT q _ iV l' _
    π' w c hG hU hq hV hl' hmul hw K hK hK' N d rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨R, hR⟩ := intertwiningAbsoluteConvergence F G P M U Q M' V A p iU l a r hA hT
    q iV l' w c hG hU hq hV hl' hmul hw K hK rho hsmooth hcalc φ hmax hrho hφ
  let j := iV ≫ q
  let Γ := intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w)
  have hclosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :=
    hclosed.locallyCompactSpace
  let : PolishSpace (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :=
    hclosed.polishSpace
  let : BorelSpace (LeftCosetSpace Γ) := LeftCosetSpace.discreteQuotientBorelSpace Γ
    (isDiscrete_intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w))
  have hinv : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ :=
    fun x hx g => hφ.1 x (Subgroup.mem_sup_left hx) g
  refine ⟨R, fun n e g => ?_⟩
  let f (s : Fin n → ℂ) := hK.intertwiningIntegrand iU j w φ (e s) g
  have hf : ∀ x, Differentiable ℂ fun s => f s x := by
    intro x
    exact (differentiable_const _).mul (differentiable_heightPower hK e.toLinearMap _)
  have hW := isOpen_setOf_isRegularParameter r hA hT hG R e
  have hI := differentiableOn_integral_of_integrable_majorants
    (intertwiningMeasure F p iU j (innerAdelicPoint F G w)) f hW hf
    (fun s _ => (hK.continuous_intertwiningIntegrand iU j w hU.1.isUnipotent
      hinv hφ.2.1.1 (e s) g).aestronglyMeasurable) (fun C hCW hC => by
        obtain ⟨b, hb, hbd⟩ := hR {g} isCompact_singleton n e C hC hCW
        exact ⟨b, hb, fun s hs x => hbd x g (Set.mem_singleton g) s hs⟩)
  exact (differentiable_heightPower hK' (-(weylParameter l c π').comp e.toLinearMap) g
    ).differentiableOn.mul hI

end Langlands.Global
