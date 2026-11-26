import Langlands.Global.AdelicIntertwiningAdjunctionReduction
import Langlands.Global.AdelicIntertwiningIntegrability
import Langlands.Analysis.Meromorphic.ContinuationUniqueness
import Langlands.Analysis.SeveralComplex.ConvexIntegralDomain

/-! # Agreement of the intertwining integral from reflected-region integrability -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set Filter Topology
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic Langlands.Analysis.SeveralComplex

/-- Pointwise absolute convergence of the actual intertwining integral on the sufficiently
regular reflected region. -/
def IntertwiningReflectedRegionIntegrabilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    (A A' : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (_hA : IsSplitTorus A.toGrp) (_hT : IsSplitTorus r.data.T.toGrp)
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q)
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (a' : A'.toGrp ⟶ M') (r' : ParabolicRootPresentation q l' a')
    [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
    [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
    (hA' : IsSplitTorus A'.toGrp) (hT' : IsSplitTorus r'.data.T.toGrp) (π' : Q ⟶ M')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    LeviSubgroup.IsGeometricUnipotentRadical iV → l' ≫ π' = 𝟙 M' →
    IsWeylConjugation p l q l' w c →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (_hK' : IsIwasawaCompact q K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho φ →
      ∃ R : ℝ, ∀ lam : ComplexCharacterParameter F P,
        r'.IsRegularParameter hA' hT' R (-weylParameter l c π' lam) →
        ∀ g, Integrable (hK.intertwiningIntegrand iU (iV ≫ q) w φ lam g)
          (intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w))

private theorem eqOn_of_meromorphic_of_isPreconnected
    {n : ℕ} {f v : (Fin n → ℂ) → ℂ} {W D O : Set (Fin n → ℂ)}
    (hWo : IsOpen W) (hWc : IsPreconnected W) (hf : DifferentiableOn ℂ f W)
    (hv : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) v D)
    (hOo : IsOpen O) (hOne : O.Nonempty) (hOW : O ⊆ W) (heq : EqOn f v O) :
    EqOn f v (W ∩ D) := by
  obtain ⟨hDo, hDd, hvd, hloc⟩ := isMeromorphicOn_iff.mp hv
  have hfden : HasLocalDenominators f W W := by
    intro s hs
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hWo s hs
    refine ⟨Metric.ball s ε, Metric.isOpen_ball, (convex_ball s ε).isPreconnected,
      Metric.mem_ball_self hε, fun _ => 1, f, differentiableOn_const 1,
      ⟨s, Metric.mem_ball_self hε, one_ne_zero⟩, hf.mono hball, fun t _ => one_mul (f t)⟩
  have hvden : HasLocalDenominators v D W := by
    intro s _
    obtain ⟨B, hBo, hBc, hsB, g, h, hg, hne, hh, hid⟩ := hloc s
    exact ⟨B, hBo, hBc.isPreconnected, hsB, g, h, hg, hne, hh, hid⟩
  obtain ⟨s₀, hs₀⟩ := hOne
  exact fun _ hs => eq_of_hasLocalDenominators hWo hWc hWo hDo
    subset_closure (fun t _ => hDd t) hf.continuousOn hvd.continuousOn hfden hvden
    (hOW hs₀) (Filter.eventually_of_mem (hOo.mem_nhds hs₀) fun _ ht _ _ => heq ht) _ hs.1 hs.1 hs.2

section Height

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
private theorem differentiable_heightPower_inCoordinates (hK : IsIwasawaCompact p K) {n : ℕ}
    (L : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    Differentiable ℂ fun s => hK.heightPower (L s) g :=
  ((LinearMap.toContinuousLinearMap
    (((complexParameterPairing F P).flip (hK.height g)).comp L)).differentiable).cexp

end Height

/-- Reflected-region integrability suffices for the agreement of the actual integral
with every finite meromorphic expansion. -/
theorem intertwiningReflectedRegionAgreement_of_integrability
    (hReflected : IntertwiningReflectedRegionIntegrabilityStatement.{u}) :
    IntertwiningReflectedRegionAgreementStatement.{u} := by
  intro F _ _ G P M U Q M' V A A' _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT q _ iV l' _
    a' r' _ _ _ hA' hT' π' w c hG hU hV hπ' hw K hK hK' N d rho hsmooth hcalc φ
    hmax hrho hφ k ψ coeff D hmer hsource
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨R, hR⟩ := hReflected F G P M U Q M' V A A' p iU l a r hA hT
    q iV l' a' r' hA' hT' π' w c hG hU hV hπ' hw K hK hK' rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨R₁, hR₁⟩ := intertwiningIntegrability F G P M U Q M' V A p iU l a r hA hT
    q iV l' w c hG hU r'.isCompatible.parabolic hV r'.isCompatible.levi
    (r'.isIso_subgroupMultiplication_of_radical hV) hw K hK rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨R₀, hR₀⟩ := hsource
  obtain ⟨n, ⟨e⟩⟩ := exists_complexParameterEquiv hG r.isCompatible.parabolic
  let : IsIso c := hw.isIso
  obtain ⟨Weyl, hWeyl⟩ := exists_weylParameter_linearEquiv l l'
    r.isCompatible.levi r'.isCompatible.levi c π' hπ'
  let e' := e.trans (Weyl.trans (LinearEquiv.neg (M := ComplexCharacterParameter F Q) ℂ))
  have he' (s) : e' s = -weylParameter l c π' (e s) :=
    congrArg Neg.neg (LinearMap.congr_fun hWeyl (e s))
  let O : Set (Fin n → ℂ) := {s | r.IsRegularParameter hA hT (max R₀ R₁) (e s)}
  let O' : Set (Fin n → ℂ) := {s | r'.IsRegularParameter hA' hT' R (e' s)}
  have hOo : IsOpen O := r.isOpen_regularParameter_inCoordinates hA hT _ e
  have hOne : O.Nonempty := r.nonempty_regularParameter_inCoordinates hA hT _ e
  have hO'o : IsOpen O' := r'.isOpen_regularParameter_inCoordinates hA' hT' R e'
  let : FiniteDimensional ℂ (ComplexCharacterParameter F P) := LinearEquiv.finiteDimensional e
  obtain ⟨hDt, hcoeff⟩ := isMeromorphicInCoordinatesOn_iInter_finite hmer
  let Dt : Set (Fin n → ℂ) := e ⁻¹' ⋂ _ : Fin k, D
  let j := iV ≫ q
  let Γ := intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w)
  let measure := intertwiningMeasure F p iU j (innerAdelicPoint F G w)
  have hclosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :=
    hclosed.locallyCompactSpace
  let : PolishSpace (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :=
    hclosed.polishSpace
  let : BorelSpace (LeftCosetSpace Γ) := LeftCosetSpace.discreteQuotientBorelSpace Γ
    (isDiscrete_intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w))
  have hinv : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ :=
    fun x hx g => hφ.1 x (Subgroup.mem_sup_left hx) g
  refine ⟨R, fun lam hlam hlamD g => ?_⟩
  let f (s : Fin n → ℂ) := hK.intertwiningIntegrand iU j w φ (e s) g
  let W := interior {s | Integrable (f s) measure}
  have hnorm (x : LeftCosetSpace Γ) : ConvexOn ℝ univ (fun s => ‖f s x‖) := by
    let y := (innerAdelicPoint F G w)⁻¹ *
      ((Quotient.out x :
        AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) : AdelicGroupPoints F G) * g
    exact convexOn_norm_mul_cexp_linear (φ y)
      (((complexParameterPairing F P).flip (hK.height y)).comp e.toLinearMap)
  have hmeas (s) : AEStronglyMeasurable (f s) measure :=
    (hK.continuous_intertwiningIntegrand iU j w hU.1.isUnipotent hinv hφ.2.1.1 (e s) g
      ).aestronglyMeasurable
  have hdiff (x : LeftCosetSpace Γ) : Differentiable ℂ (fun s => f s x) :=
    (differentiable_const _).mul (differentiable_heightPower_inCoordinates hK e.toLinearMap _)
  have hI := differentiableOn_integral_interior_of_convex_norm hdiff hmeas hnorm
  have hOp : O ⊆ W := hOo.subset_interior_iff.mpr fun s hs =>
    hR₁ (e s) (fun α hα => (le_max_right R₀ R₁).trans_lt (hs α hα)) g
  have hO'p : O' ⊆ W := hO'o.subset_interior_iff.mpr fun s hs => by
    apply hR (e s) _ g
    rw [← he']
    exact hs
  let v (s : Fin n → ℂ) := hK.intertwiningOperator hK' iU l iV c π' w φ (e s) g
  have hv : DifferentiableOn ℂ v W :=
    (differentiable_heightPower_inCoordinates hK' (-(weylParameter l c π').comp e.toLinearMap) g
      ).differentiableOn.mul hI
  have hsum : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun s => ∑ i, coeff i (e s) * ψ i g) Dt :=
    isMeromorphicOn_sum Finset.univ (hDt n e).1 (hDt n e).2 fun i _ =>
      ((hcoeff i).2 n e).mul_const (ψ i g)
  have hagree := eqOn_of_meromorphic_of_isPreconnected isOpen_interior
    (convex_setOf_integrable hmeas hnorm).interior.isPreconnected hv hsum hOo hOne hOp
    (fun s hs => hR₀ (e s) (fun α hα => (le_max_left R₀ R₁).trans_lt (hs α hα)) g)
  have htarget : e.symm lam ∈ O' := by
    change r'.IsRegularParameter hA' hT' R (e' (e.symm lam))
    rwa [he', e.apply_symm_apply]
  have hdom : e.symm lam ∈ Dt := by
    change e (e.symm lam) ∈ ⋂ _ : Fin k, D
    rw [e.apply_symm_apply]
    exact mem_iInter.mpr fun _ => hlamD
  simpa only [v, e.apply_symm_apply] using hagree ⟨hO'p htarget, hdom⟩

end Langlands.Global
