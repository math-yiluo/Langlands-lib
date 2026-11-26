import Langlands.Global.AdelicEisensteinTwistComparison
import Langlands.Global.AdelicInducedRightTranslate
import Langlands.Global.AdelicIntertwiningIntegrability

/-! # Regular-region covariance of intertwining integrals under convolution -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  [IsAffine Q.X.left] [IsAffine V.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K) (hQ : IsIwasawaCompact q K)
  (iU : U ⟶ P) (l : M ⟶ P) (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
  (cw : M' ⟶ M) (π' : Q ⟶ M') (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)

local notation "Adele" => AdelicGroupPoints F G
local notation "dh" => (Measure.haar : Measure Adele)
local notation "Γ" => intertwiningRationalSubgroup F p iU (iV ≫ q) (innerAdelicPoint F G w)
local notation "ν" => intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w)

omit [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
private theorem twist_integral_translate
    (lam : ComplexCharacterParameter F P) (a v : Adele → ℂ) (g : Adele) :
    hK.parameterTwist (fun z => ∫ h, a h * hK.inducedRightTranslate lam h v z ∂dh) lam g =
      ∫ h, a h * hK.parameterTwist v lam (g * h) ∂dh := by
  rw [IsIwasawaCompact.parameterTwist, ← integral_mul_const]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun h => by
    change a h * hK.inducedRightTranslate lam h v g * hK.heightPower lam g =
      a h * hK.parameterTwist v lam (g * h)
    rw [mul_assoc, ← IsIwasawaCompact.parameterTwist, hK.parameterTwist_inducedRightTranslate]

omit [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- Where the finite family of comparison integrands is integrable, the actual untwisted operator
is linear in the inducing form. -/
theorem IsIwasawaCompact.intertwiningOperator_sum_mul
    {m : ℕ} (v : Fin m → Adele → ℂ) (b : Fin m → ℂ)
    (lam : ComplexCharacterParameter F P) (g : Adele)
    (hint : ∀ i, Integrable (hK.intertwiningIntegrand iU (iV ≫ q) w (v i) lam g) ν) :
    hK.intertwiningOperator hQ iU l iV cw π' w (fun x => ∑ i, b i * v i x) lam g =
      ∑ i, b i * hK.intertwiningOperator hQ iU l iV cw π' w (v i) lam g := by
  have h := hK.intertwiningIntegral_eq_finset_sum_of_twist hK Finset.univ b
    (fun x => ∑ i, b i * v i x) v lam
    (fun x => by simp only [IsIwasawaCompact.parameterTwist, Finset.sum_mul, mul_assoc])
    iU (iV ≫ q) w g (fun i _ => hint i)
  simp only [IsIwasawaCompact.intertwiningOperator, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _

/-- A compact-uniform integrable majorant permits the intertwining integral to commute with a
compactly supported average of twisted right translates. The target twist uses
`weylParameter l cw π' lam` for the supplied `π'`. -/
theorem IsIwasawaCompact.intertwiningOperator_integral_translate
    (hU : IsUnipotent U) {v : Adele → ℂ} (hv : Continuous v)
    (hvinv : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) v)
    {a : Adele → ℂ} (ha : Continuous a) (has : HasCompactSupport a)
    (lam : ComplexCharacterParameter F P) (g : Adele)
    {b : LeftCosetSpace Γ → ℝ} (hb : Integrable b ν)
    (hbound : ∀ x, ∀ h ∈ tsupport a,
      ‖hK.intertwiningIntegrand iU (iV ≫ q) w v lam (g * h) x‖ ≤ b x) :
    hK.intertwiningOperator hQ iU l iV cw π' w
        (fun z => ∫ h, a h * hK.inducedRightTranslate lam h v z ∂dh) lam g =
      ∫ h, a h * hQ.inducedRightTranslate (weylParameter l cw π' lam) h
        (hK.intertwiningOperator hQ iU l iV cw π' w v lam) g ∂dh := by
  let j := iV ≫ q
  have hclosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) : Set Adele) :=
    hclosed
  let : LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :=
    hclosed.locallyCompactSpace
  let : PolishSpace (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) :=
    hclosed.polishSpace
  let : BorelSpace (LeftCosetSpace Γ) := LeftCosetSpace.discreteQuotientBorelSpace Γ
    (isDiscrete_intertwiningRationalSubgroup F p iU j (innerAdelicPoint F G w))
  let : SFinite ν := by
    unfold intertwiningMeasure AdelicSubgroupPoints.normalizedHaarMeasure
      LeftCosetSpace.discreteQuotientMeasure LeftCosetSpace.quotientMeasure
    infer_instance
  let f (h : Adele) (x : LeftCosetSpace Γ) :=
    a h * hK.intertwiningIntegrand iU j w v lam (g * h) x
  have hf : Continuous (Function.uncurry f) := by
    apply (IsOpenQuotientMap.id.prodMap (LeftCosetSpace.isOpenQuotientMap_mk Γ)).isQuotientMap.continuous_iff.mpr
    change Continuous (fun z : Adele × _ => a z.1 *
      hK.intertwiningIntegrand iU j w v lam (g * z.1) (LeftCosetSpace.mk Γ z.2))
    have hfun : (fun z : Adele × _ => a z.1 *
        hK.intertwiningIntegrand iU j w v lam (g * z.1) (LeftCosetSpace.mk Γ z.2)) =
          fun z => a z.1 * hK.parameterTwist v lam
            ((innerAdelicPoint F G w)⁻¹ * (z.2 : Adele) * (g * z.1)) :=
      funext fun z => congrArg (a z.1 * ·)
        (hK.intertwiningIntegrand_mk iU (iV ≫ q) w hU hvinv lam (g * z.1) z.2)
    rw [hfun]
    exact (ha.comp continuous_fst).mul ((hK.continuous_parameterTwist hv lam).comp
      ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).mul
        (continuous_const.mul continuous_fst)))
  have hprod : Integrable (Function.uncurry f) ((dh).prod ν) := by
    refine ((ha.integrable_of_hasCompactSupport has).norm.mul_prod hb).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    change ‖a z.1 * hK.intertwiningIntegrand iU j w v lam (g * z.1) z.2‖ ≤ ‖a z.1‖ * b z.2
    by_cases hz : a z.1 = 0
    · simp [hz]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound z.2 z.1 (subset_tsupport _ hz)) (norm_nonneg _)
  have hpower : hQ.heightPower (weylParameter l cw π' lam) g ≠ 0 := Complex.exp_ne_zero _
  apply mul_right_cancel₀ hpower
  change hQ.parameterTwist (hK.intertwiningOperator hQ iU l iV cw π' w
    (fun z => ∫ h, a h * hK.inducedRightTranslate lam h v z ∂dh) lam)
    (weylParameter l cw π' lam) g = hQ.parameterTwist
      (fun z => ∫ h, a h * hQ.inducedRightTranslate (weylParameter l cw π' lam) h
        (hK.intertwiningOperator hQ iU l iV cw π' w v lam) z ∂dh)
      (weylParameter l cw π' lam) g
  rw [IsIwasawaCompact.parameterTwist_intertwiningOperator, twist_integral_translate,
    IsIwasawaCompact.intertwiningIntegral]
  simp_rw [IsIwasawaCompact.parameterTwist_intertwiningOperator, IsIwasawaCompact.intertwiningIntegral]
  calc
    _ = ∫ x, ∫ h, f h x ∂dh ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        unfold IsIwasawaCompact.intertwiningIntegrand
        rw [twist_integral_translate]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun h => by simp only [f, IsIwasawaCompact.intertwiningIntegrand, mul_assoc]
    _ = ∫ h, ∫ x, f h x ∂ν ∂dh := (integral_integral_swap hprod).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun h => integral_const_mul _ _

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Convolution against a continuous compactly supported kernel intertwines the defining operator
throughout a sufficiently regular region, with the normalized twists at `λ` and
`weylParameter l cw π' λ`. For a Levi retraction `π'` the latter is the Weyl transport. -/
def IntertwiningConvolutionCovarianceStatement : Prop :=
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
    (iV : V ⟶ Q) (l' : M' ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left] (π' : Q ⟶ M')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (cw : M' ⟶ M),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    IsParabolicSubgroup q → LeviSubgroup.IsGeometricUnipotentRadical iV →
    IsRationalLeviSubgroup l' → IsIso (subgroupMultiplication l' iV) →
    IsWeylConjugation p l q l' w cw →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hQ : IsIwasawaCompact q K) {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (v : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho v →
      ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
        ∀ (a : AdelicGroupPoints F G → ℂ), Continuous a → HasCompactSupport a →
        ∀ g : AdelicGroupPoints F G,
          hK.intertwiningOperator hQ iU l iV cw π' w
            (fun z => ∫ h, a h * hK.inducedRightTranslate lam h v z ∂Measure.haar) lam g =
          ∫ h, a h * hQ.inducedRightTranslate (weylParameter l cw π' lam) h
            (hK.intertwiningOperator hQ iU l iV cw π' w v lam) g ∂Measure.haar

theorem intertwiningConvolutionCovariance : IntertwiningConvolutionCovarianceStatement.{u} := by
  intro F _ _ G P M U Q M' V A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT q _ iV l' _ π' w cw
    hG hU hq hV hl' hmul hw K hK hQ N d rho hsmooth hcalc v hmax hrho hv
  obtain ⟨R, hR⟩ := intertwiningAbsoluteConvergence F G P M U Q M' V A p iU l a r hA hT
    q iV l' w cw hG hU hq hV hl' hmul hw K hK rho hsmooth hcalc v hmax hrho hv
  obtain ⟨n, ⟨e⟩⟩ := exists_complexParameterEquiv hG r.isCompatible.parabolic
  refine ⟨R, fun lam hlam a ha has g => ?_⟩
  have hsingle : ∀ s ∈ ({e.symm lam} : Set (Fin n → ℂ)), r.IsRegularParameter hA hT R (e s) := by
    intro s hs
    rwa [Set.mem_singleton_iff.mp hs, e.apply_symm_apply]
  obtain ⟨b, hb, hbound⟩ := hR ((fun h => g * h) '' tsupport a)
    (has.isCompact.image (continuous_const.mul continuous_id)) n e {e.symm lam} isCompact_singleton hsingle
  refine hK.intertwiningOperator_integral_translate hQ iU l iV cw π' w hU.1.isUnipotent
    hv.2.1.1 (fun x hx g => hv.1 x (Subgroup.mem_sup_left hx) g) ha has lam g hb (fun x h hh => ?_)
  simpa only [e.apply_symm_apply] using
    hbound x (g * h) ⟨h, hh, rfl⟩ (e.symm lam) (Set.mem_singleton _)

end Langlands.Global
