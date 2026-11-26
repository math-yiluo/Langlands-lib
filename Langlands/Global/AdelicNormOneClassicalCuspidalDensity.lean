import Langlands.Automorphic.GroupSchemeClassicalCuspidalHilbertDensity
import Langlands.Automorphic.GroupSchemeDynamicParabolicRadical
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.Global.AdelicPositiveDecompositionProof

/-! # Transfer of classical cuspidal density to the norm-one quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set Filter
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSubgroupPoints PositiveRealTorus RepresentationGrowth

section PeriodComparison

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

private theorem mem_normalizedParabolicCuspidalSubrepresentation_of_zeroTerms
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (f : ContinuousRationalFunctions F G) (hf : HasZeroProperParabolicConstantTerms (evaluate F G f)) :
    f ∈ normalizedParabolicCuspidalSubrepresentation F G hPD hG := by
  apply (mem_normalizedParabolicCuspidalSubrepresentation_iff F G hPD hG f).mpr
  intro P x
  let := hG.isAffineHom
  obtain ⟨χ, hχ⟩ := P.val.property.exists_dynamicCocharacter hPD hG
  let p := Dynamic.Affine.parabolicHom χ
  let j := Dynamic.Affine.unipotentHom χ
  let hp := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  let hu := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  let incl := fun S => Subgroup.inclusion (Dynamic.unipotent_le_parabolic χ S)
  let r := hu.lift hp incl (fun _ _ => rfl)
  have hj : r ≫ p = j := hu.lift_comp_eq hp incl (fun _ _ => rfl) (fun _ _ => rfl)
  have hRep : (Dynamic.unipotent χ).IsRepresentedBy (r ≫ p) := by rw [hj]; exact hu
  have hP := Dynamic.Affine.isParabolicSubgroup_parabolicHom_of_parabolicDynamic hPD hG χ
  have hr := dynamicGeometricUnipotentRadical F G hG χ _ _ p r hp hRep
  let : IsClosedImmersion p.hom.hom.left := hP.isClosedSubgroup
  let : IsAffineHom (Dynamic.Affine.parabolicScheme χ).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_parabolicHom χ).isAffineHom
  let hr' := hr.leviSubgroup
  have hP' : SubgroupFunctor.range p = P.val.val := hp.2.trans hχ
  have hProper : SubgroupFunctor.range p ≠ ⊤ := hP' ▸ P.property
  let : IsClosedImmersion (r ≫ p).hom.hom.left := by
    rw [hj]
    exact Dynamic.Affine.isClosedSubgroup_unipotentHom χ
  let : IsAffineHom (Dynamic.Affine.unipotentScheme χ).X.hom :=
    (Dynamic.Affine.isClosedSubgroup_unipotentHom χ).isAffineHom
  let : IsAffine (Dynamic.Affine.unipotentScheme χ).X.left :=
    isAffine_of_isAffineHom (Dynamic.Affine.unipotentScheme χ).X.hom
  have hzero := congrFun (hf _ _ p r hP hr' hProper) x
  rw [subgroupConstantTerm_eq_continuousConstantTerm (r ≫ p) f x, Pi.zero_apply] at hzero
  have hR : properRationalParabolicRadicals hPD hG P = SubgroupFunctor.range (r ≫ p) :=
    rationalParabolicRadical_eq hPD hG P.val hP hP' hr.isUnipotentRadical
  let avg (U : SubgroupFunctor G)
      (hU : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))) : ℂ :=
    let : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G)) := hU
    constantTerm F G U (normalizedRationalQuotientHaarMeasure F G U) f x
  have hAvg {U W : SubgroupFunctor G} (h : U = W) (hU : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G)))
      (hW : IsClosed (adelicPoints F G W : Set (AdelicGroupPoints F G))) : avg U hU = avg W hW := by
    subst W
    rfl
  change avg _ (isClosed_properRationalParabolicRadicalAdelicPoints F G hPD hG P) = 0
  rw [hAvg hR _ (isClosed_adelicPoints_range F G (r ≫ p))]
  exact hzero

end PeriodComparison

/-- The full cuspidal Hilbert density theorem gives approximation in the
original norm-one quotient seminorm. -/
def AdelicNormOneClassicalCuspidalDensityReductionStatement : Prop :=
  AdelicEnvelopingCenterConjugationStatement.{u} → AdelicNormOneClassicalCuspidalDensityStatement.{u}

theorem adelicNormOneClassicalCuspidalDensity_of_centerConjugation :
    AdelicNormOneClassicalCuspidalDensityReductionStatement.{u} := by
  intro hAd F _ _ G _ _ hG d N hsmooth K rho hK hN hrho f hfInv hf hfCusp hfGrowth ε hε
  let := hG.isAffineHom
  let := normOneHaarRightInvariant F G hG.smooth hG.connectedSpace
  obtain ⟨T, i, hi, _⟩ := adelicPositiveDecompositionStatement F G hG
  let hc := hi.1.2
  have hi₀ := characterRestrict_injective_of_centralSplitTorusCharacter centralSplitTorusCharacter hG hi
  let := characterRestrictionFiniteIndexStatement F G hG T i hi
  obtain ⟨I, hI, ⟨e⟩⟩ := hi.1.1.1
  let := Fintype.ofFinite I
  let := positiveRationalQuotient_borelSpace F G T i hi₀ I e hc
  let Q := PositiveRationalQuotient F G T i
  let Γ := positiveRationalSubgroup F G T i
  let q := LeftCosetSpace.mk Γ
  let dq := positiveRationalQuotientHaarMeasure F G T i
  let dq₁ := normOneRationalQuotientHaarMeasure F G
  let E := positiveQuotientHomeomorph F G T i hi₀ I e hc
  let M := positiveQuotientMeasurableEquiv F G T i hi₀ I e hc
  let S := fullAEL2CuspidalSubmodule F G parabolicDynamic hG T i hi₀ I e hc
  let f₁ := normOneRationalRestriction f
  let fC : ContinuousRationalFunctions F G := ⟨⟨f, fun a x => hfInv _ ⟨a, rfl⟩ x⟩, hf.1⟩
  let φ : C(Q, ℂ) := ⟨f₁ ∘ E.symm, (continuous_normOneRationalRestriction hf.1 hfInv).comp E.symm.continuous⟩
  have hφ_mk (x : normOneSubgroup F G) : φ (q x.val) = f x.val := by
    change f₁ (E.symm (q x.val)) = _
    have hx : E (LeftCosetSpace.mk (rationalNormOneSubgroup F G) x) = q x.val := rfl
    rw [← hx, Homeomorph.symm_apply_apply]
    exact normOneRationalRestriction_mk hfInv x
  have hNormCusp := mem_normalizedParabolicCuspidalSubrepresentation_of_zeroTerms parabolicDynamic hG fC hfCusp
  have hφCusp : positiveQuotientContinuousPullback F G T i φ ∈
      normalizedParabolicCuspidalSubrepresentation F G parabolicDynamic hG := by
    apply (mem_normalizedParabolicCuspidalSubrepresentation_iff F G parabolicDynamic hG _).mpr
    intro P a
    rw [positiveQuotientConstantTerm_normOneProjection F G parabolicDynamic hG T i hi₀ I e hc]
    let x := normOneProjection F G T i hi₀ I e hc a
    have he : properParabolicPositivePeriod F G parabolicDynamic hG T i P φ x =
        constantTerm F G (properRationalParabolicRadicals parabolicDynamic hG P)
          (properParabolicQuotientMeasure F G parabolicDynamic hG P) fC x.val := by
      apply integral_congr_ae (Eventually.of_forall fun z => ?_)
      obtain ⟨n, rfl⟩ := LeftCosetSpace.mk_surjective
        (AdelicSubgroupPoints.rationalSubgroup F G (properRationalParabolicRadicals parabolicDynamic hG P)) z
      rw [properParabolicPositivePeriodIntegrand_mk, constantTermIntegrand_mk]
      exact hφ_mk (properParabolicNormOneInclusion F G parabolicDynamic hG P n * x)
    exact he.trans ((mem_normalizedParabolicCuspidalSubrepresentation_iff F G parabolicDynamic hG fC).mp
      hNormCusp P x.val)
  obtain ⟨R, hR, hDer⟩ := hfGrowth
  obtain ⟨C, _, hCover, hDecay⟩ := adelicNormOneCuspidalRapidDecay hsmooth rho hG hN
  obtain ⟨B, _, hB⟩ := hDecay f hf hfInv hfCusp R hR hDer 0
  have hf₁Mem : MemLp f₁ 2 dq₁ := memLp_normOneRationalRestriction hG hCover hf.1 hfInv
    (fun x hx => by simpa only [pow_zero, mul_one] using hB x hx) 2
  have hφMem : MemLp (φ : Q → ℂ) 2 dq :=
    hf₁Mem.comp_measurePreserving (measurePreserving_positiveQuotient_symm F G T i hi₀ I e hc)
  let v₀ := hφMem.toLp φ
  have hv₀ : (v₀ : Q → ℂ) =ᵐ[dq] φ := hφMem.coeFn_toLp
  let v : S := ⟨v₀, (groupSchemeFullAEL2ContinuousCuspidality F G parabolicDynamic hG T i hi₀ I e hc
    φ v₀ hv₀).mpr hφCusp⟩
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ ε := by
    by_cases ht : ε = ⊤
    · exact ⟨1, zero_lt_one, ht ▸ le_top⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' ht, (ENNReal.ofReal_toReal ht).le⟩
  obtain ⟨w, ψ, hDist, hψ, hψAuto, hψCusp, hψGrowth⟩ :=
    groupSchemeClassicalCuspidalHilbertDensity T i hi₀ I e hc parabolicDynamic hG hsmooth rho K
      hAd hN hrho hK v δ hδ
  let g : AdelicGroupPoints F G → ℂ := ψ ∘ q
  refine ⟨g, hψAuto, hψCusp, hψGrowth, ?_⟩
  have hRestr : normOneRationalRestriction g = (ψ : Q → ℂ) ∘ M := by
    funext z
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective (rationalNormOneSubgroup F G) z
    rw [normOneRationalRestriction_mk hψAuto.1]
    rfl
  have hRestrF : f₁ = (φ : Q → ℂ) ∘ M := by
    funext z
    change f₁ z = f₁ (E.symm (E z))
    rw [Homeomorph.symm_apply_apply]
  have hSub : normOneRationalRestriction f - normOneRationalRestriction g =
      ((φ : Q → ℂ) - (ψ : Q → ℂ)) ∘ M := by
    change f₁ - _ = _
    rw [hRestr, hRestrF]
    rfl
  rw [hSub, eLpNorm_comp_measurePreserving (φ.continuous.sub ψ.continuous).aestronglyMeasurable
    (measurePreserving_positiveQuotient F G T i hi₀ I e hc)]
  rw [← eLpNorm_congr_ae (hv₀.sub hψ), ← Lp.edist_def, Lp.edist_dist]
  rw [dist_eq_norm]
  exact (ENNReal.ofReal_lt_ofReal_iff hδ).mpr hDist |>.trans_le hδε

end Langlands.Global
