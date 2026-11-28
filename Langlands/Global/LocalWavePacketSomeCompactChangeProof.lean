import Langlands.Global.LocalWavePacketSomeCompactReduction
import Langlands.Global.AdelicWavePacketCompactCutoffs
import Langlands.Global.AdelicIwasawaCompatibleMeasureProof
import Langlands.Global.AdelicWavePacketRationalInvariance
import Langlands.Global.AdelicImaginaryIntertwiningProperties
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! # Changing the compact subgroup in Lapid's wave-packet formula -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global

open GroupScheme Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Analysis.Meromorphic WavePacketCompactChange

namespace WavePacketCompactChange

section RegularBounds

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

private theorem exists_regularBound {I : Type} [Fintype I]
    {C : I → ComplexCharacterParameter F P → Prop}
    (h : ∀ i, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → C i lam) :
    ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ i, C i lam := by
  classical
  choose R hR using h
  let B : ℝ := ∑ i, max (R i) 0
  refine ⟨B, fun lam hlam i => hR i lam (ParabolicRootPresentation.IsRegularParameter.mono r hA hT ?_ hlam)⟩
  exact (le_max_left (R i) 0).trans
    (Finset.single_le_sum (f := fun j => max (R j) 0) (fun _ _ => le_max_right _ _) (Finset.mem_univ i))

end RegularBounds

section Coefficients

variable {F : Type} [Field F] [NumberField F] {P : GroupScheme (Spec (CommRingCat.of F))}

private theorem entire_coefficient {X : Type*} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (T : X →ₗ[ℂ] ComplexCharacterParameter F P) (u : RealCharacterDual F P) :
    IsMeromorphicInCoordinatesOn (fun lam => coefficient u (T lam)) univ := by
  apply isMeromorphicInCoordinatesOn_univ
  intro n e
  let Lv : ComplexCharacterParameter F P →ₗ[ℂ] ℂ :=
    { toFun := fun lam => complexParameterPairing F P lam u
      map_add' := fun x y => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun z x => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  exact ((Lv.comp (T.comp e.toLinearMap)).toContinuousLinearMap.differentiable).cexp

end Coefficients

section Operators

variable {F : Type} [Field F] [NumberField F]
  {G P Q M M' U V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left] [IsAffine Q.X.left]
  [LocallyOfFiniteType P.X.hom] [LocallyOfFiniteType Q.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left]
  {K L : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K) (hL : IsIwasawaCompact p L)
  (hK' : IsIwasawaCompact q K) (hL' : IsIwasawaCompact q L)
  {n n' : ℕ} {u : Fin n → RealCharacterDual F P} {u' : Fin n' → RealCharacterDual F Q}
  {s : AdelicGroupPoints F G}
  (hu : Function.Injective u) (hcover : ∀ g, ∃ i, heightDifference hK hL s g = u i)
  (hu' : Function.Injective u') (hcover' : ∀ g, ∃ i, heightDifference hK' hL' s g = u' i)

local notation "Gₐ" => (AdelicGroupPoints F G)
local notation "C" => (ComplexCharacterParameter F P)

include hu hcover in
private theorem eisensteinSeries_cutoff (φ : Gₐ → ℂ) (lam : C) (g : Gₐ)
    (hSum : ∀ i, Summable (hL.eisensteinTerm (cutoff hK hL s (u i) φ) lam g)) :
    hK.eisensteinSeries φ lam (g * s) =
      ∑ i, coefficient (u i) lam * hL.eisensteinSeries (cutoff hK hL s (u i) φ) lam g := by
  classical
  have hterm (x : ParabolicRationalCosets F p) :
      hK.eisensteinTerm φ lam (g * s) x =
        ∑ i, coefficient (u i) lam * hL.eisensteinTerm (cutoff hK hL s (u i) φ) lam g x := by
    unfold IsIwasawaCompact.eisensteinTerm
    rw [← mul_assoc]
    exact parameterTwist_cutoff hK hL hu hcover φ lam _
  unfold IsIwasawaCompact.eisensteinSeries
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum]
  · simp only [tsum_mul_left]
  · exact fun i _ => (hSum i).mul_left _

variable [IsAffine V.X.left] (iU : U ⟶ P) (l : M ⟶ P) (iV : V ⟶ Q)
  [IsClosedImmersion (iV ≫ q).hom.hom.left] (cw : M' ⟶ M) (π' : Q ⟶ M')
  (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)

include hu hcover hu' hcover' in
set_option maxHeartbeats 950000 in
private theorem intertwiningOperator_cutoff {m : ℕ} (φ : Gₐ → ℂ) (ψ : Fin m → Gₐ → ℂ)
    (d : Fin m → ℂ) (lam : C) (g : Gₐ)
    (hOld : hK.intertwiningOperator hK' iU l iV cw π' w φ lam (g * s) =
      ∑ j, d j * ψ j (g * s))
    (hInt : ∀ i, Integrable (hL.intertwiningIntegrand iU (iV ≫ q) w
      (cutoff hK hL s (u i) φ) lam g)
        (intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w))) :
    ∑ i, coefficient (u i) lam * hL.intertwiningOperator hL' iU l iV cw π' w
      (cutoff hK hL s (u i) φ) lam g =
      ∑ j, ∑ b, (d j * coefficient (u' b) (weylParameter l cw π' lam)) *
        cutoff hK' hL' s (u' b) (ψ j) g := by
  classical
  let lam' := weylParameter l cw π' lam
  have hterm (x : LeftCosetSpace (intertwiningRationalSubgroup F p iU (iV ≫ q)
      (innerAdelicPoint F G w))) :
      hK.intertwiningIntegrand iU (iV ≫ q) w φ lam (g * s) x =
        ∑ i, coefficient (u i) lam * hL.intertwiningIntegrand iU (iV ≫ q) w
          (cutoff hK hL s (u i) φ) lam g x := by
    unfold IsIwasawaCompact.intertwiningIntegrand
    rw [← mul_assoc]
    exact parameterTwist_cutoff hK hL hu hcover φ lam _
  have hTransfer : hK.intertwiningIntegral iU (iV ≫ q) w φ lam (g * s) =
      ∑ i, coefficient (u i) lam * hL.intertwiningIntegral iU (iV ≫ q) w
        (cutoff hK hL s (u i) φ) lam g := by
    unfold IsIwasawaCompact.intertwiningIntegral
    simp_rw [hterm]
    rw [integral_finsetSum]
    · simp only [integral_const_mul]
    · exact fun i _ => (hInt i).const_mul _
  simp_rw [← IsIwasawaCompact.parameterTwist_intertwiningOperator hK hK' iU l iV cw π' w φ lam,
    ← IsIwasawaCompact.parameterTwist_intertwiningOperator hL hL' iU l iV cw π' w _ lam] at hTransfer
  let z := hL'.heightPower lam' g
  apply mul_right_cancel₀ (show z ≠ 0 from Complex.exp_ne_zero _)
  calc
    _ = hK'.parameterTwist (hK.intertwiningOperator hK' iU l iV cw π' w φ lam) lam' (g * s) := by
      rw [hTransfer, Finset.sum_mul]
      simp only [IsIwasawaCompact.parameterTwist, mul_assoc, z, lam']
    _ = ∑ j, d j * hK'.parameterTwist (ψ j) lam' (g * s) := by
      simp only [IsIwasawaCompact.parameterTwist, hOld, Finset.sum_mul, mul_assoc]
    _ = _ := by
      simp_rw [parameterTwist_cutoff hK' hL' hu' hcover']
      simp only [IsIwasawaCompact.parameterTwist, Finset.mul_sum, Finset.sum_mul, mul_assoc, z, lam']

end Operators

end WavePacketCompactChange

set_option maxHeartbeats 4500000 in
/-- The wave-packet pairing for holomorphic families at one maximal compact gives the
fixed-vector pairing at every maximal compact with Iwasawa decompositions for both parabolics. -/
theorem localWavePacketSomeCompactChange : LocalWavePacketSomeCompactChangeStatement := by
  classical
  intro h F _ _ G P M U P' M' U' A A' _ _ _ _ _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT
    p' _ iU' l' _ a' r' _ _ _ hA' hT' π' hG hU hU' hlπ' K hK hK' N d rho hsmooth hcalc
    hKmax hrho μM' _ hμM' n n' e e' β' hβc' hβs' hβ1' k v c S E D hv hS hc hD hE hEreg
    k' v' c' S' E' D' hv' hS' hc' hD' hE' hEreg' T _ w cw hw hinj hsurj m ψ coeff DM
    hψ hDM hcoeff hexp Θ Θ' μG
  let : LocallyOfFiniteType P.X.hom := IsClosedSubgroup.locallyOfFiniteType (j := p) r.isCompatible.parabolic.isClosedSubgroup
  let : LocallyOfFiniteType P'.X.hom := IsClosedSubgroup.locallyOfFiniteType (j := p') r'.isCompatible.parabolic.isClosedSubgroup
  obtain ⟨L, hL, hL', hLmax, hLpack⟩ :=
    h F G P M U P' M' U' A A' p iU l a r hA hT p' iU' l' a' r' hA' hT' π' hG hU hU' hlπ'
  obtain ⟨b, hb⟩ := InfiniteAdelicGroupPoints.infiniteAdelicMaximalCompactConjugacy F G
    (K.comap (ofInfinite F G).toMonoidHom) (L.comap (ofInfinite F G).toMonoidHom) hG
    hKmax.isMaximalCompact_comap_ofInfinite hLmax.isMaximalCompact_comap_ofInfinite
  let s := ofInfinite F G b
  obtain ⟨q, u, hu, huCover, hcut⟩ :=
    exists_cutoff_family (iU := iU) (l := l) hK hL b hKmax hLmax hb rho hsmooth hcalc
  obtain ⟨q', u', hu', huCover', hcut'⟩ :=
    exists_cutoff_family (iU := iU') (l := l') hK' hL' b hKmax hLmax hb rho hsmooth hcalc
  obtain ⟨μM, hHaarM, hμM⟩ := iwasawaCompatibleMeasureExistence F G P M U A p iU l a r hG hU K hK hKmax
  obtain ⟨νM, hHaarN, hνM⟩ := iwasawaCompatibleMeasureExistence F G P M U A p iU l a r hG hU L hL hLmax
  obtain ⟨νM', hHaarN', hνM'⟩ :=
    iwasawaCompatibleMeasureExistence F G P' M' U' A' p' iU' l' a' r' hG hU' L hL' hLmax
  let : μM.IsHaarMeasure := hHaarM
  let : νM.IsHaarMeasure := hHaarN
  let : νM'.IsHaarMeasure := hHaarN'
  let : Smooth G.X.hom := hG.smooth
  let : IsIso (subgroupMultiplication l iU) := r.isIso_subgroupMultiplication_of_radical hU
  let : IsIso (subgroupMultiplication l' iU') := r'.isIso_subgroupMultiplication_of_radical hU'
  let π := leviRetraction l iU hU.1.isNormal
  have hlπ : l ≫ π = 𝟙 M := levi_comp_leviRetraction l iU hU.1.isNormal
  let bump : ContDiffBump (0 : Fin n → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let β := bump.normed volume
  have hβne : ∃ y, β y ≠ 0 := by
    by_contra! hzero
    have h1 : ∫ y, β y = 1 := bump.integral_normed
    simp [hzero] at h1
  have hβne' : ∃ y, β' y ≠ 0 := by
    by_contra! hzero
    simp [hzero] at hβ1'
  let vL := fun j i => cutoff hK hL s (u i) (v j)
  let vL' := fun j i => cutoff hK' hL' s (u' i) (v' j)
  let ψL := fun t j (i : Fin (m * q')) =>
    cutoff hK' hL' s (u' (finProdFinEquiv.symm i).2) (ψ t j (finProdFinEquiv.symm i).1)
  let phase := fun (_ : Fin k) (i : Fin q) => coefficient (u i)
  let phase' := fun (_ : Fin k') (i : Fin q') => coefficient (u' i)
  let coeffL := fun t j (i : Fin (m * q')) lam =>
    coeff t j (finProdFinEquiv.symm i).1 lam *
      coefficient (u' (finProdFinEquiv.symm i).2) (weylParameter l (cw t) π' lam)
  let EL := fun j lam (g : AdelicGroupPoints F G) => E j lam (g * s)
  let EL' := fun j lam (g : AdelicGroupPoints F G) => E' j lam (g * s)
  have hSq {φ : AdelicGroupPoints F G → ℂ}
      (hφ : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l φ) (i : Fin q) :
      IsSquareIntegrableInducedForm L hL.isCompact rho hsmooth hcalc p iU l (cutoff hK hL s (u i) φ) :=
    squareIntegrable_cutoff hK hL hG r.isCompatible.levi hU r.isCompatible.splitComponent hA hlπ
      μM νM hμM hνM e bump.continuous_normed bump.hasCompactSupport_normed hβne hφ (hcut hφ.1 i)
  have hSq' {φ : AdelicGroupPoints F G → ℂ}
      (hφ : IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' φ) (i : Fin q') :
      IsSquareIntegrableInducedForm L hL'.isCompact rho hsmooth hcalc p' iU' l' (cutoff hK' hL' s (u' i) φ) :=
    squareIntegrable_cutoff hK' hL' hG r'.isCompatible.levi hU' r'.isCompatible.splitComponent hA' hlπ'
      μM' νM' hμM' hνM' e' hβc' hβs' hβne' hφ (hcut' hφ.1 i)
  have hVL j i : IsSquareIntegrableInducedForm L hL.isCompact rho hsmooth hcalc p iU l (vL j i) := hSq (hv j) i
  have hVL' j i : IsSquareIntegrableInducedForm L hL'.isCompact rho hsmooth hcalc p' iU' l' (vL' j i) :=
    hSq' (hv' j) i
  have hψL t j i : IsSquareIntegrableInducedForm L hL'.isCompact rho hsmooth hcalc p' iU' l' (ψL t j i) :=
    hSq' (hψ t j _) _
  obtain ⟨_, ⟨eC⟩⟩ := exists_complexParameterEquiv hG r.isCompatible.parabolic
  obtain ⟨_, ⟨eC'⟩⟩ := exists_complexParameterEquiv hG r'.isCompatible.parabolic
  let : FiniteDimensional ℂ (ComplexCharacterParameter F P) :=
    FiniteDimensional.of_injective eC.symm.toLinearMap eC.symm.injective
  let : FiniteDimensional ℂ (ComplexCharacterParameter F P') :=
    FiniteDimensional.of_injective eC'.symm.toLinearMap eC'.symm.injective
  have hphase j i : IsMeromorphicInCoordinatesOn (phase j i) univ := entire_coefficient LinearMap.id _
  have hphase' j i : IsMeromorphicInCoordinatesOn (phase' j i) univ := entire_coefficient LinearMap.id _
  have hcoeffL t j i : IsMeromorphicInCoordinatesOn (coeffL t j i) DM := by
    have hphaseW := entire_coefficient (weylParameter l (cw t) π') (u' (finProdFinEquiv.symm i).2)
    change IsMeromorphicInCoordinatesOn
      (coeff t j (finProdFinEquiv.symm i).1 *
        (fun lam => coefficient (u' (finProdFinEquiv.symm i).2) (weylParameter l (cw t) π' lam))) DM
    simpa only [inter_univ] using (hcoeff t j (finProdFinEquiv.symm i).1).mul hphaseW
  have hEL j : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
      EL j lam g = ∑ i, phase j i lam * hL.eisensteinSeries (vL j i) lam g := by
    obtain ⟨R, hR⟩ := hEreg j
    obtain ⟨B, hB⟩ := exists_regularBound r hA hT (fun i : Fin q =>
      eisensteinAbsoluteConvergence.exists_summable_eisensteinTerm r hA hT hG hU hL rho hsmooth
        hcalc hLmax hrho (hVL j i).1)
    refine ⟨max R B, fun lam hreg g => ?_⟩
    dsimp only [EL, phase, vL]
    rw [hR lam (ParabolicRootPresentation.IsRegularParameter.mono r hA hT (le_max_left _ _) hreg)]
    exact eisensteinSeries_cutoff hK hL hu huCover (v j) lam g
      (fun i => hB lam (ParabolicRootPresentation.IsRegularParameter.mono r hA hT (le_max_right _ _) hreg) i g)
  have hEL' j : ∃ R : ℝ, ∀ lam, r'.IsRegularParameter hA' hT' R lam → ∀ g,
      EL' j lam g = ∑ i, phase' j i lam * hL'.eisensteinSeries (vL' j i) lam g := by
    obtain ⟨R, hR⟩ := hEreg' j
    obtain ⟨B, hB⟩ := exists_regularBound r' hA' hT' (fun i : Fin q' =>
      eisensteinAbsoluteConvergence.exists_summable_eisensteinTerm r' hA' hT' hG hU' hL' rho hsmooth
        hcalc hLmax hrho (hVL' j i).1)
    refine ⟨max R B, fun lam hreg g => ?_⟩
    dsimp only [EL', phase', vL']
    rw [hR lam (ParabolicRootPresentation.IsRegularParameter.mono r' hA' hT' (le_max_left _ _) hreg)]
    exact eisensteinSeries_cutoff hK' hL' hu' huCover' (v' j) lam g
      (fun i => hB lam (ParabolicRootPresentation.IsRegularParameter.mono r' hA' hT' (le_max_right _ _) hreg) i g)
  have hexpL t j : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
      ∑ i, phase j i lam * hL.intertwiningOperator hL' iU l iU' (cw t) π' (w t) (vL j i) lam g =
        ∑ i, coeffL t j i lam * ψL t j i g := by
    obtain ⟨R, hR⟩ := hexp t j
    obtain ⟨B, hB⟩ := exists_regularBound r hA hT (fun i : Fin q =>
      intertwiningIntegrability F G P M U P' M' U' A p iU l a r hA hT
        p' iU' l' (w t) (cw t) hG hU r'.isCompatible.parabolic hU' r'.isCompatible.levi
        inferInstance (hw t) L hL rho hsmooth hcalc (vL j i) hLmax hrho (hVL j i).1)
    refine ⟨max R B, fun lam hreg g => ?_⟩
    rw [← finProdFinEquiv.sum_comp]
    simp only [coeffL, ψL, Equiv.symm_apply_apply, Fintype.sum_prod_type, vL, phase]
    exact intertwiningOperator_cutoff hK hL hK' hL' hu huCover hu' huCover' iU l iU' (cw t) π' (w t)
      (v j) (ψ t j) (fun i => coeff t j i lam) lam g
      (hR lam (ParabolicRootPresentation.IsRegularParameter.mono r hA hT (le_max_left _ _) hreg) (g * s))
      (fun i => hB lam (ParabolicRootPresentation.IsRegularParameter.mono r hA hT (le_max_right _ _) hreg) i g)
  obtain ⟨hΘL, hΘL', hPairL⟩ := hLpack rho hsmooth hcalc hrho νM' hνM'
    e e' β' hβc' hβs' hβ1' k q vL phase c S EL D hVL hphase hS hc hD (fun j g => hE j (g * s)) hEL
    k' q' vL' phase' c' S' EL' D' hVL' hphase' hS' hc' hD' (fun j g => hE' j (g * s)) hEL'
    T w cw hw hinj hsurj (m * q') ψL coeffL DM hψL hDM hcoeffL hexpL
  have hΘ : IsLeftInvariantUnder F G (rationalSubgroup F G) Θ :=
    packetIntegral_leftRationalInvariant (spectralMeasure n) (D := D)
      (fun x => imaginaryParameter F P (e x)) c E
      (fun j x hx => by
        refine hD ⟨x, ?_, rfl⟩
        by_contra hn
        exact hx ((hc j).2 x hn))
      (fun j _ hLam => eisensteinContinuation_leftRationalInvariant hK (hv j).1.1 hU r hA hT hG
        (hE j) (hEreg j) hLam)
  have hΘ' : IsLeftInvariantUnder F G (rationalSubgroup F G) Θ' :=
    packetIntegral_leftRationalInvariant (spectralMeasure n') (D := D')
      (fun x => imaginaryParameter F P' (e' x)) c' E'
      (fun j x hx => by
        refine hD' ⟨x, ?_, rfl⟩
        by_contra hn
        exact hx ((hc' j).2 x hn))
      (fun j _ hLam => eisensteinContinuation_leftRationalInvariant hK' (hv' j).1.1 hU' r' hA' hT' hG
        (hE' j) (hEreg' j) hLam)
  let Γ := rationalSubgroup F G
  let : BorelSpace (RationalQuotient F G) := LeftCosetSpace.discreteQuotientBorelSpace Γ
    (isDiscrete_rationalSubgroup F G)
  let τ := (LeftCosetSpace.rightTranslateHomeomorph Γ s).toMeasurableEquiv
  let : (Measure.haar : Measure (AdelicGroupPoints F G)).IsMulRightInvariant := adelicHaarUnimodularity.2 F G hG
  have hτ : MeasurePreserving τ μG μG := measurePreserving_rightTranslate_rationalQuotientHaarMeasure F G s
  have hR (y : RationalQuotient F G) : Θ (τ y).out = Θ (y.out * s) := rightTranslate_out_of_invariant hΘ s y
  have hR' (y : RationalQuotient F G) : Θ' (τ y).out = Θ' (y.out * s) := rightTranslate_out_of_invariant hΘ' s y
  change MemLp (fun y : RationalQuotient F G => Θ (y.out * s)) 2 μG at hΘL
  change MemLp (fun y : RationalQuotient F G => Θ' (y.out * s)) 2 μG at hΘL'
  have hL2 : MemLp (fun y : RationalQuotient F G => Θ y.out) 2 μG := by
    rw [← hτ.map_eq]
    apply τ.memLp_map_measure_iff.mpr
    change MemLp (fun y : RationalQuotient F G => Θ (τ y).out) 2 μG
    rw [funext hR]
    exact hΘL
  have hL2' : MemLp (fun y : RationalQuotient F G => Θ' y.out) 2 μG := by
    rw [← hτ.map_eq]
    apply τ.memLp_map_measure_iff.mpr
    change MemLp (fun y : RationalQuotient F G => Θ' (τ y).out) 2 μG
    rw [funext hR']
    exact hΘL'
  have hPairTranslate :
      (∫ y : RationalQuotient F G, Θ y.out * starRingEnd ℂ (Θ' y.out) ∂μG) =
      ∫ y : RationalQuotient F G, Θ (y.out * s) * starRingEnd ℂ (Θ' (y.out * s)) ∂μG := by
    rw [← hτ.integral_comp' (fun y : RationalQuotient F G => Θ y.out * starRingEnd ℂ (Θ' y.out))]
    simp only [hR, hR']
    rfl
  refine ⟨hL2, hL2', hPairTranslate.trans (hPairL.trans ?_)⟩
  apply integral_congr_ae
  filter_upwards with x
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← finProdFinEquiv.sum_comp]
  simp only [Fintype.sum_prod_type, coeffL, ψL, Equiv.symm_apply_apply, phase', vL']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => ?_
  let lamP := imaginaryParameter F P (e x)
  let lamQ := weylParameter l (cw t) π' lamP
  let d := c j x * coeff t j i lamP *
    starRingEnd ℂ (c' j' (e'.symm (realWeylParameter l (cw t) π' (e x))))
  let a₀ (f : Fin q') := coefficient (u' f) lamQ
  let B (f g : Fin q') := inducedInnerProduct L hL'.isCompact p' l' νM' e' β'
    (cutoff hK' hL' s (u' f) (ψ t j i)) (cutoff hK' hL' s (u' g) (v' j'))
  have hBase := inducedInnerProduct_eq_sum_cutoff hK' hL' hG r'.isCompatible.levi hU'
    r'.isCompatible.splitComponent hA' hlπ' μM' νM' hμM' hνM' e' hβc' hβs' hu' huCover'
    (hψ t j i) (hv' j') (hSq' (hψ t j i)) (hSq' (hv' j'))
  rw [hBase, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_eq_single f]
  · have hPhase : a₀ f * starRingEnd ℂ (a₀ f) = 1 := by
      change coefficient (u' f) (weylParameter l (cw t) π' lamP) *
        starRingEnd ℂ (coefficient (u' f) (weylParameter l (cw t) π' lamP)) = 1
      dsimp only [lamP]
      rw [weylParameter_imaginaryParameter]
      exact coefficient_mul_star_of_imaginary _ _
    calc
      _ = d * (a₀ f * starRingEnd ℂ (a₀ f)) * B f f := by dsimp only [d, a₀, B, lamP, lamQ]; ring
      _ = d * B f f := by rw [hPhase, mul_one]
  · intro g _ hgf
    rw [inducedInnerProduct_cutoff_ne hK' hL' νM' e' β' (fun h => hgf (hu' h).symm), mul_zero]
  · simp

end Langlands.Global
