import Langlands.Automorphic.GroupSchemeAutomorphicLeftTranslation
import Langlands.Global.AdelicEisensteinCentralCovariance
import Langlands.Global.EisensteinConstantTerm.Points
import Langlands.Global.AdelicEisensteinConjugateParabolicSeries
import Langlands.Global.AdelicEisensteinRegularityAmbientTransport
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Langlands.Global.AdelicRestrictionSplitCentreFiniteVolumeProof
import Langlands.Global.InducedInnerProductSesquilinearProof
import Langlands.Global.LeftCosetImageMajorant
import Langlands.Representation.Plancherel.UnramifiedRationalJacquetGeometryFiniteness
import Langlands.Global.AdelicNonAssociateWavePacketOrthogonality
import Langlands.Global.AdelicWavePacketCompletenessReduction
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyProof

/-! # Transport of full wave packets to a standard parabolic -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ContDiff

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Transport

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
  {a : A.toGrp ⟶ M} {K : Subgroup (AdelicGroupPoints F G)}
  (r : ParabolicRootPresentation p l a) (hK : IsIwasawaCompact p K)
  (s : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)

local notation "p'" => p ≫ Iso.hom (GroupScheme.innerIso G s)
local notation "t" => innerAdelicPoint F G s

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsClosedImmersion p.hom.hom.left] in
private theorem map_conjugate (x : AdelicGroupPoints F P) :
    map F P G p' x = t * map F P G p x * t⁻¹ := by
  rw [map_comp_apply_of_hom]
  exact affinePointsTarget_innerIso_hom F G s _

open InducedInnerProductSesquilinear in
omit [IsAffine U.X.left] [IsClosedImmersion p.hom.hom.left] in
private theorem inducingForm_conjugate {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
    {hsmooth : SmoothOfRelativeDimension d G.X.hom} {hcalc : AdelicDifferentialCommutator F G hsmooth}
    (r₀ : ParabolicRootPresentation p l a) (hRad : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hG : IsConnectedReductive G) (hK' : IsIwasawaCompact p' K) {v : AdelicGroupPoints F G → ℂ}
    (hv : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l v) :
    IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU l
      (fun x => v (t⁻¹ * x)) := by
  classical
  let v' : AdelicGroupPoints F G → ℂ := fun x => v (t⁻¹ * x)
  refine ⟨?_, ?_, ?_⟩
  · rw [parabolicQuotientSubgroup_conjugate s]
    simpa only [inv_inv] using hv.1.leftTranslate hcalc t⁻¹
  · intro x hx g
    change v' (map F P G p' (map F M P l x) * g) = _
    simp only [v', map_conjugate s]
    rw [show t⁻¹ * ((t * map F P G p (map F M P l x) * t⁻¹) * g) =
      map F P G p (map F M P l x) * (t⁻¹ * g) by group]
    exact hv.2.1 x hx _
  · let μK := compactHaarProbability F G K hK.isCompact
    let μM := RestrictionSplitCentre.canonicalMeasure F M
    let Γ := RestrictionSplitCentre.canonicalRationalSubgroup F M
    let w (m : AdelicGroupPoints F M) :=
      ‖parameterPower F P (-modulusParameter F P) (map F M P l m)‖
    let W (k : K) (m : AdelicGroupPoints F M) := normWeight p l v k m
    have hW (k : K) : ∀ x ∈ Γ, ∀ m, W k (x * m) = W k m := by
      apply LeftCosetSpace.invariant_sup (RestrictionSplitCentre.canonicalSubgroup F M)
        (Δ := rationalSubgroup F M)
      · exact fun x hx m => normWeight_splitComponent_mul hv.2.1 hx k m
      · exact fun x hx m => normWeight_rational_mul
          (fun a ha => hv.1.1 a (Subgroup.mem_sup_right ha)) hx k m
    obtain ⟨q, k, hk, htk⟩ := hK.exists_eq t⁻¹
    let k₀ : K := ⟨k, hk⟩
    let : Smooth G.X.hom := hG.smooth
    let : IsIso (subgroupMultiplication l iU) := r₀.isIso_subgroupMultiplication_of_radical hRad
    let m₀ : AdelicGroupPoints F M := (leviComponent l iU q⁻¹)⁻¹
    let u₀ : AdelicGroupPoints F U := (radicalComponent l iU q⁻¹)⁻¹
    have hq : q = map F U P iU u₀ * map F M P l m₀ := by
      have hh : map F M P l (leviComponent l iU q⁻¹) *
          map F U P iU (radicalComponent l iU q⁻¹) = q⁻¹ :=
        leviComponent_mul_radicalComponent l iU q⁻¹
      dsimp only [m₀, u₀]
      rw [map_inv, map_inv, ← mul_inv_rev, hh, inv_inv]
    let T : K × LeftCosetSpace Γ → K × LeftCosetSpace Γ :=
      Prod.map (k₀ * ·) (LeftCosetSpace.rightTranslate Γ m₀)
    have hM := r₀.isCompatible.levi.isConnectedReductive
    let : IsFiniteMeasure μM :=
      RestrictionSplitCentre.connectedReductiveQuotientFiniteVolume F M hM _ _
        (RestrictionSplitCentre.isSplitComponent_canonicalRestrictionComponent F M)
    have hT : MeasurePreserving T (μK.prod μM) (μK.prod μM) :=
      (measurePreserving_mul_left μK k₀).prod
        (RestrictionSplitCentre.canonicalMeasure_rightInvariant F M centralSplitTorusCharacter hM m₀)
    have hWi : Integrable (fun z : K × LeftCosetSpace Γ => W z.1 z.2.out) (μK.prod μM) := hv.2.2
    have hTm := (hT.integrable_comp_of_integrable hWi).const_mul (w m₀)⁻¹
    refine hTm.congr (Filter.Eventually.of_forall fun z => ?_)
    have hw (m : AdelicGroupPoints F M) : w (m * m₀) = w m * w m₀ := by
      simp only [w, map_mul, parameterPower_mul, norm_mul]
    have hw₀ : w m₀ ≠ 0 := norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)
    have hWout : W (k₀ * z.1) (LeftCosetSpace.rightTranslate Γ m₀ z.2).out =
        W (k₀ * z.1) (z.2.out * m₀) := by
      conv_lhs => rw [← LeftCosetSpace.mk_out Γ z.2, LeftCosetSpace.rightTranslate_mk]
      exact LeftCosetSpace.out_mk_of_invariant Γ (W (k₀ * z.1)) (hW (k₀ * z.1)) _
    have hu : map F P G p (map F U P iU u₀) ∈
        AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p)) :=
      ⟨u₀, map_comp_apply_of_hom iU u₀⟩
    have hu' := conj_mem_adelicPoints_range p iU hRad.1.isNormal (map F M P l z.2.out) hu
    have hvU : map F P G p (map F M P l z.2.out) * map F P G p (map F U P iU u₀) *
        (map F P G p (map F M P l z.2.out))⁻¹ ∈ parabolicQuotientSubgroup F p iU l := by
      obtain ⟨u, hu'⟩ := hu'
      exact Subgroup.mem_sup_left ⟨u, hu'⟩
    have hv' : v' (map F P G p' (map F M P l z.2.out) * (z.1 : AdelicGroupPoints F G)) =
        v (map F P G p (map F M P l (z.2.out * m₀)) * (↑(k₀ * z.1) : AdelicGroupPoints F G)) := by
      simp only [v', map_conjugate s, Subgroup.coe_mul, map_mul]
      rw [show t⁻¹ * ((t * map F P G p (map F M P l z.2.out) * t⁻¹) * ↑z.1) =
        map F P G p (map F M P l z.2.out) * t⁻¹ * ↑z.1 by group, ← htk, hq, map_mul]
      rw [show map F P G p (map F M P l z.2.out) *
          ((map F P G p (map F U P iU u₀) * map F P G p (map F M P l m₀)) * k) * ↑z.1 =
          (map F P G p (map F M P l z.2.out) * map F P G p (map F U P iU u₀) *
            (map F P G p (map F M P l z.2.out))⁻¹) *
          ((map F P G p (map F M P l z.2.out) * map F P G p (map F M P l m₀)) *
            (k * ↑z.1)) by group, hv.1.1 _ hvU]
    change (w m₀)⁻¹ * W (k₀ * z.1) (LeftCosetSpace.rightTranslate Γ m₀ z.2).out =
      w z.2.out * ‖v' (map F P G p' (map F M P l z.2.out) * ↑z.1)‖ ^ 2
    rw [hWout, hv']
    change (w m₀)⁻¹ * (w (z.2.out * m₀) * _) = _
    rw [hw]
    field_simp

variable [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]

omit [IsAffine U.X.left] in
/-- Conjugation of the parabolic preserves its full packet functions for the same compact.
The coefficients absorb the exponential scalar of the conjugated Eisenstein series. -/
theorem IsParabolicWavePacket.conjugate_parabolic
    [IsClosedImmersion (p ≫ (G.innerIso s).hom).hom.hom.left]
    [Mono (r.compAmbientIso (G.innerIso s)).data.i.hom.hom.left]
    [Fintype (relativeWeylGroup (r.compAmbientIso (G.innerIso s)).data.i)]
    (hG : IsConnectedReductive G) (hK' : IsIwasawaCompact p' K)
    {N d : ℕ} {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth}
    (hRad : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    {Θ : AdelicGroupPoints F G → ℂ}
    (hΘ : IsParabolicWavePacket hK rho hsmooth hcalc iU l r hA hT Θ) :
    haveI : Mono (CommGroupScheme.groupHom (r.compAmbientIso (G.innerIso s)).data.f).hom.hom.left :=
      inferInstanceAs (Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left)
    IsParabolicWavePacket hK' rho hsmooth hcalc iU l (r.compAmbientIso (G.innerIso s)) hA hT Θ := by
  obtain ⟨n, e, k, v, c, E, D, hv, hc, hD, hE, ha, hΘ⟩ := hΘ
  let v' (j : Fin k) (x : AdelicGroupPoints F G) := v j (t⁻¹ * x)
  obtain ⟨q, z, hz, ht⟩ := hK'.exists_eq t
  have hheight (lam : ComplexCharacterParameter F P) :
      hK'.heightPower lam t = parameterPower F P lam q := by
    rw [IsIwasawaCompact.heightPower, hK'.height_eq hz ht, parameterPower]
  let L : (Fin n → ℝ) →ₗ[ℝ] ℂ :=
    (((complexParameterPairing F P).flip (characterLog F P q)).restrictScalars ℝ).comp
      ((imaginaryParameter F P).comp e.toLinearMap)
  let c' (j : Fin k) (x : Fin n → ℝ) := c j x * Complex.exp (-L x)
  let E' (j : Fin k) (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :=
    parameterPower F P lam q * E j lam g
  refine ⟨n, e, k, v', c', E', D, fun j => inducingForm_conjugate hK s r hRad hG hK' (hv j),
    ?_, hD, ?_, ?_, ?_⟩
  · intro j
    have hL : ContDiff ℝ (⊤ : ℕ∞) L := L.toContinuousLinearMap.contDiff
    exact ⟨(hc j).1.mul hL.neg.cexp, (hc j).2.mul_right⟩
  · intro j g
    let : FiniteDimensional ℂ (ComplexCharacterParameter F P) := (hE j g).1
    simpa only [Set.univ_inter, E', Pi.mul_def] using
      (isMeromorphicInCoordinatesOn_parameterPower q).mul (hE j g)
  · intro j
    obtain ⟨R, hR⟩ := ha j
    refine ⟨R, fun lam hlam => ?_⟩
    have hlam' := (eisensteinRegularityAmbientTransport F G G P M A p l a r
      (G.innerIso s) hA hT R lam).mp hlam
    funext g
    exact (congrArg (fun E₀ : AdelicGroupPoints F G → ℂ => parameterPower F P lam q * E₀ g)
      (hR lam hlam')).trans (by
        rw [← hheight lam]
        exact (hK.eisensteinSeries_conjugate_parabolic s hK' r.isCompatible.levi hRad
          (hv j).1.1 lam g).symm)
  · rw [hΘ]
    funext g
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    apply Finset.sum_congr rfl
    intro j _
    have hcancel : Complex.exp (-L x) * parameterPower F P (imaginaryParameter F P (e x)) q = 1 := by
      change Complex.exp (-L x) * Complex.exp (L x) = 1
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    change c j x * E j (imaginaryParameter F P (e x)) g =
      c j x * Complex.exp (-L x) *
        (parameterPower F P (imaginaryParameter F P (e x)) q * E j (imaginaryParameter F P (e x)) g)
    rw [mul_assoc (c j x), ← mul_assoc (Complex.exp (-L x)), hcancel, one_mul]

end Transport

section Standard

variable {F : Type} [Field F] [NumberField F]
  {G P₀ : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (p₀ : P₀ ⟶ G) (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
  (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

/-- A full wave packet for a presented parabolic containing the specified minimal parabolic.
The inducing data, compact and spectral parameters are those of `IsWavePacket`. -/
def IsStandardWavePacket (Θ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∃ (P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    (_ : IsAffine P.X.left) (_ : IsAffine M.X.left) (_ : LocallyOfFiniteType M.X.hom)
    (_ : IsAffine U.X.left)
    (p : P ⟶ G) (_ : IsClosedImmersion p.hom.hom.left) (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    (_ : Mono r.data.i.hom.hom.left) (_ : Fintype (relativeWeylGroup r.data.i))
    (_ : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left)
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p ∧
    LeviSubgroup.IsGeometricUnipotentRadical iU ∧
    ∃ hK : IsIwasawaCompact p K, IsParabolicWavePacket hK rho hsmooth hcalc iU l r hA hT Θ

end Standard

/-- Each full packet is a packet of a presented parabolic above the specified minimal parabolic,
with the same compact subgroup and the same packet function. -/
def StandardWavePacketTransportStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P₀ : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (p₀ : P₀ ⟶ G), IsMinimalParabolicSubgroup p₀ →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (Θ : AdelicGroupPoints F G → ℂ),
      IsWavePacket F G K rho hsmooth hcalc Θ → IsStandardWavePacket p₀ K rho hsmooth hcalc Θ

/-- The presentation supplies a minimal parabolic inside its inducing parabolic. Rational
conjugacy moves that minimal parabolic to the prescribed one. -/
theorem standardWavePacketTransport : StandardWavePacketTransportStatement := by
  intro F _ _ G P₀ _ _ _ hG p₀ hmin K N d rho hsmooth hcalc Θ hΘ
  obtain ⟨P, M, U, A, _, _, _, _, p, _, iU, l, _, a, r, _, _, _, hA, hT, hU, hK, hΘ⟩ := hΘ
  obtain ⟨Q, q, hq, _, hqp⟩ := r.exists_minimalParabolic
  obtain ⟨s, e, he⟩ := minimalParabolicConjugacy F G hG Q P₀ q p₀ hq hmin
  let E := G.innerIso s
  let p' := p ≫ E.hom
  let r' := r.compAmbientIso E
  have : IsIso E.hom.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso E)).hom)
  let : IsClosedImmersion p'.hom.hom.left := by
    change IsClosedImmersion (p.hom.hom.left ≫ E.hom.hom.hom.left)
    infer_instance
  let : Mono r'.data.i.hom.hom.left := r'.isCompatible.maximalSplit.isSplitSubtorus.mono
  let : Fintype (relativeWeylGroup r'.data.i) :=
    @Fintype.ofFinite _ (hG.finite_relativeWeylGroup r'.data.i r'.isCompatible.maximalSplit)
  let : Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left :=
    inferInstanceAs (Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left)
  let hK' : IsIwasawaCompact p' K := hK.of_conjugate_map (map_conjugate s)
  have hle : SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p' := by
    calc
      SubgroupFunctor.range p₀ = SubgroupFunctor.range (q ≫ E.hom) := by
        rw [he, SubgroupFunctor.range_iso_comp]
      _ ≤ SubgroupFunctor.range p' := by
        dsimp only [p']
        rw [SubgroupFunctor.range_comp_iso, SubgroupFunctor.range_comp_iso]
        exact SubgroupFunctor.comap_mono hqp
  let : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have hΘ' : IsParabolicWavePacket hK rho hsmooth hcalc iU l r hA hT Θ := hΘ
  exact ⟨P, M, U, A, inferInstance, inferInstance, inferInstance, inferInstance, p', inferInstance,
    iU, l, a, r', inferInstance, inferInstance, inferInstance, hA, hT, hle, hU, hK',
    IsParabolicWavePacket.conjugate_parabolic r hK s hG hK' hU hA hT hΘ'⟩

end Langlands.Global
