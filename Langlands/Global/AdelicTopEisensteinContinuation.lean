import Langlands.Global.AdelicGroupParabolicSpectrumReduction
import Langlands.Global.AdelicWeakConstantTermTop
import Langlands.Global.AdelicIntertwiningNormalizedLevi
import Langlands.Global.AdelicParameterTwistAutomorphyReduction
import Langlands.Global.AdelicParameterTwistCenterFiniteReduction

/-! # The Eisenstein continuation at the full-group parabolic -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct ContDiff Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions InfiniteAdelicGroupPoints

namespace AdelicGroupPoints

variable {F : Type} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] [IsIso p]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

/-- On a full parabolic the Iwasawa power is an ambient character power. -/
theorem IsIwasawaCompact.heightPower_eq_parameterPower_of_isIso
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.heightPower lam g = parameterPower F G (parameterRestrict (inv p) lam) g := by
  let y := map F G P (inv p) g
  have hy : map F P G p y = g := by
    change map F P G p (map F G P (inv p) g) = _
    rw [← map_comp_apply_of_hom, IsIso.inv_hom_id]
    change g ≫ 𝟙 G.X = g
    exact Category.comp_id _
  have hH : hK.height g = characterLog F P y := hy ▸ hK.height_map y
  rw [IsIwasawaCompact.heightPower, hH, parameterPower_pullback]
  rfl

/-- The full-group height twist is multiplicative on adelic points. -/
theorem IsIwasawaCompact.heightPower_mul_of_isIso (lam : ComplexCharacterParameter F P)
    (x y : AdelicGroupPoints F G) :
    hK.heightPower lam (x * y) = hK.heightPower lam x * hK.heightPower lam y := by
  simp only [hK.heightPower_eq_parameterPower_of_isIso, parameterPower, characterLog_mul, map_add,
    Complex.exp_add]

variable [LocallyOfFiniteType G.X.hom] {d : ℕ}
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

set_option maxHeartbeats 1500000 in
/-- Multiplication by the full-group Iwasawa power preserves center finiteness.
The infinite factor is a smooth character, so one contracts the annihilator ideal
along its enveloping-center shift. -/
theorem IsIwasawaCompact.isCenterFiniteFunction_parameterTwist_of_isIso
    (hmax : IsMaximalCompactSubgroup F G K)
    {φ : AdelicGroupPoints F G → ℂ} (hsm : IsAdelicSmoothFunction F G φ)
    (hφ : IsCenterFiniteFunction F G hsmooth hcalc φ) (lam : ComplexCharacterParameter F P) :
    IsCenterFiniteFunction F G hsmooth hcalc (hK.parameterTwist φ lam) := by
  obtain ⟨I, hI, hkill⟩ := hφ
  let χ : InfiniteAdelicGroupPoints F G → ℂ := fun x => hK.heightPower lam (ofInfinite F G x)
  have hχ : χ ∈ InfinitePlotSmoothFunctions F G := by
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    have hH := hK.hasSmoothHeightPairings_of_maximalCompact hsmooth hmax lam 1
    exact (isPlotSmooth_iff_contMDiff F G hsmooth χ).mpr
      ((Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)).contMDiff.comp hH)
  have hmul (x y : InfiniteAdelicGroupPoints F G) : χ (x * y) = χ x * χ y := by
    simp only [χ, map_mul, hK.heightPower_mul_of_isIso]
  have hone : χ 1 = 1 := by
    simp only [χ, map_one, hK.heightPower_one]
  obtain ⟨θ, hθ⟩ := exists_centerShift_plotSmoothMultiplication F G hsmooth hcalc χ hχ hmul hone
  refine ⟨I.comap θ.toRingHom, ?_, ?_⟩
  · let : Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ I) :=
      (Module.Finite.equiv_iff (Submodule.Quotient.restrictScalarsEquiv ℂ I)).mp hI
    exact (Module.Finite.equiv_iff (Submodule.Quotient.restrictScalarsEquiv ℂ _)).mpr
      (Langlands.Algebra.quotientFinite_comap θ I)
  · intro z hz b hb
    let f : InfinitePlotSmoothFunctions F G := ⟨_, hsm.2.1 b⟩
    let s := hK.heightPower lam (ofFinite F G b)
    let L := plotSmoothMultiplication F G χ hχ
    have hfl : (⟨functionInfiniteSlice F G (hK.parameterTwist φ lam) b, hb⟩ :
        InfinitePlotSmoothFunctions F G) = s • L f := by
      apply Subtype.ext
      funext x
      change φ (pair F G x b) * hK.heightPower lam (pair F G x b) =
        s * (χ x * φ (pair F G x b))
      rw [hK.heightPower_pair hmax]
      dsimp [s, χ]
      ring
    have hk : plotSmoothCenterAction F G hsmooth hcalc (θ z) f = 0 :=
      hkill (θ z) hz b (hsm.2.1 b)
    rw [hfl, map_smul]
    change s • plotSmoothCenterAction F G hsmooth hcalc z
      (plotSmoothMultiplication F G χ hχ f) = 0
    rw [hθ, hk, map_zero, smul_zero]

/-- The full-group height twist of an automorphic function is automorphic. -/
theorem IsIwasawaCompact.isAutomorphicFunctionOn_parameterTwist_of_isIso
    (hmax : IsMaximalCompactSubgroup F G K)
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hrho : IsClosedSubgroup rho)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ) (lam : ComplexCharacterParameter F P) :
    IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
      (K.comap (ofInfinite F G).toMonoidHom) rho (hK.parameterTwist φ lam) := by
  obtain ⟨hleft, hsm, hfin, hcen, hgrowth⟩ := hφ
  refine ⟨?_, hK.isAdelicSmoothFunction_parameterTwist hmax hsmooth hsm lam,
    hK.isInfiniteSubgroupFiniteFunction_parameterTwist hfin lam,
    hK.isCenterFiniteFunction_parameterTwist_of_isIso hsmooth hcalc hmax hsm hcen lam,
    hK.hasModerateGrowthFunction_parameterTwist rho hrho hgrowth lam⟩
  rintro _ ⟨q, rfl⟩ g
  change φ (rational F G q * g) * hK.heightPower lam (rational F G q * g) = _
  rw [hleft _ ⟨q, rfl⟩, ← map_rational_inv_of_isIso (p := p) q,
    hK.heightPower_rational_mul]
  rfl

end AdelicGroupPoints

namespace StandardParabolicFamily

open RestrictionSplitCentre (canonicalSubgroup map_mem_canonicalSubgroup)

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "P" => fam.P fam.top
local notation "M" => fam.M fam.top
local notation "pG" => fam.p fam.top
local notation "lG" => fam.l fam.top
local notation "uG" => fam.iU fam.top
local notation "aG" => fam.a fam.top

omit [NumberField F] in
private theorem topParabolicRep : (⊤ : SubgroupFunctor G).IsRepresentedBy pG := by
  have h := standardParabolicEndpoints F G fam.connectedReductive fam.T fam.i fam.maximalSplit
    fam.ν fam.generic
  rw [← (fam.isCompatible fam.top).parabolic_eq.trans h.2.2.1]
  exact (fam.isCompatible fam.top).parabolic.isClosedSubgroup.isRepresentedBy_range

omit [NumberField F] in
private theorem topLeviRep : (⊤ : SubgroupFunctor G).IsRepresentedBy (lG ≫ pG) := by
  have h := standardParabolicEndpoints F G fam.connectedReductive fam.T fam.i fam.maximalSplit
    fam.ν fam.generic
  rw [← (fam.isCompatible fam.top).levi_eq.trans h.2.2.2.1]
  exact ((fam.isCompatible fam.top).levi.isClosedSubgroup.comp
    (fam.isCompatible fam.top).parabolic.isClosedSubgroup).isRepresentedBy_range

omit [NumberField F] in
/-- The presented full parabolic is isomorphic to the ambient group. -/
theorem isIso_topParabolic : IsIso pG := by
  rw [← fam.topParabolicRep.topIso_hom]
  infer_instance

omit [NumberField F] in
/-- The presented full Levi is isomorphic to the ambient group. -/
theorem isIso_topLevi : IsIso (lG ≫ pG) := by
  rw [← fam.topLeviRep.topIso_hom]
  infer_instance

omit [NumberField F] in
theorem halfModulusParameter_top_eq_zero : halfModulusParameter F P = 0 := by
  have hred := fam.connectedReductive.of_iso fam.topParabolicRep.topIso
  rw [halfModulusParameter, Lie.connectedReductiveAdjointDeterminant F _ hred,
    TensorProduct.tmul_zero]

variable {K : Subgroup (AdelicGroupPoints F G)} {N d : ℕ}
  {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  {hcalc : AdelicDifferentialCommutator F G hsmooth}
  (hK : IsIwasawaCompact (fam.p fam.top) K) {φ : AdelicGroupPoints F G → ℂ}

set_option quotPrecheck false in
local notation "Kinf" => K.comap (ofInfinite F G).toMonoidHom
local instance : IsClosedImmersion (pG).hom.hom.left := fam.isClosedImmersion_p fam.top
local instance : IsIso pG := fam.isIso_topParabolic

/-- A square-integrable full-group inducing form is rational-invariant and has trivial
character on the positive split centre. -/
theorem topInducingInvariance
    (hφ : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc pG uG lG φ) :
    IsLeftInvariantUnder F G (rationalSubgroup F G) φ ∧
      IsLeftInvariantUnder F G (canonicalSubgroup F G) φ := by
  let e := fam.topLeviRep.topIso
  have he : e.hom = lG ≫ pG := fam.topLeviRep.topIso_hom
  constructor
  · rintro _ ⟨q, rfl⟩ g
    have hq : rational F G q ∈ parabolicLeviRationalImage F pG lG := by
      refine ⟨G.affinePointsTarget (inv e.hom) (CommAlgCat.of F F) q, ?_⟩
      change map F M G (lG ≫ pG) (rational F M (G.affinePointsTarget (inv e.hom) _ q)) = _
      rw [← he]
      exact map_rational_inv_of_isIso (p := e.hom) q
    exact hφ.1.1 _ (Subgroup.mem_sup_right hq) g
  · intro x hx g
    let y := map F G M e.inv x
    have hy : y ∈ canonicalSubgroup F M := map_mem_canonicalSubgroup e.symm hx
    have hxy : map F M G e.hom y = x := by
      change map F M G e.hom (map F G M e.inv x) = _
      rw [← map_comp_apply_of_hom, e.inv_hom_id]
      change x ≫ 𝟙 G.X = x
      exact Category.comp_id _
    have heq := hφ.2.1 y hy g
    rw [fam.halfModulusParameter_top_eq_zero, InducedInnerProductIntegrable.parameterPower_zero,
      one_mul, ← map_comp_apply_of_hom, ← he, hxy] at heq
    exact heq

/-- The image of the positive split component of the full parabolic is the
canonical positive split centre of `G`. -/
theorem topPositive_mem_canonical {x : AdelicGroupPoints F P}
    (hx : x ∈ fam.positiveSplitComponent fam.top) :
    map F P G pG x ∈ canonicalSubgroup F G := by
  let e := fam.topLeviRep.topIso
  have he : e.hom = lG ≫ pG := fam.topLeviRep.topIso_hom
  obtain ⟨t, ht, rfl⟩ := hx
  have hmem : map F (fam.A fam.top).toGrp M aG t ∈ canonicalSubgroup F M := by
    rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup (fam.isCompatible fam.top).splitComponent]
    exact ⟨t, ht, rfl⟩
  have h := map_mem_canonicalSubgroup e hmem
  rw [he, ← map_comp_apply_of_hom, ← Category.assoc, map_comp_apply_of_hom] at h
  exact h

/-- At the full-group index a continuation agreeing on the regular region is the
one-term twist everywhere. At imaginary parameters it is its own weak constant term. -/
def TopEisensteinContinuationStatement : Prop :=
  IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
  IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc pG uG lG φ →
  ∀ (r : ParabolicRootPresentation pG lG aG) [Mono r.data.i.hom.hom.left]
    [Fintype (relativeWeylGroup r.data.i)] [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus (fam.A fam.top).toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ),
    (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam) →
    (∀ lam, E lam = hK.parameterTwist φ lam) ∧
    ∀ x : RealCharacterParameter F P,
      let f := E (imaginaryParameter F P x)
      fam.IsWeakConstantTerm hsmooth Kinf rho fam.top f f

set_option maxHeartbeats 1500000 in
theorem topEisensteinContinuation : fam.TopEisensteinContinuationStatement hK (φ := φ) (rho := rho)
    (hsmooth := hsmooth) (hcalc := hcalc) := by
  intro hmax hrho hφ r _ _ _ hA hT E hE
  obtain ⟨R, hR⟩ := hE
  have heq (lam : ComplexCharacterParameter F P) : E lam = hK.parameterTwist φ lam := by
    have hreg : r.IsRegularParameter hA hT R lam := by
      intro α hα
      rw [r.unipotentRoots_eq_empty_of_isIso fam.connectedReductive] at hα
      exact hα.elim
    rw [hR lam hreg]
    funext g
    have hl : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F pG uG lG) φ := hφ.1.1
    exact hK.eisensteinSeries_of_isIso (iU := uG) (l := lG) hl (fam.isCompatible fam.top).levi
      (fam.isUnipotentRadical fam.top) lam g
  refine ⟨heq, fun x => ?_⟩
  obtain ⟨hrat, hcent⟩ := fam.topInducingInvariance hK hφ
  have hφaut : IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G) Kinf rho φ :=
    ⟨hrat, hφ.1.2⟩
  let lam := imaginaryParameter F P x
  have haut := hK.isAutomorphicFunctionOn_parameterTwist_of_isIso hsmooth hcalc hmax rho hrho hφaut lam
  let ν := realCharacterParameterPullback (inv pG) x
  have hν (b : AdelicGroupPoints F G) (hb : b ∈ canonicalSubgroup F G) (g : AdelicGroupPoints F G) :
      hK.parameterTwist φ lam (b * g) =
        parameterPower F G (imaginaryParameter F G ν) b * hK.parameterTwist φ lam g := by
    change φ (b * g) * hK.heightPower lam (b * g) = _ * (φ g * hK.heightPower lam g)
    rw [hcent b hb g, hK.heightPower_mul_of_isIso, hK.heightPower_eq_parameterPower_of_isIso lam b,
      show imaginaryParameter F G ν = parameterRestrict (inv pG) lam from imaginaryParameter_pullback _]
    exact mul_left_comm _ _ _
  change fam.IsWeakConstantTerm hsmooth Kinf rho fam.top (E lam) (E lam)
  rw [heq lam]
  exact fam.isWeakConstantTerm_top_of_unitary haut ν hν

end StandardParabolicFamily

end Langlands.Global
