import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSourceConstants
import Langlands.Representation.Plancherel.StandardLeviPlancherelWeight

/-! # Actual Plancherel density on every intrinsic semistandard orbit -/

noncomputable section

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General
open Langlands.Plancherel.UnramifiedOperatorFamily
open Langlands.Plancherel.DynamicOppositeStandardIntertwining
open Langlands.Plancherel.DynamicOppositeCanonicalScalar
open Langlands.Plancherel.RationalDynamicSource Langlands.Plancherel.RationalPlancherelDensity

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.SourceDensity

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  {t : SemistandardSpectralIndex i} {hG : IsConnectedReductive G}
  (model : LeviModel t) (r : CocharacterPresentation hG t)

local instance modelAffineHom : IsAffineHom model.scheme.X.hom := model.reductive.isAffineHom
local instance modelAffine : IsAffine model.scheme.X.left := isAffine_of_isAffineHom model.scheme.X.hom
local instance modelSmooth : Smooth model.scheme.X.hom := model.reductive.smooth
local instance modelFiniteType : LocallyOfFiniteType model.scheme.X.hom := inferInstance
local instance modelTopology : TopologicalSpace (rationalPoints model.scheme) :=
  rationalPointTopology F model.scheme.X

set_option hygiene false in
local notation "χ" => (CommGroupScheme.groupHom r.cocharacter ≫ i)
set_option hygiene false in
local notation "MS" => parameterScheme (CommGroupScheme.groupHom r.cocharacter ≫ i)
set_option hygiene false in
local notation "MI" => model.scheme
set_option hygiene false in
local notation "νL" => normCharacters (CommGroupScheme.groupHom r.cocharacter ≫ i)
set_option hygiene false in
local notation "UL" => unitaryUnramifiedCharacters
  (fun ψ => (rationalNormCharacters (parameterScheme (CommGroupScheme.groupHom r.cocharacter ≫ i)) ψ).toMul)
set_option hygiene false in
local notation "UMI" => unitaryUnramifiedCharacters model.normCharacters
set_option hygiene false in
local notation "hMS" => parameterScheme_isConnectedReductive (CommGroupScheme.groupHom r.cocharacter ≫ i) hG
set_option hygiene false in
local notation "𝐌" => levi t

/-- The unique actual model comparison over the ambient group. -/
def parameterIso : MS ≅ MI := r.leviModel.schemeIso model

/-- The model comparison commutes with the original inclusions into G. -/
theorem parameterIso_hom_comp :
    (parameterIso model r).hom ≫ model.inclusion = Dynamic.Affine.centralizerHom χ :=
  r.leviModel.schemeIso_hom_comp model

/-- The point maps of `Z_G(ζ ∘ i) ≅ M` and of the two inclusions into `G` agree. -/
theorem pointHomeomorph_map_parameterIso
    (m : rationalPoints MS) :
    model.pointHomeomorph
        (rationalPoints.map (parameterIso model r).hom m) =
      r.literalLeviHomeomorph (parameterHomeomorph χ m) := by
  apply Subtype.ext
  change (m ≫ (parameterIso model r).hom.hom.hom) ≫
      (model.inclusion).hom.hom =
    m ≫ (Dynamic.Affine.centralizerHom χ).hom.hom
  rw [Category.assoc, ← Grp.comp_hom_hom, parameterIso_hom_comp]

/-- **Restriction `Im X(M) → Im X(Z_G(ζ ∘ i))`**: a unitary unramified character `z` of the
literal Levi subgroup `M(F)` gives the character `z ∘ e` of the centralizer scheme's points,
where `e : Z_G(ζ ∘ i)(F) ≅ M(F)` is the canonical identification. -/
def characterRestrict : UMI →ₜ* UL :=
  (rationalUnitaryUnramifiedCharacterRestrict (parameterIso model r).hom).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (HarishChandraSchwartz.unitaryUnramifiedCharactersHomeomorph
        (model.pointHomeomorph)
        (fun ψ => (rationalNormCharacters MI ψ).toMul)).symm)

/-- The restricted character is `z ∘ e`. -/
theorem characterRestrict_apply (z : UMI) (m : rationalPoints MS) :
    (characterRestrict model r z).val m =
      z.val (r.literalLeviHomeomorph (parameterHomeomorph χ m)) := by
  change z.val (model.pointHomeomorph
    (rationalPoints.map (parameterIso model r).hom m)) = _
  rw [pointHomeomorph_map_parameterIso]

/-- **Smoothness transfers along the restriction.** A function on `Im X(Z_G(ζ ∘ i))` smooth in
the Library's canonical circle coordinates becomes, after restriction from `Im X(M)`, smooth in
the actual model circle coordinates of `Im X(M)`. -/
theorem isSmoothFiniteTorusFunction_comp_characterRestrict {f : UL → ℂ}
    (hf : IsSmoothFiniteTorusFunction fun c =>
      f ((rationalCanonicalUnitaryUnramifiedCharacterCoordinates MS hMS).symm c)) :
    IsSmoothFiniteTorusFunction fun y =>
      f (characterRestrict model r
        ((model.unitaryCoordinates).toMulEquiv.symm y)) :=
  isSmoothFiniteTorusFunction_comp_pullback
    (rationalCanonicalUnitaryUnramifiedCharacterCoordinates MS hMS).toMulEquiv
    (exists_rationalCanonicalUnitaryCoordinate_eq_eval MS hMS)
    (model.unitaryCoordinates).toMulEquiv
    (model.unitaryCoordinates_hasLaurent)
    (characterRestrict model r)
    (fun m => r.literalLeviHomeomorph (parameterHomeomorph χ m))
    (characterRestrict_apply model r) hf

/-! ### Weights on the orbit of a discrete series of `M` -/

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

-- The inducing representation `π ∘ e` of `Z_G(ζ ∘ i)(F)`.
set_option hygiene false in
local notation "Aπ" => SmoothRep.pullback (r.literalLeviHomeomorph) π.obj
-- The orbit `O = {π ⊗ z ; z ∈ Im X(M)}` of the class of `π`.
set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit C hC mu
  (model.normCharacters) (discreteSeriesClass C hC mu π hsq)
set_option hygiene false in
local notation "orbitMapπ" => discreteSeriesOrbitMap C hC mu
  (model.normCharacters) (discreteSeriesClass C hC mu π hsq)

/-- A unitary unramified character `s` of `M(F)` with `π ⊗ s ≅ π` restricts to a self-twist
of the inducing representation `π ∘ e` of `Z_G(ζ ∘ i)(F)`. -/
theorem characterRestrict_mem_stabilizer {s : UMI}
    (hs : s ∈ discreteSeriesStabilizer C hC mu
      (model.normCharacters) (discreteSeriesClass C hC mu π hsq)) :
    (⟨(characterRestrict model r s).val,
      (characterRestrict model r s).property.1⟩ : unramifiedCharacters νL) ∈
      smoothRepUnramifiedTwistStabilizer νL (SmoothRep.pullback (parameterHomeomorph χ) Aπ) := by
  obtain ⟨a⟩ := nonempty_twistEquiv_of_mem_discreteSeriesStabilizer C hC mu
    (model.normCharacters) π hsq hs
  exact (SmoothRep.isoClass_eq_iff _ _).mpr
    (nonempty_twist_pullback_pullback_iso (parameterHomeomorph χ)
      (r.literalLeviHomeomorph) π.obj
      (ψ := s.val.toMonoidHom)
      (τ := (characterRestrict model r s).val.toMonoidHom) _ _
      (characterRestrict_apply model r s) a)

/-- **A weight on the orbit of `π`.** A function `W` on `Im X(Z_G(ζ ∘ i))` invariant under
translation by the unitary self-twists of the inducing representation `π ∘ e` gives the function
`π ⊗ z ↦ W(z ∘ e)` on the orbit `O` of `π`. -/
def orbitWeight (W : UL → ℂ)
    (hW : ∀ (τ : smoothRepUnramifiedTwistStabilizer νL
        (SmoothRep.pullback (parameterHomeomorph χ) Aπ))
      (hτ : τ.val.val ∈ unitaryCharacters (GroupScheme.rationalPoints MS)) (z : UL),
      W (⟨τ.val.val, τ.val.property, hτ⟩ * z) = W z) : Oπ → ℂ :=
  discreteSeriesOrbitDescend C hC mu (model.normCharacters) π hsq
    (fun z => W (characterRestrict model r z))
    (fun s hs z => by
      have h := hW ⟨_, characterRestrict_mem_stabilizer model r π C hC mu hsq hs⟩
        (characterRestrict model r s).property.2
        (characterRestrict model r z)
      change W (characterRestrict model r (z * s)) =
        W (characterRestrict model r z)
      rw [map_mul, mul_comm]
      exact h)

/-- The weight at `π ⊗ z` is `W(z ∘ e)`. -/
theorem orbitWeight_orbitMap (W : UL → ℂ)
    (hW : ∀ (τ : smoothRepUnramifiedTwistStabilizer νL
        (SmoothRep.pullback (parameterHomeomorph χ) Aπ))
      (hτ : τ.val.val ∈ unitaryCharacters (GroupScheme.rationalPoints MS)) (z : UL),
      W (⟨τ.val.val, τ.val.property, hτ⟩ * z) = W z) (z : UMI) :
    orbitWeight model r π C hC mu hsq W hW (orbitMapπ z) =
      W (characterRestrict model r z) :=
  discreteSeriesOrbitDescend_orbitMap C hC mu _ π hsq _ _ z

/-- **Smoothness in the circle coordinates of `Im X(M)`**, in the form required by the
coefficient integration interfaces: if `W` is
smooth in the Library's canonical circle coordinates of `Im X(Z_G(ζ ∘ i))`, the orbit weight
composed with the orbit map is smooth in the coordinates `the actual model circle coordinates`. -/
theorem isSmoothFiniteTorusFunction_orbitWeight (W : UL → ℂ)
    (hW : ∀ (τ : smoothRepUnramifiedTwistStabilizer νL
        (SmoothRep.pullback (parameterHomeomorph χ) Aπ))
      (hτ : τ.val.val ∈ unitaryCharacters (GroupScheme.rationalPoints MS)) (z : UL),
      W (⟨τ.val.val, τ.val.property, hτ⟩ * z) = W z)
    (hWs : IsSmoothFiniteTorusFunction fun c =>
      W ((rationalCanonicalUnitaryUnramifiedCharacterCoordinates MS hMS).symm c)) :
    IsSmoothFiniteTorusFunction fun y =>
      orbitWeight model r π C hC mu hsq W hW
        (orbitMapπ ((model.unitaryCoordinates).toMulEquiv.symm
          y)) := by
  have h : (fun y => orbitWeight model r π C hC mu hsq W hW
      (orbitMapπ ((model.unitaryCoordinates).toMulEquiv.symm
        y))) = fun y => W (characterRestrict model r
          ((model.unitaryCoordinates).toMulEquiv.symm y)) := by
    funext y
    exact orbitWeight_orbitMap model r π C hC mu hsq W hW _
  rw [h]
  exact isSmoothFiniteTorusFunction_comp_characterRestrict model r hWs

/-- The orbit weight of a continuous `W` is continuous on `O`. -/
theorem continuous_orbitWeight {W : UL → ℂ}
    (hW : ∀ (τ : smoothRepUnramifiedTwistStabilizer νL
        (SmoothRep.pullback (parameterHomeomorph χ) Aπ))
      (hτ : τ.val.val ∈ unitaryCharacters (GroupScheme.rationalPoints MS)) (z : UL),
      W (⟨τ.val.val, τ.val.property, hτ⟩ * z) = W z) (hWc : Continuous W) :
    Continuous (orbitWeight model r π C hC mu hsq W hW) :=
  continuous_discreteSeriesOrbitDescend C hC mu _ π hsq _
    (hWc.comp (characterRestrict model r).continuous)

/-! ### The Plancherel weight on the orbit of `π` -/


variable
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : DynamicOppositeStandardIntertwining.parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK Aπ)
  (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK Aπ)
  {DForward DReverse : Set (unramifiedCharacters νL)}
  (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK Aπ)
  (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK Aπ)
  {D : Set (unramifiedCharacters νL)}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hirr : ∀ z ∈ D,
    (UnramifiedLeviInduction (DynamicOppositeStandardIntertwining.decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) Aπ).IsIrreducible)

-- The canonical scalar `j_P` of the inducing representation `π ∘ e`.
set_option hygiene false in
local notation "jP" => conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK Aπ
  p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hirr

include hDForward hDReverse hD in
/-- **The Plancherel weight on the orbit of `π`** (Waldspurger V.2, V.2.1, printed p.292):
`π ⊗ z ↦ μ(π ⊗ z)`, where `μ` is the Plancherel density of the inducing representation
`π ∘ e` of `Z_G(ζ ∘ i)(F)` and `z ∈ Im X(M)` acts through the restriction `z ↦ z ∘ e`.
It is well defined because the Plancherel weight is invariant under unitary self-twists of
`π ∘ e` (`plancherelWeight_stabilizer_invariant`); it is defined under the hypothesis that `j_P⁻¹`
is regular at every unitary unramified character. -/
def orbitPlancherelWeight (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) :
    Oπ → ℂ :=
  orbitWeight model r π C hC mu hsq
    (plancherelWeight i r.cocharacter hRefl hCST hG K hK hPK hOppK Aπ p q hneForward hDForwardΩ hneReverse
      hDReverseΩ hne hirr hreg)
    (by
      intro tau htau z
      exact plancherelWeight_stabilizer_invariant i r.cocharacter hRefl hCST hG K hK hPK hOppK
        Aπ p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr
        hreg tau htau z)

/-- The Plancherel weight at `π ⊗ z` is the Plancherel weight of `π ∘ e` at `z ∘ e`. -/
theorem orbitPlancherelWeight_orbitMap
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) (z : UMI) :
    orbitPlancherelWeight model r π C hC mu hsq hRefl hCST K hK hPK hOppK p q
        hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
        (orbitMapπ z) =
      plancherelWeight i r.cocharacter hRefl hCST hG K hK hPK hOppK Aπ p q hneForward hDForwardΩ hneReverse
        hDReverseΩ hne hirr hreg (characterRestrict model r z) :=
  orbitWeight_orbitMap model r π C hC mu hsq _ _ z

/-- **Smoothness**, in the form required by the wave-packet bound
`exists_norm_rationalInducedOrbitWavePacket_le_rationalXi_rpow`: the Plancherel weight composed
with the orbit map is smooth in the actual model circle coordinates of
`Im X(M)`. -/
theorem isSmoothFiniteTorusFunction_orbitPlancherelWeight
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) :
    IsSmoothFiniteTorusFunction fun y =>
      orbitPlancherelWeight model r π C hC mu hsq hRefl hCST K hK hPK hOppK p q
        hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
        (orbitMapπ ((model.unitaryCoordinates).toMulEquiv.symm
          y)) :=
  isSmoothFiniteTorusFunction_orbitWeight model r π C hC mu hsq _ _
    (isSmoothFiniteTorusFunction_plancherelWeight i r.cocharacter hRefl hCST hG K hK hPK hOppK Aπ p q
      hneForward hDForwardΩ hneReverse hDReverseΩ hne hirr hreg)

/-- The Plancherel weight is continuous on the orbit `O`. -/
theorem continuous_orbitPlancherelWeight
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) :
    Continuous (orbitPlancherelWeight model r π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr
      hreg) :=
  continuous_orbitWeight model r π C hC mu hsq _
    (continuous_plancherelWeight i r.cocharacter hRefl hCST hG K hK hPK hOppK Aπ p q hneForward hDForwardΩ
      hneReverse hDReverseΩ hne hirr hreg)

/-- **Nonnegativity.** If `j_P⁻¹` has a nonnegative real value at the unitary character
`z ∘ e`, then the Plancherel weight at `π ⊗ z` is a nonnegative real number. -/
theorem orbitPlancherelWeight_nonneg
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) {z : UMI}
    (hz : RationalFunctionNonnegAt MS (parameterProjection_continuous χ) hMS (jP)⁻¹
      (unitaryToUnramified MS (characterRestrict model r z))) :
    ∃ b : ℝ, 0 ≤ b ∧
      orbitPlancherelWeight model r π C hC mu hsq hRefl hCST K hK hPK hOppK p q
        hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
        (orbitMapπ z) = (b : ℂ) := by
  rw [orbitPlancherelWeight_orbitMap]
  exact plancherelWeight_nonneg i r.cocharacter hRefl hCST hG K hK hPK hOppK Aπ p q hneForward hDForwardΩ
    hneReverse hDReverseΩ hne hirr hreg hz

/-- **Nonnegativity on the whole orbit.** If `j_P⁻¹` has a nonnegative real value at every unitary
unramified character of `Z_G(ζ ∘ i)`, then the Plancherel weight is a nonnegative real number at
every point of `O` (Lemma V.2.1, first item). -/
theorem orbitPlancherelWeight_nonneg_of_forall
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹)
    (hnn : ∀ z : UL, RationalFunctionNonnegAt MS (parameterProjection_continuous χ) hMS (jP)⁻¹
      (unitaryToUnramified MS z)) (x : Oπ) :
    ∃ b : ℝ, 0 ≤ b ∧
      orbitPlancherelWeight model r π C hC mu hsq hRefl hCST K hK hPK hOppK p q
        hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg x =
        (b : ℂ) :=
  ((isOpenQuotientMap_discreteSeriesOrbitMap C hC mu _ _).surjective x).elim fun _ hz =>
    hz ▸ orbitPlancherelWeight_nonneg model r π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
      (hnn _)

end Langlands.HarishChandraSchwartz.RationalSemistandard.SourceDensity
