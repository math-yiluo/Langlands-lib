import Langlands.Global.AdelicEisensteinAmbientParametersProof
import Langlands.Global.AdelicImaginaryIntertwiningProperties
import Langlands.Global.AdelicIntertwiningImaginaryUnitarityReduction
import Langlands.Global.AdelicRelativeSpectralCorootChart
import Langlands.Global.AdelicRelativeWavePacketAssociationReduction
import Langlands.Global.AdelicRegularizedConeFourierBoundary
import Langlands.Global.AdelicWavePacketChamberDecayReduction
import Langlands.Global.AdelicWeylConeOrientation
import Langlands.Global.ImaginaryAxisCoordinates

/-! # The coroot chart of a displaced Weyl term -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Set
open scoped CategoryTheory.MonObj ContDiff

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints Langlands.Global.ImaginaryAxis
  Langlands.Aubert.General.RationalPointFamily

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (P Q : StandardIndex F G fam.i fam.ν)
  {n : ℕ} {Coord : Type*} [Fintype Coord]

local notation "Param" J => RealCharacterParameter F (fam.P J)
local notation "Rel" J => relativeParameterSpace (F := F) (fam.p J)
local notation "W" => relativeWeylGroup fam.i

variable (full : (Fin n → ℝ) ≃ₗ[ℝ] (RealCharacterParameter F (fam.P P)))
  (relative : (Coord → ℝ) ≃ₗ[ℝ] ↥(relativeParameterSpace (F := F) (fam.p P)))

/-- The relative imaginary plane in full complex coordinates, displaced in a fixed real
relative direction. -/
def displacedRelativeSpectralChart (direction : Rel P) (p : ℝ × (Coord → ℝ)) : Fin n → ℂ :=
  let v : Fin n → ℝ := full.symm direction.val
  let y : Fin n → ℝ := full.symm (relative p.2).val
  fun j => (↑(p.1 * v j) : ℂ) + ImaginaryAxis.imaginarySlice y j

/-- The displacement chart is smooth in both variables. -/
theorem contDiff_displacedRelativeSpectralChart (Λ : Rel P) :
    ContDiff ℝ ∞ (fam.displacedRelativeSpectralChart P full relative Λ) := by
  let u : (Coord → ℝ) →L[ℝ] (Fin n → ℝ) :=
    (full.symm.toLinearMap.comp ((Rel P).subtype.comp relative.toLinearMap)).toContinuousLinearMap
  apply contDiff_pi.mpr
  intro j
  change ContDiff ℝ ∞ (fun p : ℝ × (Coord → ℝ) =>
    ((p.1 * full.symm Λ.val j : ℝ) : ℂ) + Complex.I * (u p.2 j : ℂ))
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_fst.mul contDiff_const)).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (((ContinuousLinearMap.proj j).comp u).contDiff.comp contDiff_snd)))

omit [Fintype Coord] in
/-- At zero displacement the chart is the coordinate inclusion of the relative imaginary plane. -/
theorem displacedRelativeSpectralChart_zero (Λ : Rel P) (x : Coord → ℝ) :
    fam.displacedRelativeSpectralChart P full relative Λ (0, x) =
      imaginarySlice (full.symm (relative x).val) := by
  funext j
  simp [displacedRelativeSpectralChart]

/-- Coroot evaluations of the Weyl-transformed complex parameter minus the fixed imaginary
exponent of the tested form. -/
def weylConeCorootValue (c : fam.M Q ⟶ fam.M P) (π : fam.P Q ⟶ fam.M Q)
    (freq : Param Q) (s : Fin n → ℂ) (α : fam.relativeSimpleRoots Q) : ℂ :=
  fam.corootValue Q (weylParameter (fam.l P) c π (realChart full s) -
    imaginaryParameter F (fam.P Q) freq) α

omit [NumberField F] in
/-- Each coroot evaluation is an affine holomorphic function of the full complex coordinates. -/
theorem differentiable_weylConeCorootValue (c : fam.M Q ⟶ fam.M P) (π : fam.P Q ⟶ fam.M Q)
    (freq : Param Q) (α : fam.relativeSimpleRoots Q) :
    Differentiable ℂ (fun s : Fin n → ℂ => fam.weylConeCorootValue P Q full c π freq s α) := by
  let A : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun s => fam.corootValue Q (weylParameter (fam.l P) c π (realChart full s)) α
      map_add' := fun x y => by simp [corootValue]
      map_smul' := fun t x => by simp [corootValue] }
  have h := A.toContinuousLinearMap.differentiable.sub_const
    (fam.corootValue Q (imaginaryParameter F (fam.P Q) freq) α)
  simpa only [weylConeCorootValue, corootValue, map_sub, LinearMap.sub_apply,
    LinearMap.coe_toContinuousLinearMap', A, LinearMap.coe_mk, AddHom.coe_mk] using h

omit [NumberField F] in
private theorem realPart_realToComplex (J : StandardIndex F G fam.i fam.ν) (x : Param J) :
    parameterRealPart F (fam.P J) (realToComplexParameter (fam.P J) x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul t χ => rw [realToComplexParameter_tmul, parameterRealPart_tmul, Complex.ofReal_re]
  | add y z hy hz => simp only [map_add, hy, hz]

omit [NumberField F] in
private theorem weylParameter_realToComplex (c : fam.M Q ⟶ fam.M P) (π : fam.P Q ⟶ fam.M Q)
    (x : Param P) :
    weylParameter (fam.l P) c π (realToComplexParameter (fam.P P) x) =
      realToComplexParameter (fam.P Q) (realWeylParameter (fam.l P) c π x) := by
  induction x using TensorProduct.inductionOn with
  | tmul t χ => rfl
  | add y z hy hz => simp only [map_add, hy, hz]

omit [NumberField F] in
private theorem corootValue_realToComplex (x : Param Q) (α : fam.relativeSimpleRoots Q) :
    fam.corootValue Q (realToComplexParameter (fam.P Q) x) α =
      (realParameterPairing F (fam.P Q) x (fam.relativeCoroot Q α) : ℂ) := by
  induction x using TensorProduct.inductionOn with
  | tmul t χ => simp [corootValue, realToComplexParameter_tmul]
  | add y z hy hz =>
    simpa only [corootValue, map_add, LinearMap.add_apply, Complex.ofReal_add] using congrArg₂ (· + ·) hy hz

/-- The real Weyl transport, followed by coroot evaluation, is a relative spectral equivalence.
Along the displaced plane its real slopes come from the ambient Weyl action, and its imaginary
translations are the coroot evaluations of the tested exponent. -/
def WeylConeCorootChartStatement (a : normalizerPoints fam.i) (c : fam.M Q ⟶ fam.M P)
    (π : fam.P Q ⟶ fam.M Q) : Prop :=
  fam.l Q ≫ π = 𝟙 (fam.M Q) →
  IsWeylConjugation (fam.p P) (fam.l P) (fam.p Q) (fam.l Q) a.val c →
  ∃ e : (Coord → ℝ) ≃L[ℝ] (fam.relativeSimpleRoots Q → ℝ),
    (∀ x α, e x α = realParameterPairing F (fam.P Q)
      (realWeylParameter (fam.l P) c π (relative x).val) (fam.relativeCoroot Q α)) ∧
    ∀ (Λ : Rel P) (freq : Param Q) (t : ℝ) (x : Coord → ℝ),
      fam.weylConeCorootValue P Q full c π freq
        (fam.displacedRelativeSpectralChart P full relative Λ (t, x)) =
        displacedOrthantParameter
          (fam.weylConeSlope Q (QuotientGroup.mk a : W)⁻¹ (fam.chamberEmbedding P Λ.val)) t
          (e x - fun α => realParameterPairing F (fam.P Q) freq (fam.relativeCoroot Q α))

theorem weylConeCorootChart (a : normalizerPoints fam.i) (c : fam.M Q ⟶ fam.M P)
    (π : fam.P Q ⟶ fam.M Q) : fam.WeylConeCorootChartStatement P Q full relative a c π := by
  intro hπ ha
  let : IsClosedImmersion (fam.p P).hom.hom.left := fam.isClosedImmersion_p P
  let : IsClosedImmersion (fam.p Q).hom.hom.left := fam.isClosedImmersion_p Q
  let : IsAffine (fam.P P).X.left := isAffine_of_isAffineHom (fam.p P).hom.hom.left
  let : IsAffine (fam.P Q).X.left := isAffine_of_isAffineHom (fam.p Q).hom.hom.left
  have hp : Mono (fam.p P).hom.hom := Over.mono_of_mono_left _
  let : Mono (fam.p P) := (Grp.forget _).mono_of_mono_map (f := fam.p P) hp
  let rootPresentation (J : StandardIndex F G fam.i fam.ν) :
      ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩
  obtain ⟨Wrel, hWrel⟩ :=
    exists_relativeWeylParameter_linearEquiv (rootPresentation P) (rootPresentation Q) hπ ha
  obtain ⟨E, hE⟩ := fam.relativeSpectralCorootChart Q
  let e := ((relative.trans Wrel).trans E.symm).toContinuousLinearEquiv
  have he (x : Coord → ℝ) (α : fam.relativeSimpleRoots Q) :
      e x α = realParameterPairing F (fam.P Q)
        (realWeylParameter (fam.l P) c π (relative x).val) (fam.relativeCoroot Q α) := by
    change E.symm (Wrel (relative x)) α = _
    rw [← hWrel]
    simpa only [LinearEquiv.apply_symm_apply] using (hE (E.symm (Wrel (relative x))) α).symm
  refine ⟨e, he, fun Λ freq t x => ?_⟩
  have hFourier : realChart full (imaginarySlice (full.symm (relative x).val)) =
      imaginaryParameter F (fam.P P) (relative x).val := by
    rw [show imaginarySlice (full.symm (relative x).val) =
      (fun j => (full.symm (relative x).val j : ℂ) * Complex.I) from
        funext fun _ => mul_comm _ _,
      realChart_I_mul, LinearEquiv.apply_symm_apply]
  have hReal : realChart full (fun j => ((t * full.symm Λ.val j : ℝ) : ℂ)) =
      (t : ℂ) • realToComplexParameter (fam.P P) Λ.val := by
    rw [realChart_ofReal]
    change realToComplexParameter (fam.P P) (full (t • full.symm Λ.val)) = _
    rw [map_smul, LinearEquiv.apply_symm_apply, map_smul]
    exact (Complex.coe_smul t _).symm
  have hParam : realChart full (fam.displacedRelativeSpectralChart P full relative Λ (t, x)) =
      (t : ℂ) • realToComplexParameter (fam.P P) Λ.val +
        imaginaryParameter F (fam.P P) (relative x).val := by
    change realChart full ((fun j => ((t * full.symm Λ.val j : ℝ) : ℂ)) +
      imaginarySlice (full.symm (relative x).val)) = _
    rw [map_add, hReal, hFourier]
  have hWeyl := eisensteinAmbientWeylParameter F G (fam.P P) (fam.M P) (fam.P Q) (fam.M Q)
    fam.T fam.i (fam.p P) (fam.l P) (fam.p Q) (fam.l Q) (fam.torus P) (fam.torus Q) π a c
    (fam.torus_comp P) (fam.torus_comp Q) hπ ha (realToComplexParameter (fam.P P) Λ.val)
  change fam.chamberEmbedding Q (parameterRealPart F (fam.P Q)
      (weylParameter (fam.l P) c π (realToComplexParameter (fam.P P) Λ.val))) =
    relativeWeylRealCharacterAction fam.i (QuotientGroup.mk a)
      (fam.chamberEmbedding P (parameterRealPart F (fam.P P) (realToComplexParameter (fam.P P) Λ.val))) at hWeyl
  rw [fam.weylParameter_realToComplex P Q c π, fam.realPart_realToComplex Q,
    fam.realPart_realToComplex P] at hWeyl
  funext α
  have hd : realParameterPairing F (fam.P Q) (realWeylParameter (fam.l P) c π Λ.val)
      (fam.relativeCoroot Q α) =
      fam.weylConeSlope Q (QuotientGroup.mk a : W)⁻¹ (fam.chamberEmbedding P Λ.val) α := by
    rw [relativeCoroot, fam.realParameterPairing_splitDual Q, hWeyl, weylConeSlope, inv_inv]
    rfl
  simp only [weylConeCorootValue, hParam, map_sub, map_add, map_smul,
    fam.weylParameter_realToComplex P Q c π, weylParameter_imaginaryParameter,
    corootValue, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    ChamberDecay.complexParameterPairing_imaginaryParameter]
  rw [show complexParameterPairing F (fam.P Q)
    (realToComplexParameter (fam.P Q) (realWeylParameter (fam.l P) c π Λ.val)) (fam.relativeCoroot Q α) = _
      from fam.corootValue_realToComplex Q _ α, hd, ← he x α]
  simp only [displacedOrthantParameter, Pi.sub_apply, Complex.ofReal_sub, Complex.ofReal_mul]
  ring

/-- A relative direction with zero Levi coroot evaluations and positive outside coroot
evaluations orients every Weyl term whose simple roots match the inducing Levi. -/
theorem exists_weylConeDisplacement :
    ∃ Λ : Rel P, ∀ (Q : StandardIndex F G fam.i fam.ν) (a : W),
      schemeWeylCharacterAction fam.i a⁻¹ '' Q.val = P.val →
      let d := fam.weylConeSlope Q a⁻¹ (fam.chamberEmbedding P Λ.val)
      (∀ α, d α ≠ 0) ∧ ((∀ α, 0 < d α) ↔ Q = P ∧ a = 1) := by
  obtain ⟨Λ, hΛ⟩ := fam.exists_relativeDominantParameter P
  refine ⟨Λ, fun J a ha => ?_⟩
  have h := fam.weylConeOrientation P J a⁻¹ (fam.chamberEmbedding P Λ.val)
    (fun α hα => by simp only [hΛ α (P.property hα), ite_eq_left hα])
    (fun α hα hp => by simp only [hΛ α hα, ite_eq_right hp, zero_lt_one]) ha
  simpa only [inv_eq_one] using h

end Langlands.Global.StandardParabolicFamily
