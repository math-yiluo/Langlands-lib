import Langlands.Global.ArchimedeanCompactAverageTranslation
import Langlands.Global.ArchimedeanCompactGroupFiniteProof
import Langlands.Global.ArchimedeanPlaceEnveloping
import Langlands.Global.ArchimedeanPlaceRestriction
import Langlands.Global.ArchimedeanSeparateJointFiniteProof
import Langlands.Global.RankinSelberg.ComplexLocalCompactProjection
import Langlands.Global.RankinSelberg.RealLocalWhittakerModel
import Langlands.Representation.Archimedean.RealPrincipalSeriesInfinitesimalCharacter
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible

/-! # Compact averages of translates for real Whittaker intertwiners -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean NumberField
open scoped Classical ContDiff Manifold Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanGL

namespace RealExactCompactProjection

attribute [local instance 100] LieRing.ofAssociativeRing

section Transport

variable (F : Type) [Field F] [NumberField F] (r : ℕ)

local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "M" => Matrix (Fin n) (Fin n) ℝ
local notation "A" => ArchimedeanMatrix F n
local notation "AG" => Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing F)
local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "S" => SmoothFunctions F n

private def matrixProjection (v : RP) : A →ₐ[ℝ] M :=
  (realPlaceScalarProjection F v).mapMatrix

private def projection (v : RP) : AG →* G :=
  (Matrix.GeneralLinearGroup.map (realPlaceScalarProjection F v).toRingHom).comp
    (archimedeanGLCoordinates F n).toMonoidHom

private def inclusion (v : RP) : G →* AG :=
  (archimedeanGLCoordinates F n).symm.toMonoidHom.comp (realPlaceGL F n v)

omit [NumberField F] in
private theorem projection_inclusion (v : RP) (g : G) :
    projection F r v (inclusion F r v g) = g := by
  apply Units.ext
  change matrixProjection F r v (archimedeanGLCoordinates F n
    ((archimedeanGLCoordinates F n).symm (realPlaceGL F n v g))).val = g.val
  rw [ContinuousMulEquiv.apply_symm_apply]
  refine Matrix.ext fun i j => ?_
  change (((realPlaceGL F n v g : ArchimedeanGL F n) :
    Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) i j).1 v = g.val i j
  change (((Pi.mulSingle v g : RP → Matrix.GeneralLinearGroup (Fin n) ℝ) v :
    Matrix.GeneralLinearGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i j = g.val i j
  rw [Pi.mulSingle_eq_same]

private def compactProjection (v : RP) (k : standardInfiniteCompact F n) :
    Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨(projection F r v k.val).val, ((mem_standardInfiniteCompact_iff F n k.val).mp k.property).1 v⟩

omit [NumberField F] in
private theorem toUnits_compactProjection (v : RP) (k : standardInfiniteCompact F n) :
    Unitary.toUnits (compactProjection F r v k) = projection F r v k.val :=
  Units.ext rfl

private def pullback (v : RP) (W : G → ℂ)
    (hW : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ W) : S := by
  refine ⟨W ∘ projection F r v, ?_⟩
  let P := (matrixProjection F r v).toLinearMap.toContinuousLinearMap
  have hP : Set.MapsTo P {x : A | IsUnit x} {x : M | IsUnit x} :=
    fun _ hx => (show IsUnit _ from hx).map (matrixProjection F r v)
  have hPdiff : ContDiff ℝ ∞ (P : A → M) := P.contDiff
  have hExt : ContDiffOn ℝ ∞ (unitsExtension W ∘ P) {x : A | IsUnit x} :=
    (contDiffOn_unitsExtension hW).comp hPdiff.contDiffOn hP
  have hVal : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, A) ∞ (Units.val : ArchimedeanGL F n → A) :=
    Units.contMDiff_val
  have hSmooth := (contMDiffOn_iff_contDiffOn.mpr hExt).comp_contMDiff hVal
    (fun g => g.isUnit)
  change ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞
    (fun x : ArchimedeanGL F n =>
      W (projection F r v ((archimedeanGLCoordinates F n).symm x)))
  refine hSmooth.congr ?_
  intro x
  rw [Function.comp_apply, Function.comp_apply]
  have heq : P x.val =
      (projection F r v ((archimedeanGLCoordinates F n).symm x)).val := by
    change matrixProjection F r v x.val = matrixProjection F r v
      (archimedeanGLCoordinates F n ((archimedeanGLCoordinates F n).symm x)).val
    rw [ContinuousMulEquiv.apply_symm_apply]
  exact ((congrArg (unitsExtension W) heq).trans (unitsExtension_val W _)).symm

private theorem pullback_differential (v : RP) (X : RealLieAlgebra F n) (W : G → ℂ)
    (hW : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ W) (g : AG) :
    (smoothDifferential F n X (pullback F r v W hW)).val g =
      rightDerivative (matrixModel ℝ n) (realPlaceLieProjection F n v X)
        W (projection F r v g) := by
  let P := (matrixProjection F r v).toLinearMap.toContinuousLinearMap
  let x : A := (archimedeanGLCoordinates F n g).val
  let E := unitsExtension W ∘ P
  have hE (h : ArchimedeanGL F n) :
      E h.val = (pullback F r v W hW).val ((archimedeanGLCoordinates F n).symm h) := by
    change unitsExtension W (matrixProjection F r v h.val) = W
      (projection F r v ((archimedeanGLCoordinates F n).symm h))
    have hh : matrixProjection F r v h.val =
        (projection F r v ((archimedeanGLCoordinates F n).symm h)).val := by
      change _ = matrixProjection F r v
        (archimedeanGLCoordinates F n ((archimedeanGLCoordinates F n).symm h)).val
      rw [ContinuousMulEquiv.apply_symm_apply]
    rw [hh, unitsExtension_val]
  rw [smoothDifferential_eq_of_extension F n X _ E hE,
    rightDerivative_eq_fderiv hW]
  have hPx : P x = (projection F r v g).val := rfl
  have hd : DifferentiableAt ℝ (unitsExtension W) (P x) :=
    differentiableAt_unitsExtension hW (hPx ▸ (projection F r v g).isUnit)
  have hPd : HasFDerivAt (P : A → M) P x := P.hasFDerivAt
  have hD : fderiv ℝ E x = (fderiv ℝ (unitsExtension W) (P x)).comp P :=
    (hd.hasFDerivAt.comp x hPd).fderiv
  change fderiv ℝ E x _ = _
  rw [hD, ContinuousLinearMap.comp_apply]
  change fderiv ℝ (unitsExtension W) (P x)
    (matrixProjection F r v (x * realLieAlgebraToMatrix F n X)) = _
  rw [map_mul]
  rfl

variable (ds : List RealBlock)

local notation "V" => Automorphic.realStandardKFinite n ds
local notation "D" => V →ₗ[ℂ] (G → ℂ)
local notation "ρ" => realStandardRep n ds
local notation "π" => realStandardLie n ds

private theorem contMDiff_standard (f : V) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (f : G → ℂ) :=
  f.2.1.1.1

/-- Pullback of the standard vectors themselves. -/
private def liftStandard (v : RP) : V →ₗ[ℂ] S where
  toFun f := pullback F r v f.val (contMDiff_standard r ds f)
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- Pullback of the coefficient functions of an intertwiner. -/
private def coefficients (v : RP) (B : D)
    (hB : ∀ f : V, ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (B f)) : V →ₗ[ℂ] S where
  toFun f := pullback F r v (B f) (hB f)
  map_add' f e := by apply Subtype.ext; funext g; exact congrFun (map_add B f e) _
  map_smul' z f := by apply Subtype.ext; funext g; exact congrFun (map_smul B z f) _

private theorem enveloping_of_lie (v : RP) (L : V →ₗ[ℂ] S)
    (hL : ∀ (X : RealLieAlgebra F n) (f : V),
      smoothDifferential F n X (L f) = L (π ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n v X) f))
    (u : EnvelopingAlgebra F n) (f : V) :
    ArchimedeanGL.envelopingAction F n u (L f) =
      L (Archimedean.envelopingAction π (realPlaceEnvelopingProjection F n v u) f) := by
  induction u using Archimedean.InfinitesimalCharacter.envInduction generalizing f with
  | algebraMap z =>
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  | ι Z =>
    change ArchimedeanGL.envelopingAction F n (envelopingGenerator F n Z) _ =
      L (Archimedean.envelopingAction π
          (realPlaceEnvelopingProjection F n v (envelopingGenerator F n Z)) f)
    rw [envelopingAction_generator, realPlaceEnvelopingProjection_generator]
    rw [realPlaceEnvelopingGenerator, Archimedean.envelopingAction,
      UniversalEnvelopingAlgebra.lift_ι_apply]
    induction Z using TensorProduct.inductionOn with
    | tmul z X =>
      have hZ : (z ⊗ₜ[ℝ] realPlaceLieProjection F n v X : ℂ ⊗[ℝ] M) =
          z • ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n v X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp only [complexSmoothLieAction_tmul, realPlaceComplexLieProjection_tmul, hZ,
        map_smul, LinearMap.smul_apply]
      congr 1
      exact hL X f
    | add X Y hX hY =>
      simp only [map_add, LinearMap.add_apply, hX, hY]
  | mul u w hu hw =>
    rw [envelopingAction_mul, hw, hu, map_mul, map_mul, Module.End.mul_apply]
  | add u w hu hw =>
    simp only [map_add, LinearMap.add_apply, hu, hw]

private theorem liftStandard_lie (v : RP) (X : RealLieAlgebra F n) (f : V) :
    smoothDifferential F n X (liftStandard F r ds v f) =
      liftStandard F r ds v (π ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n v X) f) := by
  apply Subtype.ext
  funext g
  change (smoothDifferential F n X (pullback F r v f.val (contMDiff_standard r ds f))).val g =
    (π ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n v X) f).val (projection F r v g)
  rw [pullback_differential, realStandardLie_one_tmul_apply_coe]

private theorem coefficients_lie (v : RP) {a : ℝˣ} {B : D}
    (hB : IsRealWhittakerIntertwiner r ds a B) (X : RealLieAlgebra F n) (f : V) :
    smoothDifferential F n X (coefficients F r ds v B hB.2.1 f) =
      coefficients F r ds v B hB.2.1 (π ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n v X) f) := by
  apply Subtype.ext
  funext g
  change (smoothDifferential F n X (pullback F r v (B f) (hB.2.1 f))).val g =
    B (π ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n v X) f) (projection F r v g)
  rw [pullback_differential F r v X (B f) (hB.2.1 f)]
  exact (congrFun (hB.2.2.2.2 _ f _ (realStandardLie_one_tmul_apply_coe n ds _ f)) _).symm

private theorem liftStandard_compact (v : RP) (k : standardInfiniteCompact F n) (f : V) :
    smoothRightAction F n k.val (liftStandard F r ds v f) =
      liftStandard F r ds v (ρ (compactProjection F r v k) f) := by
  apply Subtype.ext
  funext g
  change f.val (projection F r v (g * k.val)) =
    (ρ (compactProjection F r v k) f).val (projection F r v g)
  rw [realStandardRep_apply_coe, map_mul, toUnits_compactProjection]
  rfl

private theorem coefficients_compact (v : RP) {a : ℝˣ} {B : D}
    (hB : IsRealWhittakerIntertwiner r ds a B) (k : standardInfiniteCompact F n) (f : V) :
    smoothRightAction F n k.val (coefficients F r ds v B hB.2.1 f) =
      coefficients F r ds v B hB.2.1 (ρ (compactProjection F r v k) f) := by
  let k' : unitaryCompact ℝ n := ⟨Unitary.toUnits (compactProjection F r v k),
    (compactProjection F r v k).property⟩
  apply Subtype.ext
  funext g
  change B f (projection F r v (g * k.val)) =
    B (ρ (compactProjection F r v k) f) (projection F r v g)
  rw [hB.2.2.2.1 k' f _ (realStandardRep_apply_coe n ds _ f), map_mul]
  change B f (_ * _) = B f (_ * Unitary.toUnits (compactProjection F r v k))
  rw [toUnits_compactProjection]

omit [NumberField F] in
private theorem projection_mem_center (v : RP) (z : EnvelopingCenter F n) :
    realPlaceEnvelopingProjection F n v z.val ∈
      Subalgebra.center ℂ (RealPlaceEnvelopingAlgebra n) := by
  rw [Subalgebra.mem_center_iff]
  intro w
  obtain ⟨u, rfl⟩ := realPlaceEnvelopingProjection_surjective F n v w
  simpa only [map_mul] using congrArg (realPlaceEnvelopingProjection F n v)
    ((Subalgebra.mem_center_iff.mp z.property) u)

private theorem jointFinite_of (v : RP) (L : V →ₗ[ℂ] S)
    (hL : ∀ (u : EnvelopingAlgebra F n) (f : V), ArchimedeanGL.envelopingAction F n u (L f) =
      L (Archimedean.envelopingAction π (realPlaceEnvelopingProjection F n v u) f))
    (hK : ∀ (k : standardInfiniteCompact F n) (f : V),
      smoothRightAction F n k.val (L f) = L (ρ (compactProjection F r v k) f)) (f : V) :
    IsJointFinite F n (L f) := by
  apply separateJointFinite F n (L f)
  · have hle : centerOrbitSpan F n (L f) ≤ Submodule.span ℂ {L f} := by
      apply Submodule.span_le.mpr
      rintro _ ⟨z, rfl⟩
      change ArchimedeanGL.envelopingAction F n z.val (L f) ∈ Submodule.span ℂ {L f}
      rw [hL]
      obtain ⟨c, hc⟩ := realStandardLie_hasInfinitesimalCharacter n ds _
        (projection_mem_center F r v z)
      rw [hc, Module.algebraMap_end_apply, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    exact Submodule.finiteDimensional_of_le hle
  · apply compactGroupFiniteDifferential F n (L f)
    have : Module.Finite ℂ (Langlands.FiniteVectors.orbitSpan ρ f) :=
      (isRealGKModule_realStandardModule n ds).1 f
    have hle : Langlands.FiniteVectors.orbitSpan
        ((smoothRightAction F n).comp (standardInfiniteCompact F n).subtype) (L f) ≤
        (Langlands.FiniteVectors.orbitSpan ρ f).map L := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      change smoothRightAction F n k.val (L f) ∈ _
      rw [hK]
      exact Submodule.mem_map_of_mem
        (Langlands.FiniteVectors.action_mem_orbitSpan ρ (compactProjection F r v k) f)
    exact Submodule.finiteDimensional_of_le hle

end Transport

section CompactAverage

open MeasureTheory Set
open ArchimedeanGL.DerivativeSmoothFunctions
open ArchimedeanGL.SmoothFamily (averageLM averagedTranslate_mem compactRepresentation
  rightRepresentation)
open ComplexJacquet (hasFiniteCompactConvolutionKernel_of_finite_translates)

local instance realExactProjectionMeasurable (j : ℕ) :
    MeasurableSpace (unitaryCompact ℝ j) := borel _
local instance realExactProjectionBorel (j : ℕ) : BorelSpace (unitaryCompact ℝ j) := ⟨rfl⟩

variable {F : Type} [Field F] [NumberField F] {r : ℕ}
variable {ds : List RealBlock} {a : ℝˣ}

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "n" => (r + 1)
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "AG" => InfiniteAdelicGL F n
local notation "K" => standardInfiniteCompact F n
local notation "U" => unitaryCompact ℝ n
local notation "Std" => Automorphic.realStandardKFinite n ds
local notation "Fam" => ArchimedeanGL.SmoothFamily F n Bool

private def liftPair (v : RP) (B : Std →ₗ[ℂ] (G → ℂ))
    (hB : IsRealWhittakerIntertwiner r ds a B) : Std →ₗ[ℂ] Fam :=
  LinearMap.pi fun b => (toSmooth F n).symm.toLinearMap.comp
    (Bool.rec (liftStandard F r ds v) (coefficients F r ds v B hB.2.1) b)

private theorem liftPair_compact (v : RP) (B : Std →ₗ[ℂ] (G → ℂ))
    (hB : IsRealWhittakerIntertwiner r ds a B) (k : K) (f : Std) :
    compactRepresentation k (liftPair v B hB f) =
      liftPair v B hB (realStandardRep n ds (compactProjection F r v k) f) := by
  funext b
  apply (toSmooth F n).injective
  rw [ArchimedeanGL.SmoothFamily.compactRepresentation_apply, compactAction_apply,
    toSmooth_rightAction]
  cases b
  · simpa only [liftPair, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using liftStandard_compact F r ds v k f
  · simpa only [liftPair, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using coefficients_compact F r ds v hB k f

private theorem liftPair_enveloping (v : RP) (B : Std →ₗ[ℂ] (G → ℂ))
    (hB : IsRealWhittakerIntertwiner r ds a B) (q : EnvelopingAlgebra F n) (f : Std) :
    q • liftPair v B hB f =
      liftPair v B hB (Langlands.Archimedean.envelopingAction (realStandardLie n ds)
        (realPlaceEnvelopingProjection F n v q) f) := by
  funext b
  apply (toSmooth F n).injective
  change toSmooth F n (operator F n q ((liftPair v B hB f) b)) = _
  rw [toSmooth_operator]
  cases b
  · simpa only [liftPair, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using
      enveloping_of_lie F r ds v (liftStandard F r ds v) (liftStandard_lie F r ds v) q f
  · simpa only [liftPair, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using
      enveloping_of_lie F r ds v (coefficients F r ds v B hB.2.1)
        (coefficients_lie F r ds v hB) q f

private theorem liftPair_eval (v : RP) (B : Std →ₗ[ℂ] (G → ℂ))
    (hB : IsRealWhittakerIntertwiner r ds a B) (f : Std) (g : AG) :
    evalCLM F n g (liftPair v B hB f false) = f.val (projection F r v g) ∧
    evalCLM F n g (liftPair v B hB f true) = B f (projection F r v g) := by
  simp only [evalCLM_apply, liftPair, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact ⟨rfl, rfl⟩

private theorem liftPair_compactFinite (v : RP) (B : Std →ₗ[ℂ] (G → ℂ))
    (hB : IsRealWhittakerIntertwiner r ds a B) (f : Std) :
    FiniteDimensional ℂ (Langlands.FiniteVectors.orbitSpan
      (compactRepresentation (ι := Bool)) (liftPair v B hB f)) := by
  let Q := Langlands.FiniteVectors.orbitSpan (realStandardRep n ds) f
  have : Module.Finite ℂ Q := (isRealGKModule_realStandardModule n ds).1 f
  apply Submodule.finiteDimensional_of_le (S₂ := Q.map (liftPair v B hB))
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  change compactRepresentation k (liftPair v B hB f) ∈ _
  rw [liftPair_compact]
  exact Submodule.mem_map_of_mem (Langlands.FiniteVectors.action_mem_orbitSpan _ _ _)

private def placeCompactMap (v : RP) : C(U, AG) :=
  ⟨fun k => (realPlaceCompactInclusion F n v ⟨k.val.val, k.2⟩).val,
    continuous_subtype_val.comp ((realPlaceCompactInclusion F n v).continuous.comp
      ((Units.continuous_val.comp continuous_subtype_val).subtype_mk _))⟩

omit [NumberField F] in
private theorem placeCompactMap_mem (v : RP) (k : U) : placeCompactMap v k ∈ K :=
  (realPlaceCompactInclusion F n v ⟨k.val.val, k.2⟩).2

omit [NumberField F] in
private theorem projection_placeCompactMap (v : RP) (k : U) :
    projection F r v (placeCompactMap v k) = k.val := by
  have h := realPlaceGL_unitary v (⟨k.val.val, k.2⟩ : Matrix.unitaryGroup (Fin n) ℝ)
  have he : placeCompactMap v k = inclusion F r v k.val := by
    change (realPlaceCompactInclusion F n v ⟨k.val.val, k.2⟩).val = _
    apply (archimedeanGLCoordinates F n).injective
    change _ = archimedeanGLCoordinates F n
      ((archimedeanGLCoordinates F n).symm (realPlaceGL F n v k.val))
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact h.symm.trans (congrArg (realPlaceGL F n v) (Units.ext rfl))
  rw [he, projection_inclusion]

set_option maxHeartbeats 1600000 in
private theorem compact_projection_atPlace (v : RP) (ν : Measure U) [ν.IsHaarMeasure]
    (κ : C(U, ℂ)) (hκ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      fun h : U => fun k => κ (h⁻¹ * k)))) (B : Std →ₗ[ℂ] (G → ℂ))
    (hB : IsRealWhittakerIntertwiner r ds a B) (f : Std) (g : G) :
    ∃ p : Std, (∀ x : G, p.val x = ∫ k : U, κ k * f.val (x * k.val * g) ∂ν) ∧
      ∀ x : G, B p x = ∫ k : U, κ k * B f (x * k.val * g) ∂ν := by
  let L := liftPair v B hB
  let Q := LinearMap.range L
  let j := placeCompactMap (r := r) v
  let P : Fam →ₗ[ℂ] Fam := averageLM j ν κ
  have hstab (k : K) (q : EnvelopingAlgebra F n) (w : Fam) (hw : w ∈ Q) :
      compactRepresentation k (q • w) ∈ Q := by
    obtain ⟨w, rfl⟩ := hw
    change compactRepresentation k (q • liftPair v B hB w) ∈ Q
    rw [liftPair_enveloping, liftPair_compact]
    exact LinearMap.mem_range_self _ _
  have hfin (w : Fam) (hw : w ∈ Q) : FiniteDimensional ℂ
      (Langlands.FiniteVectors.orbitSpan compactRepresentation w) := by
    obtain ⟨w, rfl⟩ := hw
    exact liftPair_compactFinite v B hB w
  have hPQ : Q.map P ≤ Q := by
    apply Submodule.map_le_iff_le_comap.mpr
    intro w hw
    let O := Langlands.FiniteVectors.orbitSpan (compactRepresentation (ι := Bool)) w
    have : FiniteDimensional ℂ O := hfin w hw
    have hO : O ≤ Q := Submodule.span_le.mpr (by
      rintro _ ⟨k, rfl⟩
      change compactRepresentation k w ∈ Q
      simpa only [one_smul] using hstab k 1 w hw)
    have ha : P w ∈ O.topologicalClosure := by
      apply ArchimedeanGL.SmoothFamily.averageLM_mem_topologicalClosure
      intro k
      exact O.le_topologicalClosure
        (Langlands.FiniteVectors.action_mem_orbitSpan compactRepresentation
          ⟨j k, placeCompactMap_mem v k⟩ w)
    rw [O.closed_of_finiteDimensional.submodule_topologicalClosure_eq] at ha
    exact hO ha
  let E : Fam →ₗ[ℂ] (U → ℂ) :=
    LinearMap.pi fun k => (evalCLM F n (inclusion F r v k.val)).toLinearMap.comp
      (LinearMap.proj false)
  have hE_inj : Function.Injective (E.comp Q.subtype) := by
    rintro ⟨w, hw⟩ ⟨w', hw'⟩ he
    obtain ⟨f₁, rfl⟩ := hw
    obtain ⟨f₂, rfl⟩ := hw'
    have hEq : f₁ = f₂ := by
      apply Subtype.ext
      apply eq_of_eqOn_unitaryCompact_of_mem_principalSeries f₁.2.1.1 f₂.2.1.1
      intro k hk
      have eq := congrFun he (⟨k, hk⟩ : U)
      change evalCLM F n (inclusion F r v k) (liftPair v B hB f₁ false) =
        evalCLM F n (inclusion F r v k) (liftPair v B hB f₂ false) at eq
      rw [(liftPair_eval v B hB f₁ _).1, (liftPair_eval v B hB f₂ _).1,
        projection_inclusion] at eq
      exact eq
    subst f₂
    rfl
  obtain ⟨d, α, β, hβ, hsep⟩ :=
    hasFiniteCompactConvolutionKernel_of_finite_translates κ κ.continuous hκ
  let T := Submodule.span ℂ (Set.range α)
  have : FiniteDimensional ℂ T := FiniteDimensional.span_of_finite ℂ (Set.finite_range α)
  have hET (w : Fam) (hw : w ∈ Q.map P) : E w ∈ T := by
    obtain ⟨w, hw, rfl⟩ := hw
    obtain ⟨f, rfl⟩ := hw
    have he : E (P (L f)) = ∑ l, (∫ k : U, β l k * f.val k.val ∂ν) • α l := by
      funext x
      change evalCLM F n (inclusion F r v x.val) (P (L f) false) = _
      rw [show P (L f) false = CompactIndexAverage.averageLM j ν κ (L f false) from rfl,
        CompactIndexAverage.eval_averageLM]
      simp only [L, (liftPair_eval v B hB f _).1, map_mul, projection_inclusion,
        projection_placeCompactMap, j]
      have hs : (∫ k : U, κ (x⁻¹ * k) * f.val k.val ∂ν) =
          ∑ l, α l x * (∫ k : U, β l k * f.val k.val ∂ν) := by
        simp_rw [hsep, Finset.sum_mul, mul_assoc]
        rw [integral_finsetSum]
        · exact Finset.sum_congr rfl (fun l _ => integral_const_mul _ _)
        · intro l _
          exact (((hβ l).mul (f.2.1.1.1.continuous.comp continuous_subtype_val)).const_mul
            (α l x)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      rw [show (∫ k : U, κ k * f.val (x.val * k.val) ∂ν) =
        ∫ k : U, κ (x⁻¹ * k) * f.val k.val ∂ν by
          rw [← integral_mul_left_eq_self (fun k : U => κ (x⁻¹ * k) * f.val k.val) x]
          simp only [inv_mul_cancel_left]; rfl, hs]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [he]
    exact Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨l, rfl⟩))
  have hRank : FiniteDimensional ℂ (Q.map P) := by
    let e : (Q.map P) →ₗ[ℂ] T := (E.comp (Q.map P).subtype).codRestrict T
      (fun w => hET w w.2)
    have hi : Function.Injective e := by
      intro u w h
      have hh := hE_inj (show E.comp Q.subtype ⟨u.val, hPQ u.2⟩ =
        E.comp Q.subtype ⟨w.val, hPQ w.2⟩ from congrArg Subtype.val h)
      exact Subtype.ext (congrArg (fun z : Q => z.val) hh)
    exact FiniteDimensional.of_injective e hi
  have hjoint (b : Bool) : IsJointFinite F n (toSmooth F n (L f b)) := by
    cases b
    · simpa only [L, liftPair, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using
        jointFinite_of F r ds v (liftStandard F r ds v)
          (enveloping_of_lie F r ds v (liftStandard F r ds v) (liftStandard_lie F r ds v))
          (liftStandard_compact F r ds v) f
    · simpa only [L, liftPair, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using
        jointFinite_of F r ds v (coefficients F r ds v B hB.2.1)
          (enveloping_of_lie F r ds v (coefficients F r ds v B hB.2.1)
            (coefficients_lie F r ds v hB))
          (coefficients_compact F r ds v hB) f
  obtain ⟨p, hp⟩ := averagedTranslate_mem j ν κ Q hstab (placeCompactMap_mem v) hfin hRank
    (LinearMap.mem_range_self L f) hjoint (inclusion F r v g)
  refine ⟨p, fun x => ?_, fun x => ?_⟩
  · have h := congrArg (fun w : Fam => evalCLM F n (inclusion F r v x) (w false)) hp
    change evalCLM F n (inclusion F r v x) (L p false) =
      evalCLM F n (inclusion F r v x)
        (P (rightRepresentation (inclusion F r v g) (L f)) false) at h
    rw [show P (rightRepresentation (inclusion F r v g) (L f)) false =
      CompactIndexAverage.averageLM j ν κ (rightAction F n (inclusion F r v g) (L f false))
        from rfl,
      CompactIndexAverage.eval_averageLM] at h
    simpa only [L, (liftPair_eval v B hB _ _).1, evalCLM_rightAction, map_mul,
      projection_inclusion, j, projection_placeCompactMap] using h
  · have h := congrArg (fun w : Fam => evalCLM F n (inclusion F r v x) (w true)) hp
    change evalCLM F n (inclusion F r v x) (L p true) =
      evalCLM F n (inclusion F r v x)
        (P (rightRepresentation (inclusion F r v g) (L f)) true) at h
    rw [show P (rightRepresentation (inclusion F r v g) (L f)) true =
      CompactIndexAverage.averageLM j ν κ (rightAction F n (inclusion F r v g) (L f true))
        from rfl,
      CompactIndexAverage.eval_averageLM] at h
    simpa only [L, (liftPair_eval v B hB _ _).2, evalCLM_rightAction, map_mul,
      projection_inclusion, j, projection_placeCompactMap] using h

end CompactAverage

end RealExactCompactProjection

open MeasureTheory

local instance realExactCompactProjectionMeasurable (j : ℕ) :
    MeasurableSpace (unitaryCompact ℝ j) := borel _
local instance realExactCompactProjectionBorel (j : ℕ) :
    BorelSpace (unitaryCompact ℝ j) := ⟨rfl⟩

/-- Compact convolution, against a continuous weight with finite-dimensional left-translate
span, of a genuine right translate of a compact-finite real standard vector is again a
compact-finite standard vector; every specified real Whittaker intertwiner carries it to the
same compact convolution of the translated coefficient. -/
def RealExactCompactProjectionStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock) (a : ℝˣ) (ν : Measure (unitaryCompact ℝ (r + 1))),
    ν.IsHaarMeasure →
  ∀ (κ : C(unitaryCompact ℝ (r + 1), ℂ)),
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      fun h : unitaryCompact ℝ (r + 1) => fun k => κ (h⁻¹ * k))) →
  ∀ (B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)),
    IsRealWhittakerIntertwiner r ds a B →
  ∀ (f : Automorphic.realStandardKFinite (r + 1) ds) (g : Langlands.GeneralLinear (r + 1) ℝ),
    ∃ p : Automorphic.realStandardKFinite (r + 1) ds,
      (∀ x, p.val x = ∫ k : unitaryCompact ℝ (r + 1), κ k * f.val (x * k.val * g) ∂ν) ∧
      ∀ x, B p x = ∫ k : unitaryCompact ℝ (r + 1), κ k * B f (x * k.val * g) ∂ν

theorem realExactCompactProjection : RealExactCompactProjectionStatement := by
  intro r ds a ν hν κ hκ B hB f g
  exact RealExactCompactProjection.compact_projection_atPlace (F := ℚ)
    ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩ ν κ hκ B hB f g

end Langlands.Global.RankinSelbergGlobal
