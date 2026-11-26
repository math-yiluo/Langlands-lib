import Langlands.Global.ArchimedeanAnalyticJetProof
import Langlands.Global.ArchimedeanCompactAverageTranslation
import Langlands.Global.ArchimedeanCompactComponentCoverageProof
import Langlands.Global.ArchimedeanCompactGroupFiniteProof
import Langlands.Global.ArchimedeanEnvelopingJetProof
import Langlands.Global.ArchimedeanJointFiniteAnalyticityProof
import Langlands.Global.ArchimedeanPlaceEnveloping
import Langlands.Global.ArchimedeanPlaceRestriction
import Langlands.Global.ArchimedeanSeparateJointFiniteProof
import Langlands.Global.RankinSelberg.RealLocalWhittakerModel
import Langlands.Representation.Archimedean.RealPrincipalSeriesInfinitesimalCharacter
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible

/-! # Compact averages of genuine right translates of real Whittaker coefficients

For a weight on `O(n)` with finite-dimensional span of left translates, the compact average of a
genuine right translate of a compact-finite real standard vector is again compact-finite, and
every coefficient map compatible with `O(n)` and right derivatives commutes with this average.
The proof lifts the pair `(f, B f)` to the archimedean group of `ℚ` and applies the Library's
translation theorem for jointly finite families. See the paired Markdown.
-/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean NumberField MeasureTheory
open scoped Classical ContDiff Manifold Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanGL

namespace RealWhittakerTranslateProjection

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

/-! ### Finite compact convolution kernels -/

section Kernel

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- A continuous function whose left translates span a finite-dimensional space has a separated
convolution kernel `κ(x⁻¹ k) = ∑ⱼ αⱼ(x) βⱼ(k)` with continuous `βⱼ`. -/
theorem exists_separated_kernel (κ : K → ℂ) (hκ : Continuous κ)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun x : K => fun k => κ (x⁻¹ * k)))) :
    ∃ (m : ℕ) (α β : Fin m → K → ℂ),
      (∀ j, Continuous (β j)) ∧ ∀ x k, κ (x⁻¹ * k) = ∑ j, α j x * β j k := by
  let V := Submodule.span ℂ (Set.range fun x : K => fun k => κ (x⁻¹ * k))
  let : FiniteDimensional ℂ V := hfin
  let b := Module.finBasis ℂ V
  let shift (x : K) : V := ⟨fun k => κ (x⁻¹ * k), Submodule.subset_span ⟨x, rfl⟩⟩
  have hcont (v : V) : Continuous v.val := by
    refine Submodule.span_induction (p := fun f _ => Continuous f) ?_ continuous_const ?_ ?_ v.2
    · rintro _ ⟨x, rfl⟩
      exact hκ.comp (continuous_const.mul continuous_id)
    · intro _ _ _ _ h h'
      exact h.add h'
    · intro c _ _ h
      exact continuous_const.smul h
  refine ⟨Module.finrank ℂ V, fun j x => b.repr (shift x) j, fun j => (b j).val,
    fun j => hcont (b j), ?_⟩
  intro x k
  have hb := congrArg (fun v : V => v.val k) (b.sum_repr (shift x))
  simpa only [shift, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] using hb.symm

end Kernel

/-! ### Lifts from one real place -/

section Lift

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)

local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "M" => Matrix (Fin n) (Fin n) ℝ
local notation "A" => ArchimedeanMatrix F n
local notation "AG" => Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing F)
local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "S" => SmoothFunctions F n

/-- The matrix entries at the real place `v`. -/
def matrixProjection (v : RP) : A →ₐ[ℝ] M :=
  (realPlaceScalarProjection F v).mapMatrix

/-- The projection of the archimedean group to its factor at the real place `v`. -/
def projection (v : RP) : AG →* G :=
  (Matrix.GeneralLinearGroup.map (realPlaceScalarProjection F v).toRingHom).comp
    (archimedeanGLCoordinates F n).toMonoidHom

/-- The inclusion of the factor at the real place `v`, with identities elsewhere. -/
def inclusion (v : RP) : G →* AG :=
  (archimedeanGLCoordinates F n).symm.toMonoidHom.comp (realPlaceGL F n v)

omit [NumberField F] in
theorem projection_inclusion (v : RP) (g : G) : projection F r v (inclusion F r v g) = g := by
  apply Units.ext
  change (Matrix.GeneralLinearGroup.map (realPlaceScalarProjection F v).toRingHom
    (archimedeanGLCoordinates F n ((archimedeanGLCoordinates F n).symm
      (realPlaceGL F n v g)))).val = g.val
  rw [ContinuousMulEquiv.apply_symm_apply]
  refine Matrix.ext fun i j => ?_
  change (((Pi.mulSingle v g : RP → G) v : G) : M) i j = g.val i j
  rw [Pi.mulSingle_eq_same]

/-- The orthogonal factor at `v` of a standard compact element. -/
def compactProjection (v : RP) (k : standardInfiniteCompact F n) :
    Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨(projection F r v k.val).val, ((mem_standardInfiniteCompact_iff F n k.val).mp k.property).1 v⟩

omit [NumberField F] in
theorem toUnits_compactProjection (v : RP) (k : standardInfiniteCompact F n) :
    Unitary.toUnits (compactProjection F r v k) = projection F r v k.val :=
  Units.ext rfl

/-- Pullback of a smooth function on `GL_n(ℝ)` along the projection at `v`. -/
def pullback (v : RP) (W : G → ℂ)
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

theorem pullback_apply (v : RP) (W : G → ℂ)
    (hW : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ W) (g : AG) :
    (pullback F r v W hW).val g = W (projection F r v g) := rfl

theorem pullback_differential (v : RP) (X : RealLieAlgebra F n) (W : G → ℂ)
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

variable {r ds} in
/-- A linear map from the compact-finite real standard module to smooth functions on
`GL_n(ℝ)`, compatible with right translation by `O(n)` and with right derivatives. -/
def IsRealCoefficientMap (B : D) : Prop :=
  (∀ f : V, ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (B f)) ∧
  (∀ (k : unitaryCompact ℝ n) (f f' : V),
    (f' : G → ℂ) = Whittaker.rightTranslation ℂ G (k : G) (f : G → ℂ) →
      B f' = Whittaker.rightTranslation ℂ G (k : G) (B f)) ∧
  ∀ (X : M) (f f' : V),
    (f' : G → ℂ) = rightDerivative (matrixModel ℝ n) X (f : G → ℂ) →
      B f' = rightDerivative (matrixModel ℝ n) X (B f)

variable {r ds} in
theorem isRealCoefficientMap_of_intertwiner {a : ℝˣ} {B : D}
    (hB : IsRealWhittakerIntertwiner r ds a B) : IsRealCoefficientMap B :=
  ⟨hB.2.1, hB.2.2.2.1, hB.2.2.2.2⟩

theorem isRealCoefficientMap_subtype : IsRealCoefficientMap (V).subtype :=
  ⟨fun f => contMDiff_of_mem_realStandardModule f.2.1, fun _ _ _ h => h, fun _ _ _ h => h⟩

/-- The pullbacks of all coefficients of `B` at the real place `v`. -/
def coefficients (v : RP) (B : D)
    (hB : ∀ f : V, ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (B f)) : V →ₗ[ℂ] S where
  toFun f := pullback F r v (B f) (hB f)
  map_add' f e := by apply Subtype.ext; funext g; exact congrFun (map_add B f e) _
  map_smul' z f := by apply Subtype.ext; funext g; exact congrFun (map_smul B z f) _

variable {F r ds}

theorem coefficients_enveloping (v : RP) {B : D} (hB : IsRealCoefficientMap B)
    (u : EnvelopingAlgebra F n) (f : V) :
    ArchimedeanGL.envelopingAction F n u (coefficients F r ds v B hB.1 f) =
      coefficients F r ds v B hB.1
        (Archimedean.envelopingAction π (realPlaceEnvelopingProjection F n v u) f) := by
  induction u using Archimedean.InfinitesimalCharacter.envInduction generalizing f with
  | algebraMap z =>
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  | ι Z =>
    change ArchimedeanGL.envelopingAction F n (envelopingGenerator F n Z) _ =
      coefficients F r ds v B hB.1
        (Archimedean.envelopingAction π
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
      apply Subtype.ext
      funext g
      change (smoothDifferential F n X (pullback F r v (B f) (hB.1 f))).val g =
        B (π ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n v X) f) (projection F r v g)
      rw [pullback_differential F r v X (B f) (hB.1 f)]
      exact (congrFun (hB.2.2 _ f _ (realStandardLie_one_tmul_apply_coe n ds _ f)) _).symm
    | add X Y hX hY =>
      simp only [map_add, LinearMap.add_apply, hX, hY]
  | mul u w hu hw =>
    rw [envelopingAction_mul, hw, hu, map_mul, map_mul, Module.End.mul_apply]
  | add u w hu hw =>
    simp only [map_add, LinearMap.add_apply, hu, hw]

theorem coefficients_compact (v : RP) {B : D} (hB : IsRealCoefficientMap B)
    (k : standardInfiniteCompact F n) (f : V) :
    smoothRightAction F n k.val (coefficients F r ds v B hB.1 f) =
      coefficients F r ds v B hB.1 (ρ (compactProjection F r v k) f) := by
  let k' : unitaryCompact ℝ n := ⟨Unitary.toUnits (compactProjection F r v k),
    (compactProjection F r v k).property⟩
  apply Subtype.ext
  funext g
  change B f (projection F r v (g * k.val)) =
    B (ρ (compactProjection F r v k) f) (projection F r v g)
  rw [hB.2.1 k' f _ (realStandardRep_apply_coe n ds _ f), map_mul]
  change B f (_ * _) = B f (_ * Unitary.toUnits (compactProjection F r v k))
  rw [toUnits_compactProjection]

omit [NumberField F] in
theorem projection_mem_center (v : RP) (z : EnvelopingCenter F n) :
    realPlaceEnvelopingProjection F n v z.val ∈
      Subalgebra.center ℂ (RealPlaceEnvelopingAlgebra n) := by
  rw [Subalgebra.mem_center_iff]
  intro w
  obtain ⟨u, rfl⟩ := realPlaceEnvelopingProjection_surjective F n v w
  simpa only [map_mul] using congrArg (realPlaceEnvelopingProjection F n v)
    ((Subalgebra.mem_center_iff.mp z.property) u)

theorem coefficients_jointFinite (v : RP) {B : D} (hB : IsRealCoefficientMap B) (f : V) :
    IsJointFinite F n (coefficients F r ds v B hB.1 f) := by
  let L := coefficients F r ds v B hB.1
  apply separateJointFinite F n (L f)
  · have hle : centerOrbitSpan F n (L f) ≤ Submodule.span ℂ {L f} := by
      apply Submodule.span_le.mpr
      rintro _ ⟨z, rfl⟩
      change ArchimedeanGL.envelopingAction F n z.val (L f) ∈ Submodule.span ℂ {L f}
      rw [coefficients_enveloping v hB]
      obtain ⟨c, hc⟩ := realStandardLie_hasInfinitesimalCharacter n ds _
        (projection_mem_center v z)
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
      rw [coefficients_compact v hB]
      exact Submodule.mem_map_of_mem
        (Langlands.FiniteVectors.action_mem_orbitSpan ρ (compactProjection F r v k) f)
    exact Submodule.finiteDimensional_of_le hle

end Lift


/-! ### Compact averages of a simultaneous translate -/

section CompactAverage

open Set
open ArchimedeanGL.DerivativeSmoothFunctions
open ArchimedeanGL.SmoothFamily (averageLM averagedTranslate_mem compactRepresentation
  rightRepresentation)

local instance translateProjectionMeasurable (j : ℕ) :
    MeasurableSpace (unitaryCompact ℝ j) := borel _
local instance translateProjectionBorel (j : ℕ) : BorelSpace (unitaryCompact ℝ j) := ⟨rfl⟩

variable {F : Type} [Field F] [NumberField F] {r : ℕ} {ds : List RealBlock}

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "n" => (r + 1)
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "A" => InfiniteAdelicGL F n
local notation "K" => standardInfiniteCompact F n
local notation "U" => unitaryCompact ℝ n
local notation "Std" => Automorphic.realStandardKFinite n ds
local notation "Fam" => ArchimedeanGL.SmoothFamily F n Bool

/-- The pair of pulled-back functions `(f, B f)` at the real place `v`. -/
def liftPair (v : RP) (B : Std →ₗ[ℂ] (G → ℂ)) (hB : IsRealCoefficientMap B) :
    Std →ₗ[ℂ] Fam :=
  LinearMap.pi fun b => (toSmooth F n).symm.toLinearMap.comp
    (Bool.rec (coefficients F r ds v (Std).subtype (isRealCoefficientMap_subtype r ds).1)
      (coefficients F r ds v B hB.1) b)

theorem liftPair_compact (v : RP) {B : Std →ₗ[ℂ] (G → ℂ)} (hB : IsRealCoefficientMap B)
    (k : K) (f : Std) :
    compactRepresentation k (liftPair v B hB f) =
      liftPair v B hB (realStandardRep n ds (compactProjection F r v k) f) := by
  funext b
  apply (toSmooth F n).injective
  rw [ArchimedeanGL.SmoothFamily.compactRepresentation_apply, compactAction_apply,
    toSmooth_rightAction]
  cases b
  · simpa only [liftPair, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using
      coefficients_compact v (isRealCoefficientMap_subtype r ds) k f
  · simpa only [liftPair, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using coefficients_compact v hB k f

theorem liftPair_enveloping (v : RP) {B : Std →ₗ[ℂ] (G → ℂ)} (hB : IsRealCoefficientMap B)
    (q : EnvelopingAlgebra F n) (f : Std) :
    q • liftPair v B hB f =
      liftPair v B hB (Archimedean.envelopingAction (realStandardLie n ds)
        (realPlaceEnvelopingProjection F n v q) f) := by
  funext b
  apply (toSmooth F n).injective
  change toSmooth F n (operator F n q ((liftPair v B hB f) b)) = _
  rw [toSmooth_operator]
  cases b
  · simpa only [liftPair, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using
      coefficients_enveloping v (isRealCoefficientMap_subtype r ds) q f
  · simpa only [liftPair, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using coefficients_enveloping v hB q f

theorem liftPair_eval (v : RP) {B : Std →ₗ[ℂ] (G → ℂ)} (hB : IsRealCoefficientMap B)
    (f : Std) (g : A) :
    evalCLM F n g (liftPair v B hB f false) = f.val (projection F r v g) ∧
    evalCLM F n g (liftPair v B hB f true) = B f (projection F r v g) := by
  simp only [evalCLM_apply, liftPair, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact ⟨rfl, rfl⟩

theorem liftPair_compactFinite (v : RP) {B : Std →ₗ[ℂ] (G → ℂ)} (hB : IsRealCoefficientMap B)
    (f : Std) :
    FiniteDimensional ℂ (FiniteVectors.orbitSpan (compactRepresentation (ι := Bool))
      (liftPair v B hB f)) := by
  let Q := FiniteVectors.orbitSpan (realStandardRep n ds) f
  have : Module.Finite ℂ Q := (isRealGKModule_realStandardModule n ds).1 f
  apply Submodule.finiteDimensional_of_le (S₂ := Q.map (liftPair v B hB))
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  change compactRepresentation k (liftPair v B hB f) ∈ _
  rw [liftPair_compact]
  exact Submodule.mem_map_of_mem (FiniteVectors.action_mem_orbitSpan _ _ _)

/-- The orthogonal group at `v` inside the standard compact subgroup of the archimedean group. -/
def placeCompactMap (v : RP) : C(U, A) :=
  ⟨fun k => (realPlaceCompactInclusion F n v ⟨k.val.val, k.2⟩).val,
    continuous_subtype_val.comp ((realPlaceCompactInclusion F n v).continuous.comp
      ((Units.continuous_val.comp continuous_subtype_val).subtype_mk _))⟩

omit [NumberField F] in
theorem placeCompactMap_mem (v : RP) (k : U) : placeCompactMap v k ∈ K :=
  (realPlaceCompactInclusion F n v ⟨k.val.val, k.2⟩).2

omit [NumberField F] in
theorem projection_placeCompactMap (v : RP) (k : U) :
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
theorem compact_projection_atPlace (v : RP) (ν : Measure U) [ν.IsHaarMeasure]
    (κ : C(U, ℂ)) (hκ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      fun h : U => fun k => κ (h⁻¹ * k)))) {B : Std →ₗ[ℂ] (G → ℂ)}
    (hB : IsRealCoefficientMap B) (f : Std) (g : G) :
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
      (FiniteVectors.orbitSpan compactRepresentation w) := by
    obtain ⟨w, rfl⟩ := hw
    exact liftPair_compactFinite v hB w
  have hPQ : Q.map P ≤ Q := by
    apply Submodule.map_le_iff_le_comap.mpr
    intro w hw
    let O := FiniteVectors.orbitSpan (compactRepresentation (ι := Bool)) w
    have : FiniteDimensional ℂ O := hfin w hw
    have hO : O ≤ Q := Submodule.span_le.mpr (by
      rintro _ ⟨k, rfl⟩
      change compactRepresentation k w ∈ Q
      simpa only [one_smul] using hstab k 1 w hw)
    have ha : P w ∈ O.topologicalClosure := by
      apply ArchimedeanGL.SmoothFamily.averageLM_mem_topologicalClosure
      intro k
      exact O.le_topologicalClosure
        (FiniteVectors.action_mem_orbitSpan compactRepresentation ⟨j k, placeCompactMap_mem v k⟩ w)
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
      apply eq_of_eqOn_unitaryCompact_of_mem_principalSeries
        (realStandardModule_le_principalSeries n ds f₁.2.1)
        (realStandardModule_le_principalSeries n ds f₂.2.1)
      intro k hk
      have eq := congrFun he (⟨k, hk⟩ : U)
      change evalCLM F n (inclusion F r v k) (liftPair v B hB f₁ false) =
        evalCLM F n (inclusion F r v k) (liftPair v B hB f₂ false) at eq
      rw [(liftPair_eval v hB f₁ _).1, (liftPair_eval v hB f₂ _).1, projection_inclusion] at eq
      exact eq
    subst f₂
    rfl
  obtain ⟨d, α, β, hβ, hsep⟩ := exists_separated_kernel κ κ.continuous hκ
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
      simp only [L, (liftPair_eval v hB f _).1, map_mul, projection_inclusion,
        projection_placeCompactMap, j]
      have hs : (∫ k : U, κ (x⁻¹ * k) * f.val k.val ∂ν) =
          ∑ l, α l x * (∫ k : U, β l k * f.val k.val ∂ν) := by
        simp_rw [hsep, Finset.sum_mul, mul_assoc]
        rw [integral_finsetSum]
        · exact Finset.sum_congr rfl (fun l _ => integral_const_mul _ _)
        · intro l _
          exact (((hβ l).mul ((contMDiff_of_mem_realStandardModule f.2.1).continuous.comp
            continuous_subtype_val)).const_mul
            (α l x)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      rw [show (∫ k : U, κ k * f.val (x.val * k.val) ∂ν) =
        ∫ k : U, κ (x⁻¹ * k) * f.val k.val ∂ν by
          rw [← integral_mul_left_eq_self (fun k : U => κ (x⁻¹ * k) * f.val k.val) x]
          simp only [inv_mul_cancel_left]; rfl, hs]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [he]
    exact Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
  have hRank : FiniteDimensional ℂ (Q.map P) := by
    let e : (Q.map P) →ₗ[ℂ] T := (E.comp (Q.map P).subtype).codRestrict T (fun w => hET w w.2)
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
        coefficients_jointFinite v (isRealCoefficientMap_subtype r ds) f
    · simpa only [L, liftPair, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using coefficients_jointFinite v hB f
  obtain ⟨p, hp⟩ := averagedTranslate_mem j ν κ Q hstab (placeCompactMap_mem v) hfin hRank
    (LinearMap.mem_range_self L f) hjoint (inclusion F r v g)
  refine ⟨p, fun x => ?_, fun x => ?_⟩
  · have h := congrArg (fun w : Fam => evalCLM F n (inclusion F r v x) (w false)) hp
    change evalCLM F n (inclusion F r v x) (L p false) =
      evalCLM F n (inclusion F r v x) (P (rightRepresentation (inclusion F r v g) (L f)) false) at h
    rw [show P (rightRepresentation (inclusion F r v g) (L f)) false =
      CompactIndexAverage.averageLM j ν κ (rightAction F n (inclusion F r v g) (L f false)) from rfl,
      CompactIndexAverage.eval_averageLM] at h
    simpa only [L, (liftPair_eval v hB _ _).1, evalCLM_rightAction, map_mul,
      projection_inclusion, j, projection_placeCompactMap] using h
  · have h := congrArg (fun w : Fam => evalCLM F n (inclusion F r v x) (w true)) hp
    change evalCLM F n (inclusion F r v x) (L p true) =
      evalCLM F n (inclusion F r v x) (P (rightRepresentation (inclusion F r v g) (L f)) true) at h
    rw [show P (rightRepresentation (inclusion F r v g) (L f)) true =
      CompactIndexAverage.averageLM j ν κ (rightAction F n (inclusion F r v g) (L f true)) from rfl,
      CompactIndexAverage.eval_averageLM] at h
    simpa only [L, (liftPair_eval v hB _ _).2, evalCLM_rightAction, map_mul,
      projection_inclusion, j, projection_placeCompactMap] using h

end CompactAverage

end RealWhittakerTranslateProjection


open RealWhittakerTranslateProjection

section Statement

local instance translateProjectionMeasurable' (j : ℕ) :
    MeasurableSpace (unitaryCompact ℝ j) := borel _
local instance translateProjectionBorel' (j : ℕ) : BorelSpace (unitaryCompact ℝ j) := ⟨rfl⟩

variable (r : ℕ) in
/-- A compact average, with a weight whose left translates span a finite-dimensional space, of a
genuine right translate of a compact-finite real standard vector is again a compact-finite
standard vector; a coefficient map compatible with `O(n)` and with right derivatives carries
it to the same average of the translated coefficient. -/
def RealWhittakerTranslateProjectionStatement : Prop :=
  ∀ (ds : List RealBlock) (ν : Measure (unitaryCompact ℝ (r + 1))), ν.IsHaarMeasure →
  ∀ (κ : C(unitaryCompact ℝ (r + 1), ℂ)),
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      fun h : unitaryCompact ℝ (r + 1) => fun k => κ (h⁻¹ * k))) →
  ∀ (B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)),
    IsRealCoefficientMap B →
  ∀ (f : Automorphic.realStandardKFinite (r + 1) ds) (g : Langlands.GeneralLinear (r + 1) ℝ),
    ∃ p : Automorphic.realStandardKFinite (r + 1) ds,
      (∀ x, p.val x = ∫ k : unitaryCompact ℝ (r + 1), κ k * f.val (x * k.val * g) ∂ν) ∧
      ∀ x, B p x = ∫ k : unitaryCompact ℝ (r + 1), κ k * B f (x * k.val * g) ∂ν

/-- The proof works at the real place of `ℚ`. -/
theorem realWhittakerTranslateProjection (r : ℕ) : RealWhittakerTranslateProjectionStatement r := by
  intro ds ν hν κ hκ B hB f g
  exact compact_projection_atPlace (F := ℚ) ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
    ν κ hκ hB f g

end Statement

end Langlands.Global.RankinSelbergGlobal
