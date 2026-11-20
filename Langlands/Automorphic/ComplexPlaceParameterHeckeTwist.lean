import Langlands.Representation.Archimedean.ComplexStandardDeterminantTwist
import Langlands.Automorphic.HeckeTwist.OperatorTwist
import Langlands.Automorphic.HeckeTwist.DifferentialMultiplier
import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.Automorphic.IsobaricComplexPlaceParameter
import Langlands.Global.ArchimedeanPlaceCompact
import Langlands.Global.ArchimedeanPlaceLie
import Langlands.Global.Factors.HeckeArchimedeanComponents
import Langlands.Automorphic.AssociatedGammaAutomorphicTwist
import Langlands.Automorphic.HeckeDeterminantTwistStatement

/-!
# Complex-place parameters under twists by arbitrary Hecke characters

If an actual automorphic realization `S` has the standard-module parameter `ds` at a complex
place `v`, and the Hecke character `μ` has the local parameter `d` at `v`, then the twist
`S.heckeDeterminantTwist μ` (multiplication by `μ ∘ det`) has the parameter of the blocks
of `ds` each multiplied by `d`. No condition at infinity is imposed on `μ`. Consequently, if
`T` is the determinant multiple of `S` by `χ` and has the parameter `ds` at `v`, then `S` has
the blocks of `ds` multiplied by the parameter of `χ⁻¹` at `v`. Every Hecke character has a
parameter at every complex place, and parameters multiply for products of Hecke characters.

The two inputs from the global side are the values of the archimedean determinant character of
`μ` on the unitary group at `v` and its derivative at `1` along the Lie algebra at `v`; both are
those of `η ∘ det` on `GL_n(ℂ)` for the parameter character `η` of `μ` at `v`.
-/
noncomputable section

universe u

open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.ComplexPlaceHeckeTwist

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.LocalFactor.Archimedean
open Langlands.Archimedean Langlands.Archimedean.ComplexDeterminantTwist NumberField

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F]

local notation "RP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

/-! ## Local parameters of Hecke characters -/

/-- Every Hecke character has a parameter at every complex place: the polar data of its local
character in the selected coordinate. -/
theorem exists_hasComplexPlaceParameter (μ : HeckeCharacter F) (v : CP) :
    ∃ d : ComplexCharacterData, μ.HasComplexPlaceParameter v d :=
  ⟨HeckeFunctionalEquation.complexCompletionCharacterData v.2 (μ.infiniteComponent v.1),
    fun x => (HeckeFunctionalEquation.isComplexCharacterPresentation_complexCompletionCharacterData
      v.2 (μ.infiniteComponent v.1) x).symm⟩

/-- Parameters multiply for products of Hecke characters. -/
theorem HasComplexPlaceParameter.mul {μ μ' : HeckeCharacter F} {v : CP}
    {d d' : ComplexCharacterData} (h : μ.HasComplexPlaceParameter v d)
    (h' : μ'.HasComplexPlaceParameter v d') :
    (μ * μ').HasComplexPlaceParameter v (d.mul d') := by
  intro x
  change μ.infiniteComponent v.1 x * μ'.infiniteComponent v.1 x = _
  rw [h x, h' x]
  rfl

/-! ## The complex place inside the mixed coordinates -/

section Mixed

open scoped Classical


open Classical in
/-- The element of the mixed space equal to `z` at the complex place `v` and to `1` at every
other place. -/
def mixedSingle (v : CP) (z : ℂ) : mixedEmbedding.mixedSpace F :=
  (1, Pi.mulSingle v z)

omit [NumberField F] in
/-- The unit of the infinite adeles equal to `x` at `v` and `1` elsewhere, read in mixed
coordinates, is `mixedSingle v` of `x` read in the coordinate of `v`. -/
theorem ringEquiv_mixedSpace_ofCompletion (v : CP) (x : InfiniteCompletion F v.1) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (InfiniteAdeleRing.ofCompletion v.1 x) =
      mixedSingle v (NumberField.InfinitePlace.Completion.extensionEmbedding v.1 x) := by
  classical
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  apply Prod.ext
  · funext w
    have hw : w.1 ≠ v.1 := fun h => by
      have h1 := w.2
      rw [h] at h1
      exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr v.2) h1
    change NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        (InfiniteAdeleRing.ofCompletion v.1 x w.1) = 1
    rw [InfiniteAdeleRing.ofCompletion_apply, Pi.mulSingle_eq_of_ne hw, map_one]
  · funext w
    change NumberField.InfinitePlace.Completion.extensionEmbedding w.1
        (InfiniteAdeleRing.ofCompletion v.1 x w.1) =
      (Pi.mulSingle v (NumberField.InfinitePlace.Completion.extensionEmbedding v.1 x) : CP → ℂ) w
    rw [InfiniteAdeleRing.ofCompletion_apply]
    by_cases hw : w = v
    · subst hw
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · have hw' : w.1 ≠ v.1 := fun h => hw (Subtype.ext h)
      rw [Pi.mulSingle_eq_of_ne hw', Pi.mulSingle_eq_of_ne hw, map_one]

/-- The infinite idele inserted at one place is the idele of that place. -/
theorem infiniteIdelesInclusion_ofCompletion (v : NumberField.InfinitePlace F)
    (x : (InfiniteCompletion F v)ˣ) :
    infiniteIdelesInclusion F (Units.map (InfiniteAdeleRing.ofCompletion v) x) =
      infiniteIdeleInclusion F v x := by
  apply Units.ext
  rfl

/-- The archimedean character of `μ` at the element `mixedSingle v z` is the parameter
character of `μ` at `v` evaluated at `z`, also off the units, where both sides are `0`. -/
theorem unitsCharacterExtension_mixedSingle {μ : HeckeCharacter F} {v : CP}
    {d : ComplexCharacterData} (hμ : μ.HasComplexPlaceParameter v d) (z : ℂ) :
    unitsCharacterExtension μ.mixedCharacter (mixedSingle v z) =
      unitsCharacterExtension d.character z := by
  by_cases hz : IsUnit z
  · obtain ⟨z, rfl⟩ := hz
    let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex v.2
    let x : (InfiniteCompletion F v.1)ˣ := Units.map e.symm.toMonoidHom z
    have hx : NumberField.InfinitePlace.Completion.extensionEmbedding v.1 (x : InfiniteCompletion F v.1) =
        (z : ℂ) := e.apply_symm_apply (z : ℂ)
    let u : (mixedEmbedding.mixedSpace F)ˣ :=
      Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).toMonoidHom
        (Units.map (InfiniteAdeleRing.ofCompletion v.1) x)
    have hu : (u : mixedEmbedding.mixedSpace F) = mixedSingle v (z : ℂ) := by
      change InfiniteAdeleRing.ringEquiv_mixedSpace F (InfiniteAdeleRing.ofCompletion v.1 x) = _
      rw [ringEquiv_mixedSpace_ofCompletion, hx]
    rw [← hu, unitsCharacterExtension_unit, unitsCharacterExtension_unit]
    have hsymm : Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toRingHom.toMonoidHom u =
        Units.map (InfiniteAdeleRing.ofCompletion v.1) x := by
      apply Units.ext
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _
    congr 1
    change μ.onIdeles (infiniteIdelesInclusion F
      (Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toRingHom.toMonoidHom u)) = _
    rw [hsymm, infiniteIdelesInclusion_ofCompletion]
    change μ.infiniteComponent v.1 x = _
    rw [hμ x]
    congr 1
    apply Units.ext
    exact hx
  · have hm : ¬ IsUnit (mixedSingle v z) := by
      intro hm
      apply hz
      have h2 := hm.map ((Pi.evalRingHom (fun _ : CP => ℂ) v).comp
        (RingHom.snd (RP → ℝ) (CP → ℂ)))
      simpa [mixedSingle] using h2
    simp only [unitsCharacterExtension, hm, hz, ↓reduceDIte]

variable (n : ℕ)

open Classical in
/-- The archimedean matrix equal to `Y` at the complex place `v` and to the identity at every
other place. -/
def placeMatrix (v : CP) (Y : Matrix (Fin n) (Fin n) ℂ) : ArchimedeanMatrix F n :=
  fun i j => ((fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) i j),
    Function.update (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) i j) v (Y i j))

/-- The real-place coordinate ring homomorphism of the mixed space. -/
def realCoordinate (w : RP) : mixedEmbedding.mixedSpace F →+* ℝ :=
  (Pi.evalRingHom (fun _ : RP => ℝ) w).comp (RingHom.fst (RP → ℝ) (CP → ℂ))

/-- The complex-place coordinate ring homomorphism of the mixed space. -/
def complexCoordinate (w : CP) : mixedEmbedding.mixedSpace F →+* ℂ :=
  (Pi.evalRingHom (fun _ : CP => ℂ) w).comp (RingHom.snd (RP → ℝ) (CP → ℂ))

omit [NumberField F] in
/-- The determinant of `placeMatrix v Y` is `mixedSingle v (det Y)`. -/
theorem det_placeMatrix (v : CP) (Y : Matrix (Fin n) (Fin n) ℂ) :
    (placeMatrix n v Y).det = mixedSingle v Y.det := by
  classical
  apply Prod.ext
  · funext w
    have h := RingHom.map_det (realCoordinate w) (placeMatrix n v Y)
    have hM : (realCoordinate w).mapMatrix (placeMatrix n v Y) = 1 := by
      ext i j
      rfl
    change realCoordinate w (placeMatrix n v Y).det = _
    rw [h, hM, Matrix.det_one]
    rfl
  · funext w
    have h := RingHom.map_det (complexCoordinate w) (placeMatrix n v Y)
    change complexCoordinate w (placeMatrix n v Y).det = _
    rw [h]
    by_cases hw : w = v
    · subst hw
      have hM : (complexCoordinate w).mapMatrix (placeMatrix n w Y) = Y := by
        ext i j
        simp [complexCoordinate, placeMatrix]
      rw [hM]
      simp [mixedSingle]
    · have hM : (complexCoordinate w).mapMatrix (placeMatrix n v Y) = 1 := by
        ext i j
        simp [complexCoordinate, placeMatrix, Function.update_of_ne hw]
      rw [hM, Matrix.det_one]
      simp [mixedSingle, Pi.mulSingle_eq_of_ne hw]

omit [NumberField F] in
/-- The identity at `v` gives the identity matrix. -/
theorem placeMatrix_one (v : CP) : placeMatrix n v (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  funext i j
  apply Prod.ext
  · funext w
    by_cases hij : i = j <;> simp [placeMatrix, Matrix.one_apply, hij]
  · funext w
    by_cases hw : w = v
    · subst hw
      by_cases hij : i = j <;> simp [placeMatrix, Matrix.one_apply, hij]
    · by_cases hij : i = j <;> simp [placeMatrix, Matrix.one_apply, hij]

/-- The linear part of `placeMatrix v`: the matrix `Y` at `v` and zero elsewhere. -/
def placeLinear (v : CP) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ArchimedeanMatrix F n where
  toFun Y i j := (0, Pi.single v (Y i j))
  map_add' Y Z := by
    funext i j
    apply Prod.ext
    · simp
    · funext w
      by_cases hw : w = v <;> simp [hw]
  map_smul' r Y := by
    funext i j
    apply Prod.ext
    · simp
    · funext w
      by_cases hw : w = v <;> simp [hw]

omit [NumberField F] in
/-- `placeMatrix v` is affine with linear part `placeLinear v`. -/
theorem placeMatrix_eq (v : CP) (Y : Matrix (Fin n) (Fin n) ℂ) :
    placeMatrix n v Y = placeMatrix n v 0 + placeLinear n v Y := by
  funext i j
  apply Prod.ext
  · funext w
    simp [placeMatrix, placeLinear]
  · funext w
    by_cases hw : w = v
    · subst hw
      simp [placeMatrix, placeLinear]
    · simp [placeMatrix, placeLinear, hw]

/-- The continuous linear part of `placeMatrix v`. -/
def placeLinearCLM (v : CP) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ArchimedeanMatrix F n :=
  LinearMap.toContinuousLinearMap (placeLinear n v)

/-- The derivative of `placeMatrix v` is its linear part. -/
theorem hasFDerivAt_placeMatrix (v : CP) (Y : Matrix (Fin n) (Fin n) ℂ) :
    HasFDerivAt (placeMatrix (F := F) n v) (placeLinearCLM n v) Y := by
  have h : HasFDerivAt (fun Z => placeMatrix (F := F) n v 0 + placeLinearCLM (F := F) n v Z)
      (placeLinearCLM (F := F) n v) Y :=
    (placeLinearCLM (F := F) n v).hasFDerivAt.const_add (placeMatrix (F := F) n v 0)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun Z => ?_)
  exact placeMatrix_eq n v Z

omit [NumberField F] in
/-- The linear part of `placeMatrix v` is the inclusion of the Lie algebra at `v`. -/
theorem placeLinear_eq (v : CP) (X : Matrix (Fin n) (Fin n) ℂ) :
    placeLinear n v X = realLieAlgebraToMatrix F n (complexPlaceLieInclusion F n v X) := by
  have hc := realLiePlaceCoordinates_complexInclusion F n v X
  funext i j
  apply Prod.ext
  · funext w
    have h := congrArg (fun p => p.1 w i j) hc
    exact h.symm
  · funext w
    have h := congrArg (fun p => p.2 w i j) hc
    refine Eq.trans ?_ h.symm
    change (Pi.single v (X i j) : CP → ℂ) w = (Pi.single v X : CP → Matrix (Fin n) (Fin n) ℂ) w i j
    by_cases hw : w = v
    · subst hw
      simp
    · simp [Pi.single_eq_of_ne hw]

/-- The archimedean determinant character of `μ`, extended by zero to all archimedean
matrices. -/
def characterExtension (μ : HeckeCharacter F) (M : ArchimedeanMatrix F n) : ℂ :=
  unitsCharacterExtension μ.mixedCharacter M.det

/-- On invertible archimedean matrices the extension is the archimedean determinant character
of `μ`. -/
theorem characterExtension_unit (μ : HeckeCharacter F) (h : ArchimedeanGL F n) :
    characterExtension n μ (h : ArchimedeanMatrix F n) =
      ((μ.infiniteDeterminantCharacter n ((archimedeanGLCoordinates F n).symm h) : ℂˣ) : ℂ) := by
  rw [characterExtension, HeckeCharacter.infiniteDeterminantCharacter_apply,
    HeckeCharacter.adelicDeterminant_ofInfinite_coordinates,
    ← Matrix.GeneralLinearGroup.val_det_apply, unitsCharacterExtension_unit]

/-- The extension is differentiable at the identity. -/
theorem differentiableAt_characterExtension_one (μ : HeckeCharacter F) :
    DifferentiableAt ℝ (characterExtension n μ) 1 := by
  have hd := contDiffAt_unitsCharacterExtension μ.mixedCharacter 1
  rw [Units.val_one, ← Matrix.det_one (n := Fin n)] at hd
  exact (hd.comp (1 : ArchimedeanMatrix F n)
    (contDiff_archimedeanDet F n).contDiffAt).differentiableAt (by simp)

/-- Restricted to the complex place `v`, the extension is the extension of `η ∘ det` on
`GL_n(ℂ)` for the parameter character `η` of `μ` at `v`. -/
theorem characterExtension_placeMatrix {μ : HeckeCharacter F} {v : CP}
    {d : ComplexCharacterData} (hμ : μ.HasComplexPlaceParameter v d) :
    (fun Y => characterExtension n μ (placeMatrix n v Y)) =
      unitsExtension (detCharacter (n := n) d.character) := by
  funext Y
  rw [characterExtension, det_placeMatrix, unitsCharacterExtension_mixedSingle hμ]
  by_cases hY : IsUnit Y
  · obtain ⟨g, rfl⟩ := hY
    rw [unitsExtension_val, detCharacter, ← Matrix.GeneralLinearGroup.val_det_apply,
      unitsCharacterExtension_unit]
  · rw [unitsExtension_of_not_isUnit _ hY]
    have hd : ¬ IsUnit Y.det := fun h => hY ((Matrix.isUnit_iff_isUnit_det Y).mpr h)
    simp only [unitsCharacterExtension, hd, ↓reduceDIte]

/-- The derivative at `1` of the archimedean determinant character of `μ` along a direction at
the complex place `v` is the derivative at `1` of `η ∘ det` on `GL_n(ℂ)`, for the parameter
character `η` of `μ` at `v`. -/
theorem characterDifferential_complexPlaceLieInclusion {μ : HeckeCharacter F} {v : CP}
    {d : ComplexCharacterData} (hμ : μ.HasComplexPlaceParameter v d)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    characterDifferential (μ.infiniteDeterminantCharacter n)
        (μ.infiniteDeterminantCharacter_mem_smoothFunctions n)
        (complexPlaceLieInclusion F n v X) =
      rightDerivative (matrixModel ℂ n) X (detCharacter (n := n) d.character) 1 := by
  have hE : ∀ h : ArchimedeanGL F n, characterExtension n μ (h : ArchimedeanMatrix F n) =
      (characterFunction (μ.infiniteDeterminantCharacter n)
        (μ.infiniteDeterminantCharacter_mem_smoothFunctions n)).val
          ((archimedeanGLCoordinates F n).symm h) := fun h => characterExtension_unit n μ h
  have h1 := smoothDifferential_eq_of_extension F n (complexPlaceLieInclusion F n v X)
    (characterFunction (μ.infiniteDeterminantCharacter n)
      (μ.infiniteDeterminantCharacter_mem_smoothFunctions n)) (characterExtension n μ) hE 1
  change (smoothDifferential F n (complexPlaceLieInclusion F n v X)
    (characterFunction (μ.infiniteDeterminantCharacter n)
      (μ.infiniteDeterminantCharacter_mem_smoothFunctions n))).val 1 = _
  rw [h1, map_one, Units.val_one, one_mul, ← placeLinear_eq,
    rightDerivative_eq_fderiv (contMDiff_detCharacter _) X 1, Units.val_one, one_mul,
    ← characterExtension_placeMatrix n hμ]
  have hd := differentiableAt_characterExtension_one n μ
  rw [← placeMatrix_one (F := F) n v] at hd
  have hchain : HasFDerivAt (fun Y => characterExtension n μ (placeMatrix n v Y))
      ((fderiv ℝ (characterExtension n μ) (placeMatrix n v 1)).comp (placeLinearCLM n v)) 1 :=
    hd.hasFDerivAt.comp (1 : Matrix (Fin n) (Fin n) ℂ) (hasFDerivAt_placeMatrix n v 1)
  rw [hchain.fderiv, placeMatrix_one]
  rfl

omit [NumberField F] in
/-- In mixed coordinates, the unitary group at `v` is inserted as `placeMatrix v`. -/
theorem coordinates_complexPlaceCompactInclusion (v : CP) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ((archimedeanGLCoordinates F n (complexPlaceCompactInclusion F n v k).val :
      ArchimedeanGL F n) : ArchimedeanMatrix F n) = placeMatrix n v (k : Matrix (Fin n) (Fin n) ℂ) := by
  funext i j
  apply Prod.ext
  · funext w
    have h := congrFun (congrFun (realMatrix_complexPlaceCompactInclusion F n v w k) i) j
    exact h
  · funext w
    have h := congrFun (congrFun (complexMatrix_complexPlaceCompactInclusion F n v w k) i) j
    refine h.trans ?_
    by_cases hw : w = v
    · subst hw
      simp [placeMatrix]
    · simp [placeMatrix, Pi.mulSingle_eq_of_ne hw, Function.update_of_ne hw]

/-- On the unitary group at a complex place `v`, the determinant character of `μ` is `η ∘ det`
for the parameter character `η` of `μ` at `v`. -/
theorem adelicDeterminant_complexPlaceCompactInclusion {μ : HeckeCharacter F} {v : CP}
    {d : ComplexCharacterData} (hμ : μ.HasComplexPlaceParameter v d)
    (g : Langlands.GeneralLinear n ℂ) (hg : (g : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ((μ.adelicDeterminant n (AdelicGL.ofInfinite F n
        (complexPlaceCompactInclusion F n v ⟨g, hg⟩).val) : ℂˣ) : ℂ) =
      detCharacter d.character g := by
  have hK : (complexPlaceCompactInclusion F n v ⟨g, hg⟩).val =
      (archimedeanGLCoordinates F n).symm
        (archimedeanGLCoordinates F n (complexPlaceCompactInclusion F n v ⟨g, hg⟩).val) :=
    ((archimedeanGLCoordinates F n).symm_apply_apply _).symm
  rw [hK, HeckeCharacter.adelicDeterminant_ofInfinite_coordinates,
    ← unitsCharacterExtension_unit, Matrix.GeneralLinearGroup.val_det_apply,
    coordinates_complexPlaceCompactInclusion, det_placeMatrix,
    unitsCharacterExtension_mixedSingle hμ, detCharacter,
    ← unitsCharacterExtension_unit d.character, Matrix.GeneralLinearGroup.val_det_apply]

end Mixed

end Langlands.Automorphic.ComplexPlaceHeckeTwist

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.LocalFactor.Archimedean
open Langlands.Archimedean Langlands.Archimedean.ComplexDeterminantTwist
open Langlands.Automorphic.ComplexPlaceHeckeTwist NumberField

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance complexPlaceHeckeTwistRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance complexPlaceHeckeTwistContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance complexPlaceHeckeTwistSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance complexPlaceHeckeTwistFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance complexPlaceHeckeTwistStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

local instance complexPlaceHeckeTwistSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

set_option maxHeartbeats 1600000 in
/-- The twist rule for an arbitrary target list `ds'` whose position characters are those of
`ds` times the parameter character `η` of `μ` at `v`. -/
theorem HasComplexPlaceParameter.heckeDeterminantTwist_of_positionCharacter
    {S : OperatorRealization F n}
    {v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}}
    {ds ds' : List ComplexCharacterData} (h : S.HasComplexPlaceParameter v ds)
    {μ : HeckeCharacter F} {d : ComplexCharacterData} (hμ : μ.HasComplexPlaceParameter v d)
    (hlen : ds'.length = n)
    (hpos : ∀ (i : Fin n) (z : ℂˣ), complexPositionCharacter ds i z =
      complexPositionCharacter ds' i z * ((d.character⁻¹ z : ℂˣ) : ℂ)) :
    (S.heckeDeterminantTwist μ).HasComplexPlaceParameter v ds' := by
  obtain ⟨-, A, hA, hK, hL⟩ := h
  refine ⟨hlen, (S.heckeDeterminantTwistEquiv μ).toLinearEquiv.toLinearMap ∘ₗ A ∘ₗ
    kFiniteDetMul d.character⁻¹ hpos, ?_, ?_, ?_⟩
  · exact (S.heckeDeterminantTwistEquiv μ).injective.comp
      (hA.comp (kFiniteDetMul_injective d.character⁻¹ hpos))
  · intro k f
    refine ⟨rightTranslation_mem_kFiniteFunctions_principalSeries _ _ f.2 k.2, ?_⟩
    obtain ⟨hmem, hKeq⟩ := hK k (kFiniteDetMul d.character⁻¹ hpos f)
    have h1 : A (kFiniteDetMul d.character⁻¹ hpos
        ⟨_, rightTranslation_mem_kFiniteFunctions_principalSeries _ _ f.2 k.2⟩) =
          detCharacter d.character (k : Langlands.GeneralLinear n ℂ) • A ⟨_, hmem⟩ := by
      rw [kFiniteDetMul_rightTranslation d.character⁻¹ hpos f k.2, map_smul, detCharacter_inv,
        inv_inv]
    have hc := adelicDeterminant_complexPlaceCompactInclusion n hμ
      (k : Langlands.GeneralLinear n ℂ) k.2
    have hcomp := S.heckeDeterminantTwistEquiv_compact μ
      (complexPlaceCompactInclusion F n v ⟨((k : Langlands.GeneralLinear n ℂ) :
        Matrix (Fin n) (Fin n) ℂ), k.2⟩) (A (kFiniteDetMul d.character⁻¹ hpos f))
    rw [hc] at hcomp
    exact (congrArg (S.heckeDeterminantTwistEquiv μ) h1).trans
      ((map_smul (S.heckeDeterminantTwistEquiv μ) _ _).trans
        ((congrArg (fun y => detCharacter d.character (k : Langlands.GeneralLinear n ℂ) •
          S.heckeDeterminantTwistEquiv μ y) hKeq).trans hcomp.symm))
  · intro X f
    refine ⟨rightDerivative_mem_kFiniteFunctions_principalSeries _ _ f.2 X, ?_⟩
    obtain ⟨hmem, hLeq⟩ := hL X (kFiniteDetMul d.character⁻¹ hpos f)
    have h1 : A (kFiniteDetMul d.character⁻¹ hpos
        ⟨_, rightDerivative_mem_kFiniteFunctions_principalSeries _ _ f.2 X⟩) =
          A ⟨_, hmem⟩ + rightDerivative (matrixModel ℂ n) X
            (detCharacter (n := n) d.character) 1 • A (kFiniteDetMul d.character⁻¹ hpos f) := by
      rw [kFiniteDetMul_rightDerivative d.character⁻¹ hpos f X,
        rightDerivative_detCharacter_inv, neg_neg, map_add, map_smul]
    have hshift : heckeEnvelopingShift n μ
        (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v (1 ⊗ₜ X))) =
          envelopingGenerator F n (complexPlaceComplexLieInclusion F n v (1 ⊗ₜ X)) +
            algebraMap ℂ (EnvelopingAlgebra F n)
              (rightDerivative (matrixModel ℂ n) X (detCharacter (n := n) d.character) 1) := by
      rw [heckeEnvelopingShift, characterShift, envelopingShift_generator,
        complexPlaceComplexLieInclusion_tmul, complexCharacterDifferential_tmul, one_mul,
        characterDifferential_complexPlaceLieInclusion n hμ]
    have h2 : S.envelopingAction (heckeEnvelopingShift n μ
        (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v (1 ⊗ₜ X))))
          (A (kFiniteDetMul d.character⁻¹ hpos f)) =
        S.complexPlaceLieAction v (1 ⊗ₜ X) (A (kFiniteDetMul d.character⁻¹ hpos f)) +
          rightDerivative (matrixModel ℂ n) X (detCharacter (n := n) d.character) 1 •
            A (kFiniteDetMul d.character⁻¹ hpos f) :=
      calc S.envelopingAction (heckeEnvelopingShift n μ
            (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v (1 ⊗ₜ X))))
              (A (kFiniteDetMul d.character⁻¹ hpos f))
          = S.envelopingAction
              (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v (1 ⊗ₜ X)) +
                algebraMap ℂ (EnvelopingAlgebra F n)
                  (rightDerivative (matrixModel ℂ n) X (detCharacter (n := n) d.character) 1))
              (A (kFiniteDetMul d.character⁻¹ hpos f)) :=
            congrArg (fun u => S.envelopingAction u (A (kFiniteDetMul d.character⁻¹ hpos f)))
              hshift
        _ = S.envelopingAction
              (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v (1 ⊗ₜ X)))
                (A (kFiniteDetMul d.character⁻¹ hpos f)) +
            S.envelopingAction (algebraMap ℂ (EnvelopingAlgebra F n)
              (rightDerivative (matrixModel ℂ n) X (detCharacter (n := n) d.character) 1))
                (A (kFiniteDetMul d.character⁻¹ hpos f)) :=
            LinearMap.congr_fun (map_add S.envelopingAction _ _) _
        _ = _ :=
            congrArg (S.complexPlaceLieAction v (1 ⊗ₜ X) (A (kFiniteDetMul d.character⁻¹ hpos f)) + ·)
              ((LinearMap.congr_fun (S.envelopingAction.commutes _) _).trans
                (Module.algebraMap_end_apply ℂ ℂ S.Space _ _))
    have hdiff := S.heckeDeterminantTwistEquiv_differential μ
      (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v (1 ⊗ₜ X)))
        (A (kFiniteDetMul d.character⁻¹ hpos f))
    exact (congrArg (S.heckeDeterminantTwistEquiv μ) h1).trans
      ((congrArg (fun y => S.heckeDeterminantTwistEquiv μ (y +
          rightDerivative (matrixModel ℂ n) X (detCharacter (n := n) d.character) 1 •
            A (kFiniteDetMul d.character⁻¹ hpos f))) hLeq).trans
        ((congrArg (S.heckeDeterminantTwistEquiv μ) h2.symm).trans
          (hdiff.symm.trans (OperatorRealization.complexPlaceLieAction_apply
            (S.heckeDeterminantTwist μ) v (1 ⊗ₜ X)
              (S.heckeDeterminantTwistEquiv μ (A (kFiniteDetMul d.character⁻¹ hpos f)))).symm)))

/-- **Twist rule.** If `S` has the standard-module parameter `ds` at the complex place `v` and
the Hecke character `μ` has the parameter `d` at `v`, then `S ⊗ (μ ∘ det)` has the parameter
of the blocks of `ds` each multiplied by `d`. -/
theorem HasComplexPlaceParameter.heckeDeterminantTwist_mul {S : OperatorRealization F n}
    {v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}}
    {ds : List ComplexCharacterData} (h : S.HasComplexPlaceParameter v ds)
    {μ : HeckeCharacter F} {d : ComplexCharacterData} (hμ : μ.HasComplexPlaceParameter v d) :
    (S.heckeDeterminantTwist μ).HasComplexPlaceParameter v (ds.map fun e => e.mul d) :=
  h.heckeDeterminantTwist_of_positionCharacter hμ (by rw [List.length_map]; exact h.1)
    (complexPositionCharacter_map_mul_inv d ds h.1)

/-- The twist `S.heckeDeterminantTwist χ` is the determinant multiple of `S` by `χ`. -/
theorem isDeterminantMultiple_heckeDeterminantTwist (S : OperatorRealization F n)
    (χ : HeckeCharacter F) : IsDeterminantMultiple χ S (S.heckeDeterminantTwist χ) :=
  ⟨(S.heckeDeterminantTwistEquiv χ).toLinearEquiv, fun _ => rfl⟩

/-- A realization is the twist by `χ⁻¹` of its determinant multiple by `χ`. -/
theorem IsDeterminantMultiple.eq_heckeDeterminantTwist_inv {χ : HeckeCharacter F}
    {S T : OperatorRealization F n} (h : IsDeterminantMultiple χ S T) :
    S = T.heckeDeterminantTwist χ⁻¹ := by
  have hT : T = S.heckeDeterminantTwist χ := h.eq (isDeterminantMultiple_heckeDeterminantTwist S χ)
  rw [hT, heckeDeterminantTwist_heckeDeterminantTwist_inv]

/-- **Untwisting parameters.** If `T` is the determinant multiple of `S` by `χ` and has the
parameter `ds` at the complex place `v`, and `χ⁻¹` has the parameter `e` at `v`, then `S` has
the parameter of the blocks of `ds` each multiplied by `e`. -/
theorem IsDeterminantMultiple.hasComplexPlaceParameter {χ : HeckeCharacter F}
    {S T : OperatorRealization F n} (h : IsDeterminantMultiple χ S T)
    {v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}}
    {ds : List ComplexCharacterData} (hT : T.HasComplexPlaceParameter v ds)
    {e : ComplexCharacterData} (he : χ⁻¹.HasComplexPlaceParameter v e) :
    S.HasComplexPlaceParameter v (ds.map fun d => d.mul e) :=
  h.eq_heckeDeterminantTwist_inv ▸ hT.heckeDeterminantTwist_mul he

end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- The twist rule for an actual cuspidal realization. -/
theorem hasComplexPlaceParameter_heckeDeterminantTwist_mul (S : CuspidalOperatorRealization F r)
    {v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}}
    {ds : List ComplexCharacterData} (h : S.isoClass.HasComplexPlaceParameter v ds)
    {μ : HeckeCharacter F} {d : ComplexCharacterData} (hμ : μ.HasComplexPlaceParameter v d) :
    (S.heckeDeterminantTwist μ).isoClass.HasComplexPlaceParameter v
      (ds.map fun e => e.mul d) :=
  OperatorRealization.HasComplexPlaceParameter.heckeDeterminantTwist_mul h hμ

end CuspidalOperatorRealization

end Langlands.Automorphic
