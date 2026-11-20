import Langlands.Global.AdelicParabolicInductionArchimedean
import Langlands.Global.RankinSelberg.ArchimedeanPlaces
import Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction
import Langlands.Representation.Archimedean.PrincipalSeriesStability

/-! # Scalar local slices of smooth adelic block sections -/

noncomputable section

universe uF uV

namespace Langlands.Global.AdelicParabolicInduction

open NumberField Langlands.GeneralLinear AdelicBlockParabolic ArchimedeanGL
open Langlands.Archimedean (matrixModel rightDerivative)
open Langlands.Automorphic
open RankinSelbergGlobal
open scoped Classical Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type uF) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable (σ : Representation ℂ (FullLevi F B) V)

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "A" => ArchimedeanMatrix F n

section MatrixSlice

variable {𝕜 : Type} [RCLike 𝕜]
variable (ι : Langlands.GeneralLinear n 𝕜 →* ArchimedeanGL F n)

private def placeInclusion : Langlands.GeneralLinear n 𝕜 →* AdelicGL F n :=
  (AdelicGL.ofInfinite F n).toMonoidHom.comp
    ((archimedeanGLCoordinates F n).symm.toMonoidHom.comp ι)

private def scalarSlice (y : AdelicGL F n) (ℓ : V →L[ℂ] ℂ) :
    SmoothSections F B σ →ₗ[ℂ] (Langlands.GeneralLinear n 𝕜 → ℂ) where
  toFun f h := ℓ (evaluate F B σ f.val (y * placeInclusion F ι h))
  map_add' _ _ := funext fun _ => ℓ.map_add _ _
  map_smul' _ _ := funext fun _ => ℓ.map_smul _ _

private theorem scalarSlice_apply (y : AdelicGL F n) (ℓ : V →L[ℂ] ℂ)
    (f : SmoothSections F B σ) (h : Langlands.GeneralLinear n 𝕜) :
    scalarSlice F B σ ι y ℓ f h =
      ℓ ((smoothInfiniteSlice F B σ (AdelicGL.finite F n y) f).val
        (AdelicGL.infinite F n y * (archimedeanGLCoordinates F n).symm (ι h))) := by
  rw [smoothInfiniteSlice_apply]
  change ℓ (evaluate F B σ f.val
      (y * AdelicGL.ofInfinite F n ((archimedeanGLCoordinates F n).symm (ι h)))) = _
  rw [← AdelicGL.pair_projections F n y, AdelicGL.ofInfinite_eq_pair, AdelicGL.pair_mul]
  simp only [AdelicGL.infinite_pair, AdelicGL.finite_pair, mul_one]

private theorem scalarSlice_contMDiff (C : A) (L : Matrix (Fin n) (Fin n) 𝕜 →L[ℝ] A)
    (hι : ∀ h, (ι h : A) = C + L h.val)
    (y : AdelicGL F n) (ℓ : V →L[ℂ] ℂ) (f : SmoothSections F B σ) :
    ContMDiff (matrixModel 𝕜 n) 𝓘(ℝ, ℂ) ∞ (scalarSlice F B σ ι y ℓ f) := by
  have hplot : ContMDiff (matrixModel 𝕜 n) (𝓘(ℝ, A)) ∞ ι := by
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    have he : (Units.val : ArchimedeanGL F n → A) ∘ ι =
        fun h : Langlands.GeneralLinear n 𝕜 => C + L h.val := funext hι
    rw [he]
    exact contMDiff_const.add (L.contDiff.contMDiff.comp (Units.contMDiff_val (𝕜 := ℝ)))
  let s := smoothInfiniteSlice F B σ (AdelicGL.finite F n y) f
  have hs := (vectorSmoothMap F n V ℓ
    (vectorSmoothLeftTranslation F n (AdelicGL.infinite F n y) s)).property.comp hplot
  convert hs using 1
  funext g
  exact scalarSlice_apply F B σ ι y ℓ f g

private theorem scalarSlice_rightDerivative
    (C : A) (L : Matrix (Fin n) (Fin n) 𝕜 →L[ℝ] A)
    (hι : ∀ h, (ι h : A) = C + L h.val)
    (X : Matrix (Fin n) (Fin n) 𝕜) (Z : RealLieAlgebra F n)
    (hZ : realLieAlgebraToMatrix F n Z = L X)
    (hσ : ∀ p, Continuous (inducingRepresentation F B σ p))
    (y : AdelicGL F n) (ℓ : V →L[ℂ] ℂ) (f : SmoothSections F B σ)
    (g : Langlands.GeneralLinear n 𝕜) :
    rightDerivative (matrixModel 𝕜 n) X (scalarSlice F B σ ι y ℓ f) g =
      scalarSlice F B σ ι y ℓ (realLieAction F B σ hσ Z f) g := by
  let z := y * placeInclusion F ι g
  let a := AdelicGL.infinite F n z
  let s := smoothInfiniteSlice F B σ (AdelicGL.finite F n z) f
  let m := archimedeanGLCoordinates F n a
  let left : A →L[ℝ] A := (ContinuousLinearMap.mul ℝ A) (m : A)
  let ψ : Matrix (Fin n) (Fin n) 𝕜 → ℂ :=
    fun M => ℓ (vectorCoordinateExtension F n s ((m : A) * (C + L M)))
  have hleft (u : A) : left u = (m : A) * u := rfl
  have hone : C + L 1 = 1 := by
    simpa only [map_one, Units.val_one] using (hι 1).symm
  have h_at : left (C + L 1) = m.val := by rw [hone, hleft, mul_one]
  have ha : HasFDerivAt (vectorCoordinateExtension F n s)
      (fderiv ℝ (vectorCoordinateExtension F n s) m.val) (left (C + L 1)) := by
    rw [h_at]
    exact ((vectorCoordinateExtension_contDiffAt F n s m).differentiableAt (by simp)).hasFDerivAt
  have hcomp := ha.comp (1 : Matrix (Fin n) (Fin n) 𝕜)
    (left.hasFDerivAt.comp _ (L.hasFDerivAt.const_add C))
  have hψ := (ℓ.restrictScalars ℝ).hasFDerivAt.comp (1 : Matrix (Fin n) (Fin n) 𝕜) hcomp
  have hψ' : HasFDerivAt ψ
      ((ℓ.restrictScalars ℝ).comp
        ((fderiv ℝ (vectorCoordinateExtension F n s) m.val).comp (left.comp L))) 1 := by
    simpa only [ψ, Function.comp_def, hleft, ContinuousLinearMap.coe_restrictScalars'] using! hψ
  have h_orbit (h : Langlands.GeneralLinear n 𝕜) :
      scalarSlice F B σ ι y ℓ f (g * h) = ψ h.val := by
    have hg : y * placeInclusion F ι (g * h) =
        z * AdelicGL.ofInfinite F n ((archimedeanGLCoordinates F n).symm (ι h)) := by
      rw [map_mul, ← mul_assoc]
      rfl
    change ℓ (evaluate F B σ f.val (y * placeInclusion F ι (g * h))) = _
    rw [hg]
    change scalarSlice F B σ ι z ℓ f h = _
    rw [scalarSlice_apply]
    dsimp only [ψ, s, m, a]
    rw [← hι h, ← Units.val_mul, vectorCoordinateExtension_apply,
      map_mul (archimedeanGLCoordinates F n).symm,
      ContinuousMulEquiv.symm_apply_apply]
  have hd := Langlands.Archimedean.mfderiv_eq_fderiv_of_eq_comp
    h_orbit 1 hψ'.differentiableAt
  rw [Units.val_one] at hd
  have he : rightDerivative (matrixModel 𝕜 n) X (scalarSlice F B σ ι y ℓ f) g =
      fderiv ℝ ψ 1 X :=
    congrArg (fun D : Matrix (Fin n) (Fin n) 𝕜 →L[ℝ] ℂ => D X) hd
  rw [he, hψ'.fderiv]
  change _ = ℓ (evaluate F B σ (realLieAction F B σ hσ Z f).val z)
  rw [realLieAction_apply, evaluate_sectionDifferential, vectorSmoothDifferential_apply,
    vectorDirectionalValue, hZ]
  rfl

private theorem scalarSlice_compact (y : AdelicGL F n) (ℓ : V →L[ℂ] ℂ)
    (f : SmoothSections F B σ) (g k : Langlands.GeneralLinear n 𝕜)
    (c : standardInfiniteCompact F n)
    (hc : c.val = (archimedeanGLCoordinates F n).symm (ι k)) :
    scalarSlice F B σ ι y ℓ (compactRepresentation F B σ c f) g =
      scalarSlice F B σ ι y ℓ f (g * k) := by
  change ℓ (evaluate F B σ (compactRepresentation F B σ c f).val
    (y * placeInclusion F ι g)) = ℓ (evaluate F B σ f.val (y * placeInclusion F ι (g * k)))
  rw [evaluate_compactRepresentation, hc, map_mul, mul_assoc]
  rfl

end MatrixSlice

private def realPlaceLinear (v : RP) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] A :=
  ((realLieAlgebraToMatrix F n).toLinearMap.comp
    (realPlaceLieInclusion F n v).toLinearMap).toContinuousLinearMap

private def complexPlaceLinear (v : CP) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] A :=
  ((realLieAlgebraToMatrix F n).toLinearMap.comp
    (complexPlaceLieInclusion F n v).toLinearMap).toContinuousLinearMap

omit [NumberField F] in
private theorem realPlaceGL_affine (v : RP) (h : Langlands.GeneralLinear n ℝ) :
    (realPlaceGL F n v h : A) = realPlaceMatrixBase v + realPlaceLinear F v h.val := by
  change _ = realPlaceMatrixBase v + realLieAlgebraToMatrix F n (realPlaceLieInclusion F n v h.val)
  rw [realLieAlgebraToMatrix_realPlaceLieInclusion]
  refine Matrix.ext fun i j => Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · change ((Pi.mulSingle v h : RP → Langlands.GeneralLinear n ℝ) w).val i j =
      (if w = v then 0 else (1 : Matrix (Fin n) (Fin n) ℝ) i j) +
        (Pi.single v (h.val i j) : RP → ℝ) w
    by_cases hw : w = v
    · subst w
      simp
    · simp [hw]
  · change (1 : Matrix (Fin n) (Fin n) ℂ) i j = (1 : Matrix (Fin n) (Fin n) ℂ) i j + 0
    exact (add_zero _).symm

omit [NumberField F] in
private theorem complexPlaceGL_affine (v : CP) (h : Langlands.GeneralLinear n ℂ) :
    (complexPlaceGL F n v h : A) = complexPlaceMatrixBase v + complexPlaceLinear F v h.val := by
  change _ = complexPlaceMatrixBase v + realLieAlgebraToMatrix F n
    (complexPlaceLieInclusion F n v h.val)
  rw [realLieAlgebraToMatrix_complexPlaceLieInclusion]
  refine Matrix.ext fun i j => Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · change (1 : Matrix (Fin n) (Fin n) ℝ) i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j + 0
    exact (add_zero _).symm
  · change ((Pi.mulSingle v h : CP → Langlands.GeneralLinear n ℂ) w).val i j =
      (if w = v then 0 else (1 : Matrix (Fin n) (Fin n) ℂ) i j) +
        (Pi.single v (h.val i j) : CP → ℂ) w
    by_cases hw : w = v
    · subst w
      simp
    · simp [hw]

omit [NumberField F] in
private theorem realPlaceCompact_eq (v : RP) (k : Matrix.unitaryGroup (Fin n) ℝ) :
    (realPlaceCompactInclusion F n v k).val =
      (archimedeanGLCoordinates F n).symm (realPlaceGL F n v (Unitary.toUnits k)) := by
  apply (archimedeanGLCoordinates F n).injective
  rw [ContinuousMulEquiv.apply_symm_apply]
  apply Units.ext
  rw [coordinates_realPlaceCompactInclusion, realPlaceGL_affine]
  change _ = realPlaceMatrixBase v + realLieAlgebraToMatrix F n
    (realPlaceLieInclusion F n v (k : Matrix (Fin n) (Fin n) ℝ))
  rw [realLieAlgebraToMatrix_realPlaceLieInclusion, add_comm]

omit [NumberField F] in
private theorem complexPlaceCompact_eq (v : CP) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    (complexPlaceCompactInclusion F n v k).val =
      (archimedeanGLCoordinates F n).symm (complexPlaceGL F n v (Unitary.toUnits k)) := by
  apply (archimedeanGLCoordinates F n).injective
  rw [ContinuousMulEquiv.apply_symm_apply]
  apply Units.ext
  rw [coordinates_complexPlaceCompactInclusion, complexPlaceGL_affine]
  change _ = complexPlaceMatrixBase v + realLieAlgebraToMatrix F n
    (complexPlaceLieInclusion F n v (k : Matrix (Fin n) (Fin n) ℂ))
  rw [realLieAlgebraToMatrix_complexPlaceLieInclusion, add_comm]

/-- At a real place, evaluate a section along the right orbit of a fixed adelic point. -/
def realPlaceSlice (v : RP) (y : AdelicGL F n) (ℓ : V →L[ℂ] ℂ) :
    SmoothSections F B σ →ₗ[ℂ] (Langlands.GeneralLinear n ℝ → ℂ) :=
  scalarSlice F B σ (realPlaceGL F n v) y ℓ

/-- At a complex place, view the complex matrices with their underlying real smooth structure. -/
def complexPlaceSlice (v : CP) (y : AdelicGL F n) (ℓ : V →L[ℂ] ℂ) :
    SmoothSections F B σ →ₗ[ℂ] (Langlands.GeneralLinear n ℂ → ℂ) :=
  scalarSlice F B σ (complexPlaceGL F n v) y ℓ

theorem realPlaceSlice_apply (v : RP) (y : AdelicGL F n) (ℓ : V →L[ℂ] ℂ)
    (f : SmoothSections F B σ) (g : Langlands.GeneralLinear n ℝ) :
    realPlaceSlice F B σ v y ℓ f g =
      ℓ (evaluate F B σ f.val
        (y * AdelicGL.ofInfinite F n ((archimedeanGLCoordinates F n).symm (realPlaceGL F n v g)))) :=
  rfl

theorem complexPlaceSlice_apply (v : CP) (y : AdelicGL F n) (ℓ : V →L[ℂ] ℂ)
    (f : SmoothSections F B σ) (g : Langlands.GeneralLinear n ℂ) :
    complexPlaceSlice F B σ v y ℓ f g =
      ℓ (evaluate F B σ f.val
        (y * AdelicGL.ofInfinite F n ((archimedeanGLCoordinates F n).symm (complexPlaceGL F n v g)))) :=
  rfl

theorem realPlaceSlice_contMDiff (v : RP) (y : AdelicGL F n) (ℓ : V →L[ℂ] ℂ)
    (f : SmoothSections F B σ) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (realPlaceSlice F B σ v y ℓ f) :=
  scalarSlice_contMDiff F B σ (realPlaceGL F n v)
    (realPlaceMatrixBase v) (realPlaceLinear F v) (realPlaceGL_affine F v) y ℓ f

theorem complexPlaceSlice_contMDiff (v : CP) (y : AdelicGL F n) (ℓ : V →L[ℂ] ℂ)
    (f : SmoothSections F B σ) :
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (complexPlaceSlice F B σ v y ℓ f) :=
  scalarSlice_contMDiff F B σ (complexPlaceGL F n v)
    (complexPlaceMatrixBase v) (complexPlaceLinear F v) (complexPlaceGL_affine F v) y ℓ f

theorem realPlaceSlice_rightDerivative (hσ : ∀ p, Continuous (inducingRepresentation F B σ p))
    (v : RP) (y : AdelicGL F n) (ℓ : V →L[ℂ] ℂ) (f : SmoothSections F B σ)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    rightDerivative (matrixModel ℝ n) X (realPlaceSlice F B σ v y ℓ f) =
      realPlaceSlice F B σ v y ℓ (realLieAction F B σ hσ (realPlaceLieInclusion F n v X) f) := by
  funext g
  exact scalarSlice_rightDerivative F B σ (realPlaceGL F n v)
    (realPlaceMatrixBase v) (realPlaceLinear F v) (realPlaceGL_affine F v)
    X (realPlaceLieInclusion F n v X) rfl hσ y ℓ f g

theorem complexPlaceSlice_rightDerivative (hσ : ∀ p, Continuous (inducingRepresentation F B σ p))
    (v : CP) (y : AdelicGL F n) (ℓ : V →L[ℂ] ℂ) (f : SmoothSections F B σ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    rightDerivative (matrixModel ℂ n) X (complexPlaceSlice F B σ v y ℓ f) =
      complexPlaceSlice F B σ v y ℓ (realLieAction F B σ hσ (complexPlaceLieInclusion F n v X) f) := by
  funext g
  exact scalarSlice_rightDerivative F B σ (complexPlaceGL F n v)
    (complexPlaceMatrixBase v) (complexPlaceLinear F v) (complexPlaceGL_affine F v)
    X (complexPlaceLieInclusion F n v X) rfl hσ y ℓ f g

theorem realPlaceSlice_compact (v : RP) (y : AdelicGL F n) (ℓ : V →L[ℂ] ℂ)
    (f : SmoothSections F B σ) (k : Matrix.unitaryGroup (Fin n) ℝ)
    (g : Langlands.GeneralLinear n ℝ) :
    realPlaceSlice F B σ v y ℓ f (g * Unitary.toUnits k) =
      realPlaceSlice F B σ v y ℓ (compactRepresentation F B σ
        (realPlaceCompactInclusion F n v k) f) g :=
  (scalarSlice_compact F B σ (realPlaceGL F n v) y ℓ f g (Unitary.toUnits k)
    (realPlaceCompactInclusion F n v k) (realPlaceCompact_eq F v k)).symm

theorem complexPlaceSlice_compact (v : CP) (y : AdelicGL F n) (ℓ : V →L[ℂ] ℂ)
    (f : SmoothSections F B σ) (k : Matrix.unitaryGroup (Fin n) ℂ)
    (g : Langlands.GeneralLinear n ℂ) :
    complexPlaceSlice F B σ v y ℓ f (g * Unitary.toUnits k) =
      complexPlaceSlice F B σ v y ℓ (compactRepresentation F B σ
        (complexPlaceCompactInclusion F n v k) f) g :=
  (scalarSlice_compact F B σ (complexPlaceGL F n v) y ℓ f g (Unitary.toUnits k)
    (complexPlaceCompactInclusion F n v k) (complexPlaceCompact_eq F v k)).symm

end Langlands.Global.AdelicParabolicInduction
