import Langlands.Global.ArchimedeanCompact
import Mathlib.Algebra.Group.Pi.Lemmas

/-! # Actual single-place embeddings in the standard infinite compact subgroup -/

noncomputable section

universe u

open scoped Classical
open NumberField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000

namespace Langlands.Global

variable (F : Type u) [Field F] (n : ℕ)

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ

namespace ArchimedeanCompactFactors

/-- The original coordinate product maps continuously onto its actual compact image. -/
def toStandardCompact : ArchimedeanCompactFactors F n →ₜ* standardInfiniteCompact F n where
  toFun p := ⟨toInfiniteAdelicGL F n p, ⟨p, rfl⟩⟩
  map_one' := Subtype.ext ((toInfiniteAdelicGL F n).map_one)
  map_mul' p q := Subtype.ext ((toInfiniteAdelicGL F n).map_mul p q)
  continuous_toFun := (toInfiniteAdelicGL F n).continuous.subtype_mk _

@[simp] theorem toStandardCompact_val (p : ArchimedeanCompactFactors F n) :
    (toStandardCompact F n p).val = toInfiniteAdelicGL F n p := rfl

theorem toStandardCompact_injective : Function.Injective (toStandardCompact F n) := by
  intro p q h
  exact toInfiniteAdelicGL_injective F n (congrArg Subtype.val h)

theorem toStandardCompact_surjective : Function.Surjective (toStandardCompact F n) := by
  rintro ⟨g, p, hp⟩
  exact ⟨p, Subtype.ext hp⟩

/-- Insert one real orthogonal matrix and identities in every other factor. -/
def realPlaceFactor (v : RP) : RK →ₜ* ArchimedeanCompactFactors F n where
  toMonoidHom := (MonoidHom.mulSingle (fun _ : RP => RK) v).prod 1
  continuous_toFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro w
      by_cases h : w = v
      · subst w
        simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
        exact continuous_id
      · simpa [h] using (continuous_const : Continuous (fun _ : RK => (1 : RK)))
    · exact continuous_const

/-- Insert one complex unitary matrix and identities in every other factor. -/
def complexPlaceFactor (v : CP) : CK →ₜ* ArchimedeanCompactFactors F n where
  toMonoidHom := (1 : CK →* (RP → RK)).prod
    (MonoidHom.mulSingle (fun _ : CP => CK) v)
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_const
    · apply continuous_pi
      intro w
      by_cases h : w = v
      · subst w
        simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
        exact continuous_id
      · simpa [h] using (continuous_const : Continuous (fun _ : CK => (1 : CK)))

@[simp] theorem realPlaceFactor_fst (v w : RP) (k : RK) :
    (realPlaceFactor F n v k).1 w = (Pi.mulSingle v k : RP → RK) w := rfl

@[simp] theorem realPlaceFactor_snd (v : RP) (w : CP) (k : RK) :
    (realPlaceFactor F n v k).2 w = 1 := rfl

@[simp] theorem complexPlaceFactor_fst (v : CP) (w : RP) (k : CK) :
    (complexPlaceFactor F n v k).1 w = 1 := rfl

@[simp] theorem complexPlaceFactor_snd (v w : CP) (k : CK) :
    (complexPlaceFactor F n v k).2 w = (Pi.mulSingle v k : CP → CK) w := rfl

theorem realPlaceFactor_injective (v : RP) :
    Function.Injective (realPlaceFactor F n v) := by
  intro k l h
  simpa only [realPlaceFactor_fst, Pi.mulSingle_eq_same] using
    congrArg (fun p : ArchimedeanCompactFactors F n => p.1 v) h

theorem complexPlaceFactor_injective (v : CP) :
    Function.Injective (complexPlaceFactor F n v) := by
  intro k l h
  simpa only [complexPlaceFactor_snd, Pi.mulSingle_eq_same] using
    congrArg (fun p : ArchimedeanCompactFactors F n => p.2 v) h

end ArchimedeanCompactFactors

/-- A real-place orthogonal group embeds continuously in the actual standard compact. -/
def realPlaceCompactInclusion (v : RP) : RK →ₜ* standardInfiniteCompact F n :=
  (ArchimedeanCompactFactors.toStandardCompact F n).comp
    (ArchimedeanCompactFactors.realPlaceFactor F n v)

/-- A complex-place unitary group embeds continuously in the actual standard compact. -/
def complexPlaceCompactInclusion (v : CP) : CK →ₜ* standardInfiniteCompact F n :=
  (ArchimedeanCompactFactors.toStandardCompact F n).comp
    (ArchimedeanCompactFactors.complexPlaceFactor F n v)

theorem realPlaceCompactInclusion_injective (v : RP) :
    Function.Injective (realPlaceCompactInclusion F n v) :=
  (ArchimedeanCompactFactors.toStandardCompact_injective F n).comp
    (ArchimedeanCompactFactors.realPlaceFactor_injective F n v)

theorem complexPlaceCompactInclusion_injective (v : CP) :
    Function.Injective (complexPlaceCompactInclusion F n v) :=
  (ArchimedeanCompactFactors.toStandardCompact_injective F n).comp
    (ArchimedeanCompactFactors.complexPlaceFactor_injective F n v)

theorem realMatrix_realPlaceCompactInclusion (v w : RP) (k : RK) :
    ArchimedeanGL.realMatrix F n
      (archimedeanGLCoordinates F n (realPlaceCompactInclusion F n v k).val) w =
        ((Pi.mulSingle v k : RP → RK) w).val := by
  change ArchimedeanGL.realMatrix F n
    (archimedeanGLCoordinates F n (ArchimedeanCompactFactors.toInfiniteAdelicGL F n
      (ArchimedeanCompactFactors.realPlaceFactor F n v k))) w = _
  rw [ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
  rfl

theorem complexMatrix_complexPlaceCompactInclusion (v w : CP) (k : CK) :
    ArchimedeanGL.complexMatrix F n
      (archimedeanGLCoordinates F n (complexPlaceCompactInclusion F n v k).val) w =
        ((Pi.mulSingle v k : CP → CK) w).val := by
  change ArchimedeanGL.complexMatrix F n
    (archimedeanGLCoordinates F n (ArchimedeanCompactFactors.toInfiniteAdelicGL F n
      (ArchimedeanCompactFactors.complexPlaceFactor F n v k))) w = _
  rw [ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
  rfl

theorem complexMatrix_realPlaceCompactInclusion (v : RP) (w : CP) (k : RK) :
    ArchimedeanGL.complexMatrix F n
      (archimedeanGLCoordinates F n (realPlaceCompactInclusion F n v k).val) w = 1 := by
  change ArchimedeanGL.complexMatrix F n
    (archimedeanGLCoordinates F n (ArchimedeanCompactFactors.toInfiniteAdelicGL F n
      (ArchimedeanCompactFactors.realPlaceFactor F n v k))) w = _
  rw [ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
  rfl

theorem realMatrix_complexPlaceCompactInclusion (v : CP) (w : RP) (k : CK) :
    ArchimedeanGL.realMatrix F n
      (archimedeanGLCoordinates F n (complexPlaceCompactInclusion F n v k).val) w = 1 := by
  change ArchimedeanGL.realMatrix F n
    (archimedeanGLCoordinates F n (ArchimedeanCompactFactors.toInfiniteAdelicGL F n
      (ArchimedeanCompactFactors.complexPlaceFactor F n v k))) w = _
  rw [ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
  rfl

end Langlands.Global
