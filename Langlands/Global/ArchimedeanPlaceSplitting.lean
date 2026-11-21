import Langlands.Global.ArchimedeanPlaceRestriction

/-! # Smooth splitting at one archimedean place -/

noncomputable section
universe u
open NumberField
open scoped Classical ContDiff Manifold Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000

namespace Langlands.Global.ArchimedeanGL

open RankinSelbergGlobal

variable {F : Type u} [Field F] {n : ℕ}

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

/-- The real-place projection of the group in mixed coordinates. -/
def realPlaceGLProjection (w : RP) : ArchimedeanGL F n →* RMˣ :=
  Units.map ((realPlaceScalarProjection F w).mapMatrix).toMonoidHom

/-- The complex-place projection of the group in mixed coordinates. -/
def complexPlaceGLProjection (w : CP) : ArchimedeanGL F n →* CMˣ :=
  Units.map ((complexPlaceScalarProjection F w).mapMatrix).toMonoidHom

theorem archimedeanGL_ext_places {g h : ArchimedeanGL F n}
    (hr : ∀ w : RP, realPlaceGLProjection w g = realPlaceGLProjection w h)
    (hc : ∀ w : CP, complexPlaceGLProjection w g = complexPlaceGLProjection w h) : g = h := by
  apply Units.ext
  refine Matrix.ext fun i j => Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · exact congrArg (fun x : RMˣ => x.val i j) (hr w)
  · exact congrArg (fun x : CMˣ => x.val i j) (hc w)

theorem realPlaceGLProjection_realPlaceGL (v w : RP) (x : RMˣ) :
    realPlaceGLProjection v (realPlaceGL F n w x) = (Pi.mulSingle w x : RP → RMˣ) v := by
  apply Units.ext
  rfl

theorem complexPlaceGLProjection_complexPlaceGL (v w : CP) (x : CMˣ) :
    complexPlaceGLProjection v (complexPlaceGL F n w x) = (Pi.mulSingle w x : CP → CMˣ) v := by
  apply Units.ext
  rfl

@[simp]
theorem realPlaceGLProjection_complexPlaceGL (v : RP) (w : CP) (x : CMˣ) :
    realPlaceGLProjection v (complexPlaceGL F n w x) = 1 := by
  apply Units.ext
  rfl

@[simp]
theorem complexPlaceGLProjection_realPlaceGL (v : CP) (w : RP) (x : RMˣ) :
    complexPlaceGLProjection v (realPlaceGL F n w x) = 1 := by
  apply Units.ext
  rfl

/-- Replace the chosen real coordinate by the identity and retain all other coordinates. -/
def realPlaceGLComplement (w : RP) (g : ArchimedeanGL F n) : ArchimedeanGL F n :=
  g * (realPlaceGL F n w (realPlaceGLProjection w g))⁻¹

/-- Replace the chosen complex coordinate by the identity and retain all other coordinates. -/
def complexPlaceGLComplement (w : CP) (g : ArchimedeanGL F n) : ArchimedeanGL F n :=
  g * (complexPlaceGL F n w (complexPlaceGLProjection w g))⁻¹

theorem realPlaceGLComplement_split (w : RP) (g : ArchimedeanGL F n) :
    realPlaceGLComplement w g * realPlaceGL F n w (realPlaceGLProjection w g) = g := by
  simp [realPlaceGLComplement, mul_assoc]

theorem complexPlaceGLComplement_split (w : CP) (g : ArchimedeanGL F n) :
    complexPlaceGLComplement w g * complexPlaceGL F n w (complexPlaceGLProjection w g) = g := by
  simp [complexPlaceGLComplement, mul_assoc]

theorem realPlaceGLComplement_commute (w : RP) (g : ArchimedeanGL F n) (x : RMˣ) :
    Commute (realPlaceGLComplement w g) (realPlaceGL F n w x) := by
  apply (commute_iff_eq _ _).2
  apply archimedeanGL_ext_places
  · intro v
    by_cases hv : v = w
    · subst v
      simp [realPlaceGLComplement, realPlaceGLProjection_realPlaceGL]
    · simp [map_mul, realPlaceGLProjection_realPlaceGL, Pi.mulSingle_eq_of_ne hv]
  · intro v
    simp

theorem complexPlaceGLComplement_commute (w : CP) (g : ArchimedeanGL F n) (x : CMˣ) :
    Commute (complexPlaceGLComplement w g) (complexPlaceGL F n w x) := by
  apply (commute_iff_eq _ _).2
  apply archimedeanGL_ext_places
  · intro v
    simp
  · intro v
    by_cases hv : v = w
    · subst v
      simp [complexPlaceGLComplement, complexPlaceGLProjection_complexPlaceGL]
    · simp [map_mul, complexPlaceGLProjection_complexPlaceGL, Pi.mulSingle_eq_of_ne hv]

variable [NumberField F]

theorem contMDiff_realPlaceGLProjection (w : RP) :
    ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, RM) ∞ (realPlaceGLProjection (n := n) w) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  let P : ArchimedeanMatrix F n →L[ℝ] RM :=
    ((realPlaceScalarProjection F w).mapMatrix).toLinearMap.toContinuousLinearMap
  exact P.contDiff.contMDiff.comp Units.contMDiff_val

theorem contMDiff_complexPlaceGLProjection (w : CP) :
    ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, CM) ∞ (complexPlaceGLProjection (n := n) w) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  let P : ArchimedeanMatrix F n →L[ℝ] CM :=
    ((complexPlaceScalarProjection F w).mapMatrix).toLinearMap.toContinuousLinearMap
  exact P.contDiff.contMDiff.comp Units.contMDiff_val

theorem contMDiff_realPlaceGLComplement (w : RP) :
    ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, ArchimedeanMatrix F n) ∞
      (realPlaceGLComplement (n := n) w) :=
  contMDiff_id.mul ((contMDiff_realPlaceGL (n := n) w).comp (contMDiff_realPlaceGLProjection w)).inv

theorem contMDiff_complexPlaceGLComplement (w : CP) :
    ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, ArchimedeanMatrix F n) ∞
      (complexPlaceGLComplement (n := n) w) :=
  contMDiff_id.mul
    ((contMDiff_complexPlaceGL (n := n) w).comp (contMDiff_complexPlaceGLProjection w)).inv

/-- At each infinite place, the actual group is split by a smooth projection and a
smooth complementary factor that commutes with the local subgroup. -/
def PlaceSplittingStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (m : ℕ),
    (∀ w : {v : InfinitePlace K // v.IsReal},
      ContMDiff 𝓘(ℝ, ArchimedeanMatrix K m) 𝓘(ℝ, Matrix (Fin m) (Fin m) ℝ) ∞
        (realPlaceGLProjection (n := m) w) ∧
      ContMDiff 𝓘(ℝ, ArchimedeanMatrix K m) 𝓘(ℝ, ArchimedeanMatrix K m) ∞
        (realPlaceGLComplement (n := m) w) ∧
      (∀ g, realPlaceGLComplement w g * realPlaceGL K m w (realPlaceGLProjection w g) = g) ∧
      ∀ g x, Commute (realPlaceGLComplement w g) (realPlaceGL K m w x)) ∧
    ∀ w : {v : InfinitePlace K // v.IsComplex},
      ContMDiff 𝓘(ℝ, ArchimedeanMatrix K m) 𝓘(ℝ, Matrix (Fin m) (Fin m) ℂ) ∞
        (complexPlaceGLProjection (n := m) w) ∧
      ContMDiff 𝓘(ℝ, ArchimedeanMatrix K m) 𝓘(ℝ, ArchimedeanMatrix K m) ∞
        (complexPlaceGLComplement (n := m) w) ∧
      (∀ g, complexPlaceGLComplement w g * complexPlaceGL K m w (complexPlaceGLProjection w g) = g) ∧
      ∀ g x, Commute (complexPlaceGLComplement w g) (complexPlaceGL K m w x)

theorem placeSplitting : PlaceSplittingStatement.{u} := by
  intro K _ _ m
  exact ⟨fun w => ⟨contMDiff_realPlaceGLProjection w, contMDiff_realPlaceGLComplement w,
    realPlaceGLComplement_split w, realPlaceGLComplement_commute w⟩,
    fun w => ⟨contMDiff_complexPlaceGLProjection w, contMDiff_complexPlaceGLComplement w,
      complexPlaceGLComplement_split w, complexPlaceGLComplement_commute w⟩⟩

end Langlands.Global.ArchimedeanGL
