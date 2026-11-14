import Langlands.Global.RankinSelberg.UnequalIntegrals
import Langlands.Global.GeneralLinearBlockIntrinsicMeasure
import Langlands.Group.GL.LowerBlockLocalizationCoordinates

/-! # Actual global Whittaker integrals for unequal ranks -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance whittakerSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance whittakerSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

/-- The actual adelic upper unitriangular subgroup. -/
abbrev unipotentAdelic (n : ℕ) : Subgroup (Points F n) :=
  AdelicSubgroupPoints.adelicPoints F (Scheme F n) (upperUnipotent F n)

/-- The principal upper unitriangular subgroup, in the ambient adelic group. -/
def unipotentRationalImage (n : ℕ) : Subgroup (Points F n) :=
  ((unipotentAdelic F n).subtype.comp
    (AdelicSubgroupPoints.rational F (Scheme F n) (upperUnipotent F n))).range

theorem unipotentRationalImage_le (n : ℕ) :
    unipotentRationalImage F n ≤ AdelicGroupPoints.rationalSubgroup F (Scheme F n) := by
  rintro x ⟨q, rfl⟩
  exact ⟨q.val, rfl⟩

theorem isDiscrete_unipotentRationalImage (n : ℕ) :
    IsDiscrete (unipotentRationalImage F n : Set (Points F n)) :=
  (AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F n)).mono
    (unipotentRationalImage_le F n)

/-- The actual homogeneous space `N_n(𝔸) \ GL_n(𝔸)`. -/
abbrev WhittakerQuotient (n : ℕ) := LeftCosetSpace (unipotentAdelic F n)

instance whittakerQuotientBorelSpace (n : ℕ) : BorelSpace (WhittakerQuotient F n) :=
  LeftCosetSpace.quotient_borelSpace (unipotentAdelic F n)

instance whittakerRationalQuotientBorelSpace (n : ℕ) :
    BorelSpace (LeftCosetSpace (unipotentRationalImage F n)) :=
  LeftCosetSpace.discreteQuotientBorelSpace (unipotentRationalImage F n)
    (isDiscrete_unipotentRationalImage F n)

/-- Forget the rational unipotent class and retain the adelic unipotent class. -/
def toWhittakerQuotient (n : ℕ) :
    LeftCosetSpace (unipotentRationalImage F n) → WhittakerQuotient F n :=
  LeftCosetSpace.lift (unipotentRationalImage F n)
    (LeftCosetSpace.mk (unipotentAdelic F n)) fun γ x => by
      apply LeftCosetSpace.mk_subgroup_mul
        (unipotentAdelic F n) ⟨γ.val, ?_⟩ x
      obtain ⟨q, hq⟩ := γ.property
      rw [← hq]
      exact (AdelicSubgroupPoints.rational F (Scheme F n) (upperUnipotent F n) q).property

theorem continuous_toWhittakerQuotient (n : ℕ) :
    Continuous (toWhittakerQuotient F n) := by
  apply (LeftCosetSpace.continuous_iff (unipotentRationalImage F n)).mpr
  exact LeftCosetSpace.continuous_mk (unipotentAdelic F n)

theorem measurable_toWhittakerQuotient (n : ℕ) :
    Measurable (toWhittakerQuotient F n) :=
  (continuous_toWhittakerQuotient F n).measurable

/-- Quotient Haar with the unipotent rational quotient assigned mass one:
push ambient Haar/counting measure from `N_n(F) \ GL_n(𝔸)` to the adelic quotient. -/
def whittakerQuotientMeasure (n : ℕ) : Measure (WhittakerQuotient F n) :=
  Measure.map (toWhittakerQuotient F n)
    (LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F n)
      (isDiscrete_unipotentRationalImage F n))

local instance rectangleMeasurableSpace (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) :=
  borel _

local instance rectangleBorelSpace (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩

theorem measurable_rectangleCoordinates (k m : ℕ) :
    Measurable (fun x =>
      (GeneralLinearBlockUnipotent.adelicCoordinates F
        (show k + m = k + m from rfl) x).toAdd) := by
  have hc : Continuous (fun x =>
      (GeneralLinearBlockUnipotent.adelicCoordinates F
        (show k + m = k + m from rfl) x).toAdd) :=
    (GeneralLinearBlockUnipotent.adelicCoordinates F
      (show k + m = k + m from rfl)).continuous
  exact hc.measurable

/-- Rectangular additive Haar transported from the Library's covolume-one
two-block unipotent Haar normalization. -/
def rectangleMeasure (k m : ℕ) : Measure (Matrix (Fin k) (Fin m) (Adeles F)) :=
  Measure.map
    (fun x => (GeneralLinearBlockUnipotent.adelicCoordinates F
      (show k + m = k + m from rfl) x).toAdd)
    (GeneralLinearBlockUnipotent.normalizedBlockHaarMeasure F
      (show k + m = k + m from rfl))

/-- The block matrix `[[h,0,0],[x,I_(n-m-1),0],[0,0,1]]`. -/
def rectangularPoint {r t : ℕ} (h : t < r) (g : Points F (t + 1))
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F)) : Points F (r + 1) :=
  (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
    (GeneralLinear.reindex
      (finCongr (congrArg (fun a : ℕ => a + 1)
        (Nat.add_sub_of_le (Nat.succ_le_of_lt h))))
      (GeneralLinear.lowerBlockLocalization 1
        (GeneralLinearGroupPoints.adelicEquiv F (t + 1) g) x 1))

/-- The Weyl element `diag(I_m,w_(n-m))` on the actual adelic carrier. -/
def unfoldingWeyl {r t : ℕ} (h : t < r) : Points F (r + 1) :=
  (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
    (GeneralLinear.reindex
      (finCongr (Nat.add_sub_of_le (Nat.le_of_lt (Nat.succ_lt_succ h))))
      (GeneralLinear.blockSum
        (1, GeneralLinear.weylLong ((r + 1) - (t + 1)) (Adeles F))))

/-- Positive right translation of a function on actual adelic points. -/
def translateFunction (n : ℕ) (a : Points F n) (W : Points F n → ℂ) :
    Points F n → ℂ := fun g => W (g * a)

/-- The unequal-rank Whittaker integrand, using a quotient representative. -/
def unequalWhittakerIntegrand {r t : ℕ} (h : t < r)
    (W : Points F (r + 1) → ℂ) (W' : Points F (t + 1) → ℂ) (s : ℂ)
    (q : WhittakerQuotient F (t + 1)) : ℂ :=
  let g := q.out
  W (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) g) * W' g *
    detPower F (t + 1) g (s - ((r - t : ℕ) : ℂ) / 2)

/-- The raw global Whittaker integral `Ψ(s;W,W')`. -/
def unequalWhittakerIntegral {r t : ℕ} (h : t < r)
    (W : Points F (r + 1) → ℂ) (W' : Points F (t + 1) → ℂ) (s : ℂ) : ℂ :=
  ∫ q, unequalWhittakerIntegrand F h W W' s q
    ∂whittakerQuotientMeasure F (t + 1)

/-- The dual Whittaker integrand before the rectangular integration. -/
def dualWhittakerKernel {r t : ℕ} (h : t < r)
    (W : Points F (r + 1) → ℂ) (W' : Points F (t + 1) → ℂ) (s : ℂ)
    (q : WhittakerQuotient F (t + 1))
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F)) : ℂ :=
  let g := q.out
  W (rectangularPoint F h g x) * W' g *
    detPower F (t + 1) g (s - ((r - t : ℕ) : ℂ) / 2)

/-- The dual Whittaker integrand after the rectangular integration. -/
def dualWhittakerIntegrand {r t : ℕ} (h : t < r)
    (W : Points F (r + 1) → ℂ) (W' : Points F (t + 1) → ℂ) (s : ℂ)
    (q : WhittakerQuotient F (t + 1)) : ℂ :=
  ∫ x, dualWhittakerKernel F h W W' s q x
    ∂rectangleMeasure F (r - (t + 1)) (t + 1)

/-- The iterated defining integral `Ψ̃(s;W,W')`. The Weyl right translation,
when required for unfolding, is passed explicitly in the first function. -/
def dualWhittakerIntegral {r t : ℕ} (h : t < r)
    (W : Points F (r + 1) → ℂ) (W' : Points F (t + 1) → ℂ) (s : ℂ) : ℂ :=
  ∫ q, dualWhittakerIntegrand F h W W' s q
    ∂whittakerQuotientMeasure F (t + 1)

end Langlands.Global.RankinSelbergGlobal
