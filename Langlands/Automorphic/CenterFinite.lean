import Langlands.Automorphic.Smooth
import Langlands.Global.ArchimedeanEnvelopingAction
import Langlands.Representation.FiniteVectors
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Simultaneous center finiteness of all adelic infinite slices -/

noncomputable section

universe u

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- A family indexed by every finite adelic argument, with actual smooth slices. -/
abbrev SmoothSliceFamily :=
  FiniteAdelicGL K n → ArchimedeanGL.SmoothFunctions K n

/-- Apply the actual center differential operator to every slice at once. -/
def centerFamilyAction :
    ArchimedeanGL.EnvelopingCenter K n →ₐ[ℂ] Module.End ℂ (SmoothSliceFamily K n) where
  toFun z := LinearMap.pi fun b =>
    (ArchimedeanGL.centerAction K n z).comp (LinearMap.proj b)
  map_zero' := by ext F b; simp
  map_one' := by ext F b; simp
  map_add' z w := by ext F b; simp
  map_mul' z w := by ext F b; simp [Module.End.mul_apply]
  commutes' c := by ext F b; simp

@[simp]
theorem centerFamilyAction_apply (z : ArchimedeanGL.EnvelopingCenter K n)
    (F : SmoothSliceFamily K n) (b : FiniteAdelicGL K n) :
    centerFamilyAction K n z F b = ArchimedeanGL.centerAction K n z (F b) := rfl

def centerFamilyRepresentation :
    Representation ℂ (ArchimedeanGL.EnvelopingCenter K n) (SmoothSliceFamily K n) :=
  (centerFamilyAction K n).toMonoidHom

/-- One linear map records the orbit of the entire family, without separate slice bounds. -/
def centerFamilyOrbitMap (F : SmoothSliceFamily K n) :
    ArchimedeanGL.EnvelopingCenter K n →ₗ[ℂ] SmoothSliceFamily K n where
  toFun z := centerFamilyAction K n z F
  map_add' z w := by simp
  map_smul' c z := by simp

def centerFamilyOrbitSpan (F : SmoothSliceFamily K n) :
    Submodule ℂ (SmoothSliceFamily K n) :=
  FiniteVectors.orbitSpan (centerFamilyRepresentation K n) F

theorem centerFamilyOrbitSpan_eq_range (F : SmoothSliceFamily K n) :
    centerFamilyOrbitSpan K n F = LinearMap.range (centerFamilyOrbitMap K n F) := by
  change Submodule.span ℂ (Set.range (centerFamilyOrbitMap K n F)) = _
  exact Submodule.span_eq (LinearMap.range (centerFamilyOrbitMap K n F))

/-- A common finite-dimensional center orbit for the full family of slices. -/
def IsCenterFiniteFamily (F : SmoothSliceFamily K n) : Prop :=
  Module.Finite ℂ (centerFamilyOrbitSpan K n F)

/-- The single ideal that annihilates every slice in the family. -/
def centerFamilyAnnihilator (F : SmoothSliceFamily K n) :
    Ideal (ArchimedeanGL.EnvelopingCenter K n) where
  carrier := {z | centerFamilyAction K n z F = 0}
  zero_mem' := by simp
  add_mem' hz hw := by simp_all
  smul_mem' a z hz := by
    change centerFamilyAction K n (a * z) F = 0
    rw [map_mul, Module.End.mul_apply, hz, map_zero]

@[simp]
theorem mem_centerFamilyAnnihilator (F : SmoothSliceFamily K n)
    (z : ArchimedeanGL.EnvelopingCenter K n) :
    z ∈ centerFamilyAnnihilator K n F ↔
      ∀ b, ArchimedeanGL.centerAction K n z (F b) = 0 := by
  change (fun b => ArchimedeanGL.centerAction K n z (F b)) = 0 ↔ _
  exact funext_iff

theorem centerFamilyAnnihilator_restrictScalars (F : SmoothSliceFamily K n) :
    (centerFamilyAnnihilator K n F).restrictScalars ℂ =
      LinearMap.ker (centerFamilyOrbitMap K n F) := rfl

/-- Finite orbit is exactly finite complex codimension of the common annihilator. -/
theorem isCenterFiniteFamily_iff_finite_quotient (F : SmoothSliceFamily K n) :
    IsCenterFiniteFamily K n F ↔
      Module.Finite ℂ (ArchimedeanGL.EnvelopingCenter K n ⧸
        (centerFamilyAnnihilator K n F).restrictScalars ℂ) := by
  change Module.Finite ℂ (centerFamilyOrbitSpan K n F) ↔ _
  rw [centerFamilyOrbitSpan_eq_range, centerFamilyAnnihilator_restrictScalars]
  exact (Module.Finite.equiv_iff (centerFamilyOrbitMap K n F).quotKerEquivRange).symm

/-- The source's existential formulation uses one ideal for all finite arguments. -/
theorem isCenterFiniteFamily_iff_exists_ideal (F : SmoothSliceFamily K n) :
    IsCenterFiniteFamily K n F ↔
      ∃ I : Ideal (ArchimedeanGL.EnvelopingCenter K n),
        Module.Finite ℂ (ArchimedeanGL.EnvelopingCenter K n ⧸ I.restrictScalars ℂ) ∧
        ∀ z ∈ I, ∀ b, ArchimedeanGL.centerAction K n z (F b) = 0 := by
  constructor
  · intro h
    exact ⟨centerFamilyAnnihilator K n F,
      (isCenterFiniteFamily_iff_finite_quotient K n F).mp h,
      fun z hz => (mem_centerFamilyAnnihilator K n F z).mp hz⟩
  · rintro ⟨I, hI, h⟩
    apply (isCenterFiniteFamily_iff_finite_quotient K n F).mpr
    let := hI
    have hle : I.restrictScalars ℂ ≤
        (centerFamilyAnnihilator K n F).restrictScalars ℂ := by
      intro z hz
      exact (mem_centerFamilyAnnihilator K n F z).mpr (h z hz)
    exact Module.Finite.of_surjective (Submodule.factor hle)
      (Submodule.factor_surjective hle)

/-- The actual smooth infinite slice, bundled with its smoothness proof. -/
def smoothInfiniteSlice (b : FiniteAdelicGL K n) :
    SmoothRationalFunctions K n →ₗ[ℂ] ArchimedeanGL.SmoothFunctions K n where
  toFun f := ⟨infiniteSlice K n b f.val, by
    have hf := f.property.1
    change f.val ∈ (⨅ b : FiniteAdelicGL K n,
      (ArchimedeanGL.smoothFunctions K n).comap (infiniteSlice K n b)) at hf
    exact (Submodule.mem_iInf _).mp hf b⟩
  map_add' f h := Subtype.ext rfl
  map_smul' c f := Subtype.ext rfl

/-- View one adelic function as its entire family of infinite slices. -/
def smoothSliceFamily : SmoothRationalFunctions K n →ₗ[ℂ] SmoothSliceFamily K n :=
  LinearMap.pi (smoothInfiniteSlice K n)

@[simp]
theorem smoothSliceFamily_apply (f : SmoothRationalFunctions K n)
    (b : FiniteAdelicGL K n) (a : InfiniteAdelicGL K n) :
    (smoothSliceFamily K n f b).val a =
      evaluate K n f.val (AdelicGL.pair K n a b) := rfl

theorem smoothSliceFamily_injective : Function.Injective (smoothSliceFamily K n) := by
  intro f h heq
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hx := congrArg (fun F : SmoothSliceFamily K n =>
    (F (AdelicGL.finite K n x)).val (AdelicGL.infinite K n x)) heq
  change evaluate K n f.val x = evaluate K n h.val x
  simpa only [smoothSliceFamily_apply, AdelicGL.pair_projections] using hx

/-- Simultaneous center finiteness is pulled back along the actual slice family. -/
def IsCenterFinite (f : SmoothRationalFunctions K n) : Prop :=
  IsCenterFiniteFamily K n (smoothSliceFamily K n f)

theorem isCenterFinite_iff_exists_ideal (f : SmoothRationalFunctions K n) :
    IsCenterFinite K n f ↔
      ∃ I : Ideal (ArchimedeanGL.EnvelopingCenter K n),
        Module.Finite ℂ (ArchimedeanGL.EnvelopingCenter K n ⧸ I.restrictScalars ℂ) ∧
        ∀ z ∈ I, ∀ b,
          ArchimedeanGL.centerAction K n z (smoothInfiniteSlice K n b f) = 0 :=
  isCenterFiniteFamily_iff_exists_ideal K n (smoothSliceFamily K n f)

def centerFiniteSmoothFunctions : Submodule ℂ (SmoothRationalFunctions K n) :=
  (FiniteVectors.subrepresentation (centerFamilyRepresentation K n)).toSubmodule.comap
    (smoothSliceFamily K n)

@[simp]
theorem mem_centerFiniteSmoothFunctions (f : SmoothRationalFunctions K n) :
    f ∈ centerFiniteSmoothFunctions K n ↔ IsCenterFinite K n f := Iff.rfl

/-- Finite adelic translation reindexes the complete family. -/
def finiteTranslateFamily (d : FiniteAdelicGL K n) :
    (centerFamilyRepresentation K n).IntertwiningMap (centerFamilyRepresentation K n) where
  toLinearMap :=
    { toFun F b := F (b * d)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

theorem smoothSliceFamily_finiteRightAction (d : FiniteAdelicGL K n)
    (f : SmoothRationalFunctions K n) :
    smoothSliceFamily K n (smoothRightAction K n (AdelicGL.ofFinite K n d) f) =
      finiteTranslateFamily K n d (smoothSliceFamily K n f) := by
  funext b
  apply Subtype.ext
  funext a
  change evaluate K n f.val (AdelicGL.pair K n a b * AdelicGL.ofFinite K n d) =
    evaluate K n f.val (AdelicGL.pair K n a (b * d))
  rw [AdelicGL.ofFinite_eq_pair, AdelicGL.pair_mul, mul_one]

theorem isCenterFinite_finiteRightAction (d : FiniteAdelicGL K n)
    {f : SmoothRationalFunctions K n} (hf : IsCenterFinite K n f) :
    IsCenterFinite K n (smoothRightAction K n (AdelicGL.ofFinite K n d) f) := by
  change FiniteVectors.IsFiniteVector (centerFamilyRepresentation K n)
    (smoothSliceFamily K n (smoothRightAction K n (AdelicGL.ofFinite K n d) f))
  rw [smoothSliceFamily_finiteRightAction]
  exact FiniteVectors.IsFiniteVector.map (finiteTranslateFamily K n d) hf

/-- The actual finite adelic action preserves the simultaneous center-finite subspace. -/
def centerFiniteSmoothSubrepresentation :
    Subrepresentation ((smoothRightAction K n).comp (AdelicGL.ofFinite K n).toMonoidHom) where
  toSubmodule := centerFiniteSmoothFunctions K n
  apply_mem_toSubmodule d _ hf := isCenterFinite_finiteRightAction K n d hf

/-- Actual smooth rational-invariant adelic functions with a common finite center orbit. -/
abbrev CenterFiniteSmoothRationalFunctions := centerFiniteSmoothFunctions K n

def centerFiniteSmoothFiniteRightAction :
    Representation ℂ (FiniteAdelicGL K n) (CenterFiniteSmoothRationalFunctions K n) :=
  (centerFiniteSmoothSubrepresentation K n).toRepresentation

/-- Equivariant inclusion into the smooth ambient space with its finite adelic action. -/
def centerFiniteSmoothInclusion :
    (centerFiniteSmoothFiniteRightAction K n).IntertwiningMap
      ((smoothRightAction K n).comp (AdelicGL.ofFinite K n).toMonoidHom) where
  toLinearMap := (centerFiniteSmoothFunctions K n).subtype
  isIntertwining' _ := by ext; rfl

theorem centerFiniteSmoothInclusion_injective :
    Function.Injective (centerFiniteSmoothInclusion K n) := Subtype.val_injective

@[simp]
theorem evaluate_centerFiniteSmoothFiniteRightAction (d : FiniteAdelicGL K n)
    (x : AdelicGL K n) (f : CenterFiniteSmoothRationalFunctions K n) :
    evaluate K n (centerFiniteSmoothFiniteRightAction K n d f).val.val x =
      evaluate K n f.val.val (x * AdelicGL.ofFinite K n d) := rfl

end Langlands.Automorphic
