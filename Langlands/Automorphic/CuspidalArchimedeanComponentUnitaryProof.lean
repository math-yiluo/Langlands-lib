import Langlands.Automorphic.CuspidalArchimedeanComponentStatement
import Langlands.Automorphic.CuspidalUnitaryForm

/-!
# Unitarizable archimedean standard-module components

A proof of `Langlands.Automorphic.CuspidalArchimedeanStandardUnitarizableStatement`. If an
actual cuspidal realization `T` of `GL_{r+1}` has a unitary central character, it carries a
unitary form `b` (`CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter`).
The compact and Lie actions at an infinite place `v` are restrictions of the global ones, so
`b` is invariant under the compact action at `v` and skew under every real direction at `v`.
Pulling `b` back along the injective map of a place parameter gives the unitary form on the
standard module. See the paired Markdown.
-/

noncomputable section

universe u

open scoped TensorProduct Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

local instance componentUnitaryRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance componentUnitaryContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance componentUnitarySmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance componentUnitaryFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance componentUnitaryStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n)

local instance componentUnitarySpaceAddCommGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace UnitaryForm

variable {S}

/-- The form of a unitary form, as an invariant form of the compact action at a real
place. -/
def realPlaceCompactForm (b : S.UnitaryForm) (v : RP) :
    Langlands.InvariantPositiveForm (S.realPlaceCompactRepresentation v) where
  toInnerProductCore := b.finiteForm.toInnerProductCore
  invariant k f g := b.compact_invariant (realPlaceCompactInclusion F n v k) f g

/-- The form of a unitary form, as an invariant form of the compact action at a complex
place. -/
def complexPlaceCompactForm (b : S.UnitaryForm) (v : CP) :
    Langlands.InvariantPositiveForm (S.complexPlaceCompactRepresentation v) where
  toInnerProductCore := b.finiteForm.toInnerProductCore
  invariant k f g := b.compact_invariant (complexPlaceCompactInclusion F n v k) f g

@[simp] theorem realPlaceCompactForm_inner (b : S.UnitaryForm) (v : RP) (f g : S.Space) :
    (b.realPlaceCompactForm v).inner f g = b.inner f g := rfl

@[simp] theorem complexPlaceCompactForm_inner (b : S.UnitaryForm) (v : CP)
    (f g : S.Space) : (b.complexPlaceCompactForm v).inner f g = b.inner f g := rfl

/-- A unitary form is skew under every real direction at a real place. -/
theorem realPlace_skew (b : S.UnitaryForm) (v : RP) (X : Matrix (Fin n) (Fin n) ℝ)
    (f g : S.Space) :
    b.inner (S.realPlaceLieAction v (1 ⊗ₜ X) f) g +
      b.inner f (S.realPlaceLieAction v (1 ⊗ₜ X) g) = 0 :=
  b.real_skew (realPlaceLieInclusion F n v X) f g

/-- A unitary form is skew under every real direction at a complex place. -/
theorem complexPlace_skew (b : S.UnitaryForm) (v : CP) (X : Matrix (Fin n) (Fin n) ℂ)
    (f g : S.Space) :
    b.inner (S.complexPlaceLieAction v (1 ⊗ₜ X) f) g +
      b.inner f (S.complexPlaceLieAction v (1 ⊗ₜ X) g) = 0 :=
  b.real_skew (complexPlaceLieInclusion F n v X) f g

end UnitaryForm

variable {S}

/-- The compact clause of a real place parameter, for elements of `Matrix.unitaryGroup`. -/
theorem realPlaceParameter_compact {v : RP} {ds : List RealBlock}
    {A : realStandardKFinite n ds →ₗ[ℂ] S.Space}
    (hK : ∀ (k : Archimedean.unitaryCompact ℝ n) (f : realStandardKFinite n ds),
      ∃ hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
            realStandardKFinite n ds,
        A ⟨_, hf⟩ = S.realPlaceCompactRepresentation v
          ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ (A f))
    (k : Matrix.unitaryGroup (Fin n) ℝ) (f : realStandardKFinite n ds) :
    A (Archimedean.realStandardRep n ds k f) = S.realPlaceCompactRepresentation v k (A f) := by
  have hk : Unitary.toUnits k ∈ Archimedean.unitaryCompact ℝ n := k.2
  have e1 : Archimedean.realStandardRep n ds k f = ⟨_, (hK ⟨_, hk⟩ f).1⟩ := by
    apply Subtype.ext
    rw [Archimedean.realStandardRep_apply_coe]
  have e2 : (⟨(((⟨Unitary.toUnits k, hk⟩ : Archimedean.unitaryCompact ℝ n) :
      Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), hk⟩ :
        Matrix.unitaryGroup (Fin n) ℝ) = k := Subtype.ext rfl
  have h := (hK ⟨_, hk⟩ f).2
  rw [e2] at h
  exact (congrArg A e1).trans h

/-- The compact clause of a complex place parameter, for elements of `Matrix.unitaryGroup`. -/
theorem complexPlaceParameter_compact {v : CP} {ds : List ComplexCharacterData}
    {A : complexStandardKFinite n ds →ₗ[ℂ] S.Space}
    (hK : ∀ (k : Archimedean.unitaryCompact ℂ n) (f : complexStandardKFinite n ds),
      ∃ hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
          (k : Langlands.GeneralLinear n ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ) ∈
            complexStandardKFinite n ds,
        A ⟨_, hf⟩ = S.complexPlaceCompactRepresentation v
          ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ (A f))
    (k : Matrix.unitaryGroup (Fin n) ℂ) (f : complexStandardKFinite n ds) :
    A (Archimedean.complexStandardRep n ds k f) =
      S.complexPlaceCompactRepresentation v k (A f) := by
  have hk : Unitary.toUnits k ∈ Archimedean.unitaryCompact ℂ n := k.2
  have e1 : Archimedean.complexStandardRep n ds k f = ⟨_, (hK ⟨_, hk⟩ f).1⟩ := by
    apply Subtype.ext
    rw [Archimedean.principalSeriesRep_apply_coe]
  have e2 : (⟨(((⟨Unitary.toUnits k, hk⟩ : Archimedean.unitaryCompact ℂ n) :
      Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), hk⟩ :
        Matrix.unitaryGroup (Fin n) ℂ) = k := Subtype.ext rfl
  have h := (hK ⟨_, hk⟩ f).2
  rw [e2] at h
  exact (congrArg A e1).trans h

/-- The Lie clause of a real place parameter, for the standard Lie action. -/
theorem realPlaceParameter_lie {v : RP} {ds : List RealBlock}
    {A : realStandardKFinite n ds →ₗ[ℂ] S.Space}
    (hL : ∀ (X : Matrix (Fin n) (Fin n) ℝ) (f : realStandardKFinite n ds),
      ∃ hf : Archimedean.rightDerivative (Archimedean.matrixModel ℝ n) X
          (f : Langlands.GeneralLinear n ℝ → ℂ) ∈ realStandardKFinite n ds,
        A ⟨_, hf⟩ = S.realPlaceLieAction v (1 ⊗ₜ X) (A f))
    (X : Matrix (Fin n) (Fin n) ℝ) (f : realStandardKFinite n ds) :
    A (Archimedean.realStandardLie n ds (1 ⊗ₜ X) f) =
      S.realPlaceLieAction v (1 ⊗ₜ X) (A f) := by
  have e1 : Archimedean.realStandardLie n ds (1 ⊗ₜ X) f = ⟨_, (hL X f).1⟩ :=
    Subtype.ext (Archimedean.realStandardLie_one_tmul_apply_coe n ds X f)
  exact (congrArg A e1).trans (hL X f).2

/-- The Lie clause of a complex place parameter, for the standard Lie action. -/
theorem complexPlaceParameter_lie {v : CP} {ds : List ComplexCharacterData}
    {A : complexStandardKFinite n ds →ₗ[ℂ] S.Space}
    (hL : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (f : complexStandardKFinite n ds),
      ∃ hf : Archimedean.rightDerivative (Archimedean.matrixModel ℂ n) X
          (f : Langlands.GeneralLinear n ℂ → ℂ) ∈ complexStandardKFinite n ds,
        A ⟨_, hf⟩ = S.complexPlaceLieAction v (1 ⊗ₜ X) (A f))
    (X : Matrix (Fin n) (Fin n) ℂ) (f : complexStandardKFinite n ds) :
    A (Archimedean.complexStandardLie n ds (1 ⊗ₜ X) f) =
      S.complexPlaceLieAction v (1 ⊗ₜ X) (A f) := by
  have e1 : Archimedean.complexStandardLie n ds (1 ⊗ₜ X) f = ⟨_, (hL X f).1⟩ :=
    Subtype.ext (Archimedean.principalSeriesLie_one_tmul_apply_coe _ _ _ X f)
  exact (congrArg A e1).trans (hL X f).2

/-- A unitary form of a realization makes the standard module of every real place parameter
unitarizable. -/
theorem UnitaryForm.isRealUnitarizable_of_hasRealPlaceParameter (b : S.UnitaryForm)
    {v : RP} {ds : List RealBlock} (h : S.HasRealPlaceParameter v ds) :
    Archimedean.IsRealUnitarizableGKModule n (Archimedean.realStandardRep n ds)
      (Archimedean.realStandardLie n ds) := by
  obtain ⟨-, A, hA, hK, hL⟩ := h
  let B : (Archimedean.realStandardRep n ds).IntertwiningMap
      (S.realPlaceCompactRepresentation v) :=
    LinearMap.intertwiningMap_of_isIntertwiningMap _ _ A (realPlaceParameter_compact hK)
  refine ⟨(b.realPlaceCompactForm v).comap B hA, fun X f g => ?_⟩
  exact (congrArg₂ (fun x y => b.inner x (A g) + b.inner (A f) y)
    (realPlaceParameter_lie hL X f) (realPlaceParameter_lie hL X g)).trans
      (b.realPlace_skew v X (A f) (A g))

/-- A unitary form of a realization makes the standard module of every complex place
parameter unitarizable. -/
theorem UnitaryForm.isComplexUnitarizable_of_hasComplexPlaceParameter (b : S.UnitaryForm)
    {v : CP} {ds : List ComplexCharacterData} (h : S.HasComplexPlaceParameter v ds) :
    Archimedean.IsComplexUnitarizableGKModule n (Archimedean.complexStandardRep n ds)
      (Archimedean.complexStandardLie n ds) := by
  obtain ⟨-, A, hA, hK, hL⟩ := h
  let B : (Archimedean.complexStandardRep n ds).IntertwiningMap
      (S.complexPlaceCompactRepresentation v) :=
    LinearMap.intertwiningMap_of_isIntertwiningMap _ _ A (complexPlaceParameter_compact hK)
  refine ⟨(b.complexPlaceCompactForm v).comap B hA, fun X f g => ?_⟩
  exact (congrArg₂ (fun x y => b.inner x (A g) + b.inner (A f) y)
    (complexPlaceParameter_lie hL X f) (complexPlaceParameter_lie hL X g)).trans
      (b.complexPlace_skew v X (A f) (A g))

end OperatorRealization

/-- **Unitarizable archimedean components** (the unitarity of the archimedean factors `V_v` of
Getz–Hahn 2024, §11.4, p. 301, before display (11.15)). The unitary form of a cuspidal
realization with unitary central character, pulled back along the injective map of a place
parameter, is a unitary form of the standard module. -/
theorem cuspidalArchimedeanStandardUnitarizable :
    CuspidalArchimedeanStandardUnitarizableStatement.{u} := by
  intro F _ _ _ r T hT
  obtain ⟨b⟩ := T.isUnitarizable_of_hasUnitaryCentralCharacter hT
  exact ⟨fun _ _ h => b.isRealUnitarizable_of_hasRealPlaceParameter h,
    fun _ _ h => b.isComplexUnitarizable_of_hasComplexPlaceParameter h⟩

end Langlands.Automorphic
