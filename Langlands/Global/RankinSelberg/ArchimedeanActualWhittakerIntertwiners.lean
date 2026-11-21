import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerAnalyticProof
import Langlands.Global.RankinSelberg.CuspidalWhittakerIdentityNonzero
import Langlands.Global.RankinSelberg.RealPlaceWhittakerAnalyticProof

/-! # Normalized actual Whittaker intertwiners at the infinite places -/

noncomputable section

universe u

open NumberField
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.Global.RankinSelbergGlobal

open Automorphic HeckeFunctionalEquation LocalFactor.Archimedean

local notation "RP" F => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" F => {v : InfinitePlace F // InfinitePlace.IsComplex v}

/-- Each supplied standard parameter has a normalized Whittaker intertwiner formed
by restricting actual cuspidal Whittaker functions, for the given adelic character. -/
def ArchimedeanActualWhittakerIntertwinersStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T : CuspidalOperatorRealization F r),
    (∀ (v : RP F) (d : List RealBlock), T.realization.HasRealPlaceParameter v d →
      ∀ (a : ℝˣ), IsRealAdditiveComponent ψ v.1 v.2 a →
        ∃ (A : realStandardKFinite (r + 1) d →ₗ[ℂ] T.Space)
          (B : realStandardKFinite (r + 1) d →ₗ[ℂ] (GeneralLinear (r + 1) ℝ → ℂ)),
          T.realization.IsRealPlaceMap v d A ∧ IsRealWhittakerIntertwiner r d a B ∧
          (∃ f, B f 1 = 1) ∧
          ∀ f g, B f g = cuspWhittaker F T ψ.complex (A f) (realPlacePoint F (r + 1) v g)) ∧
    (∀ (w : CP F) (d : List ComplexCharacterData), T.realization.HasComplexPlaceParameter w d →
      ∀ (a : ℂˣ), IsComplexAdditiveComponent ψ w.1 w.2 a →
        ∃ (A : complexStandardKFinite (r + 1) d →ₗ[ℂ] T.Space)
          (B : complexStandardKFinite (r + 1) d →ₗ[ℂ] (GeneralLinear (r + 1) ℂ → ℂ)),
          T.realization.IsComplexPlaceMap w d A ∧ IsComplexWhittakerIntertwiner r d a B ∧
          (∃ f, B f 1 = 1) ∧
          ∀ f g, B f g = cuspWhittaker F T ψ.complex (A f) (complexPlacePoint F (r + 1) w g))

variable {F : Type u} [Field F] [NumberField F]

local instance actualIntertwinerAffine (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance actualIntertwinerSmooth (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance actualIntertwinerRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance actualIntertwinerContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance actualIntertwinerFiniteSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance actualIntertwinerAutomorphicGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance actualIntertwinerStableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance actualIntertwinerRealizationGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace ActualWhittakerIntertwiners

private theorem exists_normalized_map_value {I V E : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup E] [Module ℂ E]
    (A : I → V →ₗ[ℂ] E) (L : E →ₗ[ℂ] ℂ)
    (hA : (⨆ i, LinearMap.range (A i)) = ⊤) (hL : L ≠ 0) :
    ∃ i f, L (A i f) = 1 := by
  have h : ∃ i f, L (A i f) ≠ 0 := by
    by_contra! hzero
    have hker : ⊤ ≤ LinearMap.ker L := by
      rw [← hA]
      apply iSup_le
      rintro i _ ⟨f, rfl⟩
      exact LinearMap.mem_ker.mpr (hzero i f)
    apply hL
    apply LinearMap.ext
    intro x
    exact LinearMap.mem_ker.mp (hker (Submodule.mem_top (x := x)))
  obtain ⟨i, f, hf⟩ := h
  exact ⟨i, (L (A i f))⁻¹ • f, by simp only [map_smul, smul_eq_mul, inv_mul_cancel₀ hf]⟩

private theorem adelicPoint_one (n : ℕ) : adelicPoint F n 1 1 = 1 := by
  unfold adelicPoint
  rw [map_one]
  change (GeneralLinearGroupPoints.adelicEquiv F n).symm (AdelicGL.ofInfinite F n 1) = 1
  rw [map_one, map_one]

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} (T : CuspidalOperatorRealization F r)
  (χ : AddChar (Adeles F) ℂ) (hχ : IsStandardAdditiveCharacter F χ)

private def identityValue : T.Space →ₗ[ℂ] ℂ where
  toFun x := cuspWhittaker F T χ x 1
  map_add' x y := UnramifiedWhittaker.cuspWhittaker_add F χ hχ T x y 1
  map_smul' c x := UnramifiedWhittaker.cuspWhittaker_smul F χ T c x 1

private theorem identityValue_ne_zero : identityValue T χ hχ ≠ 0 := by
  obtain ⟨x, hx⟩ := cuspidalWhittakerIdentityNonzero F r T χ hχ
  exact fun h => hx (LinearMap.congr_fun h x)

end ActualWhittakerIntertwiners

open ActualWhittakerIntertwiners

theorem archimedeanActualWhittakerIntertwiners :
    ArchimedeanActualWhittakerIntertwinersStatement.{u} := by
  intro F _ _ _ ψ hψ r T
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  let L := identityValue T ψ.complex hstd
  have hL : L ≠ 0 := identityValue_ne_zero T ψ.complex hstd
  have hFin : finitePoint F (r + 1) 1 = 1 := adelicPoint_one (r + 1)
  constructor
  · intro v d hd a ha
    let Maps := {A : realStandardKFinite (r + 1) d →ₗ[ℂ] T.Space //
      T.realization.IsRealPlaceMap v d A}
    have htop : (⨆ A : Maps, LinearMap.range A.1) = ⊤ :=
      T.realization.realPlaceIsotypic_eq_top T.irreducible hd
    obtain ⟨A, f, hf⟩ := exists_normalized_map_value (E := T.Space) (fun A : Maps => A.1) L htop hL
    obtain ⟨B, hB, hBf⟩ :=
      (realPlaceWhittakerIntertwinerReduction realPlaceWhittakerAnalytic F ψ hψ r T v a ha
        d A.1 A.2 1).1
    have hval (f : realStandardKFinite (r + 1) d) (g : GeneralLinear (r + 1) ℝ) :
        B f g = cuspWhittaker F T ψ.complex (A.1 f) (realPlacePoint F (r + 1) v g) := by
      simpa only [hFin, mul_one] using congrFun (hBf f) g
    have hOne : realPlacePoint F (r + 1) v 1 = 1 := by
      rw [realPlacePoint, map_one, adelicPoint_one]
    refine ⟨A.1, B, A.2, hB, ⟨f, ?_⟩, hval⟩
    rw [hval f 1, hOne]
    exact hf
  · intro w d hd a ha
    let Maps := {A : complexStandardKFinite (r + 1) d →ₗ[ℂ] T.Space //
      T.realization.IsComplexPlaceMap w d A}
    have htop : (⨆ A : Maps, LinearMap.range A.1) = ⊤ :=
      T.realization.complexPlaceIsotypic_eq_top T.irreducible hd
    obtain ⟨A, f, hf⟩ := exists_normalized_map_value (E := T.Space) (fun A : Maps => A.1) L htop hL
    obtain ⟨B, hB, hBf⟩ :=
      (complexPlaceWhittakerIntertwinerReduction complexPlaceWhittakerAnalytic F ψ hψ r T w a ha
        d A.1 A.2 1).1
    have hval (f : complexStandardKFinite (r + 1) d) (g : GeneralLinear (r + 1) ℂ) :
        B f g = cuspWhittaker F T ψ.complex (A.1 f) (complexPlacePoint F (r + 1) w g) := by
      simpa only [hFin, mul_one] using congrFun (hBf f) g
    have hOne : complexPlacePoint F (r + 1) w 1 = 1 := by
      rw [complexPlacePoint, map_one, adelicPoint_one]
    refine ⟨A.1, B, A.2, hB, ⟨f, ?_⟩, hval⟩
    rw [hval f 1, hOne]
    exact hf

end Langlands.Global.RankinSelbergGlobal
