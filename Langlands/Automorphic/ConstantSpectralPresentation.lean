import Langlands.Automorphic.ConstantTensorPresentation
import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Representation.Hecke.DoubleCosetSandwich

/-! # Actual spherical spectra of the rank-one constant presentation -/

noncomputable section
open scoped Classical TensorProduct

universe uG uV uF uP

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Hecke

open MeasureTheory

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (μ : Measure G) [μ.IsHaarMeasure]
  (ρ : Representation ℂ G V) (hρ : Langlands.IsSmooth ρ)

/-- A normalized double coset from the normalizer acts by the actual group element. -/
theorem doubleCosetOperator_coe_of_mem_normalizer {g : G}
    (hg : g ∈ Subgroup.normalizer (K.toSubgroup : Set G))
    (v : Langlands.fixedVectors ρ K.toSubgroup) :
    (doubleCosetOperator K hK μ ρ hρ g v : V) = ρ g v := by
  have hfun :
      HeckeAlgebra.toTestFunction μ
        (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK
          (HeckeAlgebra.Corner.doubleCoset K hK μ g)) =
      TestFunction.leftTranslate g
        (HeckeAlgebra.toTestFunction μ
          (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK 1)) := by
    ext x
    exact HeckeAlgebra.Corner.doubleCoset_apply_of_mem_normalizer K hK μ hg x
  change integratedAction μ ρ hρ _ v = ρ g v
  rw [hfun, integratedAction_leftTranslate]
  change ρ g (heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK) v) = _
  rw [heckeAction_normalizedIndicator_of_fixed μ ρ hρ K hK v.property]

end Langlands.Hecke

namespace Langlands.Unramified

open Langlands.Correspondence

/-- The rank-one spectrum consisting of the scalar one. -/
def rankOneTrivialSpectrum : Eigenvalues 1 :=
  Eigenvalues.ofTuple (fun _ => 1)

@[simp]
theorem rankOneTrivialSpectrum_eulerPolynomial :
    Eigenvalues.eulerPolynomial rankOneTrivialSpectrum = 1 - Polynomial.X := by
  simp [rankOneTrivialSpectrum]

@[simp]
theorem rankOneTrivialSpectrum_powerTrace (k : ℕ) :
    Eigenvalues.powerTrace rankOneTrivialSpectrum k = 1 := by
  simp [rankOneTrivialSpectrum]

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

@[simp]
theorem standardHeckeScalar_rankOneTrivialSpectrum (i : Fin 2) :
    standardHeckeScalar F rankOneTrivialSpectrum i = 1 := by
  fin_cases i <;>
    simp [standardHeckeScalar, elementaryCoefficient, Polynomial.coeff_one]

attribute [local instance] heckeFieldTopology heckeGeneralLinearTopology
  heckeGeneralLinearTopologicalGroup heckeGeneralLinearMeasurable heckeGeneralLinearBorel
  heckeGeneralLinearT2

/-- The actual rank-one standard operators are identity for a trivial action. -/
theorem standardHeckeOperator_rankOne_of_trivial
    (A : AutomorphicObject.{uF, uV} F (0 : ℕ).succPNat)
    (hA : ∀ g v, A.obj.representation g v = v)
    (i : Fin 2) (v : fixedVectors A.obj.representation (sphericalSubgroup F 0)) :
    standardHeckeOperator F A i v = v := by
  have hc : standardDiagonal F 0 i ∈ Subgroup.center (GeneralLinear 1 F.Carrier) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Units.ext
    ext j k
    fin_cases j
    fin_cases k
    simp [standardDiagonal_val, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
  have hn := Subgroup.center_le_normalizer
    ((sphericalOpenSubgroup F 0).toSubgroup : Set (GeneralLinear 1 F.Carrier)) hc
  apply Subtype.ext
  exact (Hecke.doubleCosetOperator_coe_of_mem_normalizer
    (sphericalOpenSubgroup F 0) (sphericalOpenSubgroup_isCompact F 0)
    (sphericalHaar F 0) A.obj.representation A.obj.isSmooth hn v).trans (hA _ _)

/-- This spectrum satisfies all actual standard equations on the whole fixed space. -/
theorem hasSphericalHeckeSpectrum_rankOne_of_trivial
    (A : AutomorphicObject.{uF, uV} F (0 : ℕ).succPNat)
    (hfixed : fixedVectors A.obj.representation (sphericalSubgroup F 0) ≠ ⊥)
    (hA : ∀ g v, A.obj.representation g v = v) :
    HasSphericalHeckeSpectrum F A rankOneTrivialSpectrum := by
  refine ⟨hfixed, ?_⟩
  intro i v
  rw [standardHeckeScalar_rankOneTrivialSpectrum, one_smul]
  exact standardHeckeOperator_rankOne_of_trivial F A hA i v

end Langlands.Unramified

namespace Langlands.Automorphic.ConstantFunctions

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.Unramified

variable (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance : AddCommGroup (RationalInvariantFunctions F 1) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F 1) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F 1) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F 1) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F 1) := Submodule.addCommGroup _
local instance {v : FinitePlace F} (S : LocalRealization F 1 v) :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- Actual unramified data for the constructed rank-one constant tensor. -/
def rankOneUnramifiedData :
    (finiteTensorPresentation.{uF, uP} F 1).UnramifiedData
      (rankOneCuspidal F).finiteRealization_ne_bot ∅ where
  exceptional_subset := le_rfl
  irreducible v _ := tensorLocalModel_isIrreducible F 1 v
  admissible v _ := tensorLocalModel_isAdmissible F 1 v
  eigenvalues _ _ := rankOneTrivialSpectrum
  hasSpectrum v _ := by
    let P := finiteTensorPresentation.{uF, uP} F 1
    let hS : (realization F 1).toFiniteRealization.IsNonzero F 1 :=
      (rankOneCuspidal F).finiteRealization_ne_bot
    let A := P.localPadicObject hS v
      (tensorLocalModel_isIrreducible F 1 v) (tensorLocalModel_isAdmissible F 1 v)
    change HasSphericalHeckeSpectrum (CompletionPadic.padicField v) A rankOneTrivialSpectrum
    apply hasSphericalHeckeSpectrum_rankOne_of_trivial
    · obtain ⟨f, hf, hfix⟩ := P.localComponent_exists_integral_fixed hS v
        (by simp)
      change ∀ g ∈ (localIntegral F 1 v).toSubgroup,
        (P.localComponent hS v).representation g f = f at hfix
      rw [localIntegral_eq_sphericalSubgroup F v 0] at hfix
      exact (Submodule.ne_bot_iff _).mpr ⟨f, fun g => hfix g.val g.property, hf⟩
    · intro g f
      obtain ⟨x, rfl⟩ := (P.localComponentEquiv hS v).surjective f
      exact (LinearMap.congr_fun ((P.localComponentEquiv hS v).isIntertwining' g) x).symm

/-- A genuine spectral presentation of the actual constant rank-one cusp line. -/
def rankOneSpectralPresentation :
    CuspidalSpectralPresentation.{uF, uP} (rankOneCuspidal F) where
  finiteSlice := CuspidalOperatorRealization.FiniteSlice.whole (rankOneCuspidal F)
  localFactor v := Langlands.SmoothRep.of (tensorLocalModel F 1 v)
    (tensorLocalModel_isSmooth F 1 v)
  tensorExceptional := ∅
  reference _ := ULift.up 1
  reference_fixed := tensorReference_fixed F 1
  presentation := finiteTensorPresentation F 1
  exceptional := ∅
  unramified := rankOneUnramifiedData F

@[simp]
theorem rankOneSpectralPresentation_eigenvalues
    (v : FinitePlace F)
    (hv : v ∉ (rankOneSpectralPresentation.{uF, uP} F).exceptional) :
    (rankOneSpectralPresentation.{uF, uP} F).spectralSystem.eigenvalues v hv =
      rankOneTrivialSpectrum := rfl

end Langlands.Automorphic.ConstantFunctions
