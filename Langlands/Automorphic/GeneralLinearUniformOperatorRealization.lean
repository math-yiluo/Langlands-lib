import Langlands.Automorphic.GeneralLinearAdelicUniformForms
import Langlands.Automorphic.FullOperatorRealization
import Langlands.Automorphic.OperatorCompactCompatibility

/-! # Uniform adelic forms of `GL_n` as an actual operator realization

The matrix-side uniform-growth bound is a subspace of the original finite-smooth carrier,
stable under the whole original operator algebra. Its automorphic part is an invariant
subspace of all original forms and hence an existing `OperatorRealization`. The actual
group-scheme uniform forms map onto exactly this subspace, so they are also closed under
the transported standard maximal compact. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance uniformRealizationGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance uniformRealizationGeneralLinearAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
  Module.addCommMonoidToAddCommGroup ℂ

local instance uniformRealizationMatrixRationalAddCommGroup :
    AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _

local instance uniformRealizationMatrixContinuousAddCommGroup :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _

local instance uniformRealizationMatrixAddCommGroup :
    AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _

local instance uniformRealizationFormsAddCommGroup :
    AddCommGroup (Langlands.Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _

variable {N : ℕ}
  (rho : GroupScheme.MatrixRepresentation
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) (Fin N))

/-- The matrix-side form of uniform growth: one exponent for all original enveloping
derivatives, bounded by the full adelic height of `rho` at the corresponding actual point. -/
def IsGeneralLinearUniformGrowth (f : Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :
    Prop :=
  ∃ e : ℕ, ∀ a : ArchimedeanGL.EnvelopingAlgebra F n, ∃ C : ℝ, 0 ≤ C ∧
    ∀ g : AdelicGL F n,
      ‖Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
        (Langlands.Automorphic.finiteSmoothInclusion F n
          (Langlands.Automorphic.finiteSmoothEnvelopingAction F n a f)) g‖ ≤
        C * RepresentationGrowth.adelicHeight F GLG rho
          ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm g) ^ e

variable {F n rho}

/-- Acting by another original enveloping element preserves the same shared exponent. -/
theorem IsGeneralLinearUniformGrowth.envelopingAction
    {f : Langlands.Automorphic.FiniteSmoothRationalFunctions F n}
    (hf : IsGeneralLinearUniformGrowth F n rho f) (b : ArchimedeanGL.EnvelopingAlgebra F n) :
    IsGeneralLinearUniformGrowth F n rho
      (Langlands.Automorphic.finiteSmoothEnvelopingAction F n b f) := by
  obtain ⟨e, hf⟩ := hf
  refine ⟨e, fun a => ?_⟩
  simpa only [map_mul, Module.End.mul_apply] using hf (a * b)

/-- Right translation by one adelic point multiplies a full-height bound by a constant. -/
theorem norm_evaluate_rightAction_le (hN : 0 < N)
    {h : Langlands.Automorphic.FiniteSmoothRationalFunctions F n} {C : ℝ} {e : ℕ}
    (hC : 0 ≤ C)
    (hh : ∀ g : AdelicGL F n,
      ‖Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
        (Langlands.Automorphic.finiteSmoothInclusion F n h) g‖ ≤
        C * RepresentationGrowth.adelicHeight F GLG rho
          ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm g) ^ e)
    (x : AdelicGL F n) (g : AdelicGL F n) :
    ‖Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
        (Langlands.Automorphic.finiteSmoothInclusion F n
          (Langlands.Automorphic.finiteSmoothRightAction F n x h)) g‖ ≤
      (C * RepresentationGrowth.adelicHeight F GLG rho
          ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm x) ^ e) *
        RepresentationGrowth.adelicHeight F GLG rho
          ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm g) ^ e := by
  have hn0 (y : AdelicGroupPoints F GLG) : 0 ≤ RepresentationGrowth.adelicHeight F GLG rho y :=
    zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F GLG rho hN y)
  calc
    _ ≤ C * RepresentationGrowth.adelicHeight F GLG rho
        ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm (g * x)) ^ e := hh (g * x)
    _ ≤ C * (RepresentationGrowth.adelicHeight F GLG rho
          ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm g) *
        RepresentationGrowth.adelicHeight F GLG rho
          ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm x)) ^ e := by
      rw [map_mul]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hn0 _) (RepresentationGrowth.adelicHeight_mul_le
          F GLG rho hN _ _) e) hC
    _ = _ := by rw [mul_pow]; ring

/-- Finite right translation preserves matrix-side uniform growth. -/
theorem IsGeneralLinearUniformGrowth.finiteRightAction (hN : 0 < N)
    {f : Langlands.Automorphic.FiniteSmoothRationalFunctions F n}
    (hf : IsGeneralLinearUniformGrowth F n rho f) (d : FiniteAdelicGL F n) :
    IsGeneralLinearUniformGrowth F n rho
      (Langlands.Automorphic.finiteSmoothFiniteRightAction F n d f) := by
  obtain ⟨e, hf⟩ := hf
  refine ⟨e, fun a => ?_⟩
  obtain ⟨C, hC, hb⟩ := hf a
  have hn0 (y : AdelicGroupPoints F GLG) : 0 ≤ RepresentationGrowth.adelicHeight F GLG rho y :=
    zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F GLG rho hN y)
  refine ⟨C * RepresentationGrowth.adelicHeight F GLG rho
      ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm (AdelicGL.ofFinite F n d)) ^ e,
    mul_nonneg hC (pow_nonneg (hn0 _) e), fun g => ?_⟩
  rw [← Langlands.Automorphic.finiteSmoothFiniteRightAction_envelopingAction]
  exact norm_evaluate_rightAction_le hN hC hb (AdelicGL.ofFinite F n d) g

/-- Right translation by an infinite adelic point preserves matrix-side uniform growth.
The derivative of the translate is the translate of a conjugated derivative. -/
theorem IsGeneralLinearUniformGrowth.infiniteRightAction (hN : 0 < N)
    {f : Langlands.Automorphic.FiniteSmoothRationalFunctions F n}
    (hf : IsGeneralLinearUniformGrowth F n rho f) (x : InfiniteAdelicGL F n) :
    IsGeneralLinearUniformGrowth F n rho
      (Langlands.Automorphic.finiteSmoothRightAction F n (AdelicGL.ofInfinite F n x) f) := by
  obtain ⟨e, hf⟩ := hf
  refine ⟨e, fun a => ?_⟩
  obtain ⟨C, hC, hb⟩ := hf ((ArchimedeanGL.envelopingConjugation F n x).symm a)
  have hn0 (y : AdelicGroupPoints F GLG) : 0 ≤ RepresentationGrowth.adelicHeight F GLG rho y :=
    zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F GLG rho hN y)
  refine ⟨C * RepresentationGrowth.adelicHeight F GLG rho
      ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm (AdelicGL.ofInfinite F n x)) ^ e,
    mul_nonneg hC (pow_nonneg (hn0 _) e), fun g => ?_⟩
  have hcov := Langlands.Automorphic.finiteSmoothRightAction_envelopingAction x
    ((ArchimedeanGL.envelopingConjugation F n x).symm a) f
  rw [AlgEquiv.apply_symm_apply] at hcov
  rw [← hcov]
  exact norm_evaluate_rightAction_le hN hC hb (AdelicGL.ofInfinite F n x) g

theorem IsGeneralLinearUniformGrowth.zero : IsGeneralLinearUniformGrowth F n rho 0 := by
  refine ⟨0, fun a => ⟨0, le_rfl, fun g => ?_⟩⟩
  have h0 : Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
      (Langlands.Automorphic.finiteSmoothInclusion F n
        (Langlands.Automorphic.finiteSmoothEnvelopingAction F n a 0)) g = 0 := by
    rw [map_zero]
    rfl
  rw [h0, norm_zero, zero_mul]

theorem IsGeneralLinearUniformGrowth.add (hN : 0 < N)
    {f h : Langlands.Automorphic.FiniteSmoothRationalFunctions F n}
    (hf : IsGeneralLinearUniformGrowth F n rho f) (hh : IsGeneralLinearUniformGrowth F n rho h) :
    IsGeneralLinearUniformGrowth F n rho (f + h) := by
  obtain ⟨e, hf⟩ := hf
  obtain ⟨e', hh⟩ := hh
  refine ⟨max e e', fun a => ?_⟩
  obtain ⟨C, hC, hfa⟩ := hf a
  obtain ⟨D, hD, hha⟩ := hh a
  refine ⟨C + D, add_nonneg hC hD, fun g => ?_⟩
  set H := RepresentationGrowth.adelicHeight F GLG rho
    ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm g) with hH
  have h1 : 1 ≤ H := RepresentationGrowth.one_le_adelicHeight F GLG rho hN _
  have hsplit : Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
      (Langlands.Automorphic.finiteSmoothInclusion F n
        (Langlands.Automorphic.finiteSmoothEnvelopingAction F n a (f + h))) g =
      Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
        (Langlands.Automorphic.finiteSmoothInclusion F n
          (Langlands.Automorphic.finiteSmoothEnvelopingAction F n a f)) g +
      Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
        (Langlands.Automorphic.finiteSmoothInclusion F n
          (Langlands.Automorphic.finiteSmoothEnvelopingAction F n a h)) g := by
    rw [map_add]
    rfl
  rw [hsplit]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ C * H ^ e + D * H ^ e' := add_le_add (hfa g) (hha g)
    _ ≤ C * H ^ max e e' + D * H ^ max e e' :=
      add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (le_max_left e e')) hC)
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (le_max_right e e')) hD)
    _ = (C + D) * H ^ max e e' := (add_mul _ _ _).symm

theorem IsGeneralLinearUniformGrowth.smul
    {f : Langlands.Automorphic.FiniteSmoothRationalFunctions F n}
    (hf : IsGeneralLinearUniformGrowth F n rho f) (z : ℂ) :
    IsGeneralLinearUniformGrowth F n rho (z • f) := by
  obtain ⟨e, hf⟩ := hf
  refine ⟨e, fun a => ?_⟩
  obtain ⟨C, hC, hfa⟩ := hf a
  refine ⟨‖z‖ * C, mul_nonneg (norm_nonneg z) hC, fun g => ?_⟩
  have hs : Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
      (Langlands.Automorphic.finiteSmoothInclusion F n
        (Langlands.Automorphic.finiteSmoothEnvelopingAction F n a (z • f))) g =
      z * Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
        (Langlands.Automorphic.finiteSmoothInclusion F n
          (Langlands.Automorphic.finiteSmoothEnvelopingAction F n a f)) g := by
    rw [map_smul]
    rfl
  rw [hs, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hfa g) (norm_nonneg z)

variable (F n rho)

/-- Matrix-side uniform growth as a subspace of the original finite-smooth carrier. -/
def generalLinearUniformGrowthSubmodule (hN : 0 < N) :
    Submodule ℂ (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) where
  carrier := {f | IsGeneralLinearUniformGrowth F n rho f}
  zero_mem' := IsGeneralLinearUniformGrowth.zero
  add_mem' := IsGeneralLinearUniformGrowth.add hN
  smul_mem' z _ hf := hf.smul z

@[simp]
theorem mem_generalLinearUniformGrowthSubmodule (hN : 0 < N)
    (f : Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :
    f ∈ generalLinearUniformGrowthSubmodule F n rho hN ↔
      IsGeneralLinearUniformGrowth F n rho f := Iff.rfl

/-- Every element of the original concrete operator algebra preserves uniform growth. -/
theorem generalLinearUniformGrowthSubmodule_operator_invariant (hN : 0 < N)
    (a : Langlands.Automorphic.automorphicOperatorAlgebra F n)
    (f : Langlands.Automorphic.FiniteSmoothRationalFunctions F n)
    (hf : f ∈ generalLinearUniformGrowthSubmodule F n rho hN) :
    a.val f ∈ generalLinearUniformGrowthSubmodule F n rho hN :=
  ((Langlands.Automorphic.operator_invariant_iff F n _).mpr
    ⟨fun d _ hf => IsGeneralLinearUniformGrowth.finiteRightAction hN hf d,
      fun k _ hf => IsGeneralLinearUniformGrowth.infiniteRightAction hN hf k.val,
      fun b _ hf => IsGeneralLinearUniformGrowth.envelopingAction hf b⟩) a f hf

/-- The uniform-growth forms are an invariant subspace of all original matrix forms. -/
def uniformGeneralLinearFormSubrepresentation (hN : 0 < N) :
    Subrepresentation (Langlands.Automorphic.fullAutomorphicAction F n) where
  toSubmodule := (generalLinearUniformGrowthSubmodule F n rho hN).comap
    (Langlands.Automorphic.automorphicSubrepresentation F n).toSubmodule.subtype
  apply_mem_toSubmodule a f hf :=
    generalLinearUniformGrowthSubmodule_operator_invariant F n rho hN a f.val hf

@[simp]
theorem mem_uniformGeneralLinearFormSubrepresentation (hN : 0 < N)
    (f : Langlands.Automorphic.AutomorphicForms F n) :
    f ∈ uniformGeneralLinearFormSubrepresentation F n rho hN ↔
      IsGeneralLinearUniformGrowth F n rho f.val := Iff.rfl

/-- The existing whole-operator realization whose all-form image is the uniform subspace. -/
def uniformGeneralLinearOperatorRealization (hN : 0 < N) :
    Langlands.Automorphic.OperatorRealization F n :=
  (Langlands.Automorphic.operatorRealizationFullFormOrderIso F n).symm
    (uniformGeneralLinearFormSubrepresentation F n rho hN)

@[simp]
theorem uniformGeneralLinearOperatorRealization_fullFormImage (hN : 0 < N) :
    (uniformGeneralLinearOperatorRealization F n rho hN).fullFormImage =
      uniformGeneralLinearFormSubrepresentation F n rho hN :=
  (Langlands.Automorphic.operatorRealizationFullFormOrderIso F n).apply_symm_apply _

variable {d : ℕ} (hsmooth : SmoothOfRelativeDimension d
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom)
  (hcalc : AdelicDifferentialCommutator F
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) hsmooth)
  (hrho : GroupScheme.IsClosedSubgroup rho) (hN : 0 < N)
  (hG : GroupScheme.IsConnectedReductive
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))

/-- The actual uniform forms for the transported standard maximal compact. -/
abbrev UniformGeneralLinearAdelicForms :
    Submodule ℂ (FinitePlotSmoothRationalFunctions F GLG) :=
  (uniformAdelicAutomorphicSubrepresentation F GLG (generalLinearStandardInfiniteCompact F n)
    rho hsmooth hcalc hG hrho (generalLinearStandardInfiniteCompact_isMaximalCompact F n)
    hN).toSubmodule

/-- An actual function is a uniform form exactly when its original matrix function is an
original form with matrix-side uniform growth. The ordinary full growth is then automatic. -/
theorem mem_uniformAdelicAutomorphic_iff_generalLinear
    (f : FinitePlotSmoothRationalFunctions F GLG) :
    f ∈ UniformGeneralLinearAdelicForms F n rho hsmooth hcalc hrho hN hG ↔
      finitePlotSmoothGeneralLinearEquiv F n f ∈
          (Langlands.Automorphic.automorphicSubrepresentation F n).toSubmodule ∧
        IsGeneralLinearUniformGrowth F n rho (finitePlotSmoothGeneralLinearEquiv F n f) := by
  have hU := hasAdelicUniformPolynomialGrowth_iff_generalLinear F n hsmooth hcalc rho f
  have hA := isAdelicAutomorphicForm_iff_generalLinear_and_adelicGrowth
    F n rho hsmooth hcalc hrho hN f
  have hM := mem_adelicAutomorphicSubrepresentation F GLG
    (generalLinearStandardInfiniteCompact F n) rho hsmooth hcalc hG hrho
    (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN f
  have hF := Langlands.Automorphic.mem_automorphicSubrepresentation F n
    (finitePlotSmoothGeneralLinearEquiv F n f)
  constructor
  · rintro ⟨hf, hu⟩
    exact ⟨hF.mpr (hA.mp (hM.mp hf)).1, hU.mp hu⟩
  · rintro ⟨hf, hu⟩
    have hu' := hU.mpr hu
    exact ⟨hM.mpr (hA.mpr ⟨hF.mp hf,
      (hasAdelicModerateGrowth_iff F GLG rho hN f.val).mpr hu'.polynomialGrowth⟩), hu'⟩

/-- The actual uniform forms map onto exactly the matrix-side uniform forms. -/
theorem range_uniformAdelicAutomorphicGeneralLinearMap :
    LinearMap.range (uniformAdelicAutomorphicGeneralLinearMap F n hsmooth hcalc rho hrho hN hG) =
      (uniformGeneralLinearFormSubrepresentation F n rho hN).toSubmodule := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact ((mem_uniformAdelicAutomorphic_iff_generalLinear F n rho hsmooth hcalc hrho hN hG
      g.val).mp g.property).2
  · intro hf
    have hmem : (finitePlotSmoothGeneralLinearEquiv F n).symm f.val ∈
        UniformGeneralLinearAdelicForms F n rho hsmooth hcalc hrho hN hG := by
      apply (mem_uniformAdelicAutomorphic_iff_generalLinear F n rho hsmooth hcalc hrho hN hG
        _).mpr
      rw [LinearEquiv.apply_symm_apply]
      exact ⟨f.property, hf⟩
    refine ⟨⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    exact (finitePlotSmoothGeneralLinearEquiv F n).apply_symm_apply f.val

/-- The actual uniform forms are linearly equivalent to the matrix-side uniform forms. -/
def uniformAdelicAutomorphicGeneralLinearEquiv :
    UniformGeneralLinearAdelicForms F n rho hsmooth hcalc hrho hN hG ≃ₗ[ℂ]
      (uniformGeneralLinearFormSubrepresentation F n rho hN).toSubmodule :=
  (LinearEquiv.ofInjective _
      (uniformAdelicAutomorphicGeneralLinearMap_injective F n hsmooth hcalc rho hrho hN hG)).trans
    (LinearEquiv.ofEq _ _
      (range_uniformAdelicAutomorphicGeneralLinearMap F n rho hsmooth hcalc hrho hN hG))

@[simp]
theorem uniformAdelicAutomorphicGeneralLinearEquiv_val
    (f : UniformGeneralLinearAdelicForms F n rho hsmooth hcalc hrho hN hG) :
    (uniformAdelicAutomorphicGeneralLinearEquiv F n rho hsmooth hcalc hrho hN hG f).val =
      uniformAdelicAutomorphicGeneralLinearMap F n hsmooth hcalc rho hrho hN hG f := rfl

/-- The equivalence carries the actual enveloping action to the original differential
operator of the corresponding original enveloping element. -/
theorem uniformAdelicAutomorphicGeneralLinearEquiv_envelopingAction
    (a : AdelicEnvelopingAlgebra F GLG hsmooth)
    (f : UniformGeneralLinearAdelicForms F n rho hsmooth hcalc hrho hN hG) :
    uniformAdelicAutomorphicGeneralLinearEquiv F n rho hsmooth hcalc hrho hN hG
        (uniformAdelicAutomorphicEnvelopingAction F GLG hsmooth hcalc
          (generalLinearStandardInfiniteCompact F n) rho hG hrho
          (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN a f) =
      (uniformGeneralLinearFormSubrepresentation F n rho hN).toRepresentation
        (Langlands.Automorphic.differentialOperator F n
          (GeneralLinearGroupPoints.infiniteEnvelopingEquiv F n hsmooth hcalc a))
        (uniformAdelicAutomorphicGeneralLinearEquiv F n rho hsmooth hcalc hrho hN hG f) :=
  Subtype.ext
    (uniformAdelicAutomorphicGeneralLinearMap_envelopingAction F n hsmooth hcalc rho hrho hN hG
      a f)

/-- The equivalence carries actual finite translation to the original finite operator. -/
theorem uniformAdelicAutomorphicGeneralLinearEquiv_finiteRightAction
    (c : FiniteAdelicGroupPoints F GLG)
    (f : UniformGeneralLinearAdelicForms F n rho hsmooth hcalc hrho hN hG) :
    uniformAdelicAutomorphicGeneralLinearEquiv F n rho hsmooth hcalc hrho hN hG
        ((uniformAdelicAutomorphicSubrepresentation F GLG
          (generalLinearStandardInfiniteCompact F n) rho hsmooth hcalc hG hrho
          (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN).toRepresentation c f) =
      (uniformGeneralLinearFormSubrepresentation F n rho hN).toRepresentation
        (Langlands.Automorphic.finiteOperator F n (GeneralLinearGroupPoints.finiteHomeomorph F n c))
        (uniformAdelicAutomorphicGeneralLinearEquiv F n rho hsmooth hcalc hrho hN hG f) :=
  Subtype.ext
    (uniformAdelicAutomorphicGeneralLinearMap_finiteRightAction F n hsmooth hcalc rho hrho hN hG
      c f)

/-- The actual uniform forms are linearly equivalent to the space of the operator realization. -/
def uniformAdelicAutomorphicRealizationEquiv :
    UniformGeneralLinearAdelicForms F n rho hsmooth hcalc hrho hN hG ≃ₗ[ℂ]
      (uniformGeneralLinearOperatorRealization F n rho hN).Space :=
  (uniformAdelicAutomorphicGeneralLinearEquiv F n rho hsmooth hcalc hrho hN hG).trans
    ((LinearEquiv.ofEq _ _ (congrArg Subrepresentation.toSubmodule
        (uniformGeneralLinearOperatorRealization_fullFormImage F n rho hN)).symm).trans
      (uniformGeneralLinearOperatorRealization F n rho hN).fullFormEquiv.symm.toLinearEquiv)

/-- The realization space holds the same underlying original matrix function. -/
@[simp]
theorem uniformAdelicAutomorphicRealizationEquiv_val
    (f : UniformGeneralLinearAdelicForms F n rho hsmooth hcalc hrho hN hG) :
    ((uniformAdelicAutomorphicRealizationEquiv F n rho hsmooth hcalc hrho hN hG f).val).val =
      finitePlotSmoothGeneralLinearEquiv F n f.val := rfl

/-- Original matrix right translation by an actual point of an infinite subgroup. -/
theorem finitePlotSmoothGeneralLinearEquiv_infiniteSubgroupAction
    (U : Subgroup (InfiniteAdelicGroupPoints F GLG)) (k : U)
    (f : FinitePlotSmoothRationalFunctions F GLG) :
    finitePlotSmoothGeneralLinearEquiv F n (finitePlotSmoothInfiniteSubgroupAction F GLG U k f) =
      Langlands.Automorphic.finiteSmoothRightAction F n
        (AdelicGL.ofInfinite F n (GeneralLinearGroupPoints.infiniteHomeomorph F n k.val))
        (finitePlotSmoothGeneralLinearEquiv F n f) := by
  apply Subtype.ext
  change continuousGeneralLinearEquiv F n
      (continuousRightAction F GLG (AdelicGroupPoints.ofInfinite F GLG k.val) f.val) = _
  rw [continuousGeneralLinearEquiv_rightAction,
    GeneralLinearGroupPoints.adelicHomeomorph_ofInfinite]
  rfl

/-- The actual uniform space is closed under the transported standard maximal compact. -/
theorem uniformAdelicAutomorphic_infiniteSubgroupAction_mem
    (k : generalLinearStandardInfiniteCompact F n) {f : FinitePlotSmoothRationalFunctions F GLG}
    (hf : f ∈ UniformGeneralLinearAdelicForms F n rho hsmooth hcalc hrho hN hG) :
    finitePlotSmoothInfiniteSubgroupAction F GLG (generalLinearStandardInfiniteCompact F n) k f ∈
      UniformGeneralLinearAdelicForms F n rho hsmooth hcalc hrho hN hG := by
  rw [mem_uniformAdelicAutomorphic_iff_generalLinear F n rho hsmooth hcalc hrho hN hG] at hf ⊢
  rw [finitePlotSmoothGeneralLinearEquiv_infiniteSubgroupAction]
  let k' : standardInfiniteCompact F n :=
    ⟨GeneralLinearGroupPoints.infiniteHomeomorph F n k.val, k.property⟩
  refine ⟨?_, IsGeneralLinearUniformGrowth.infiniteRightAction hN hf.2 k'.val⟩
  exact (Langlands.Automorphic.fullAutomorphicSubrepresentation F n).apply_mem_toSubmodule
    (Langlands.Automorphic.compactOperator F n k') hf.1

/-- The transported standard maximal compact acts on the actual uniform forms. -/
def uniformAdelicAutomorphicCompactSubrepresentation :
    Subrepresentation
      (finitePlotSmoothInfiniteSubgroupAction F GLG
        (generalLinearStandardInfiniteCompact F n)) where
  toSubmodule := UniformGeneralLinearAdelicForms F n rho hsmooth hcalc hrho hN hG
  apply_mem_toSubmodule k _ hf :=
    uniformAdelicAutomorphic_infiniteSubgroupAction_mem F n rho hsmooth hcalc hrho hN hG k hf

end Langlands.Automorphic.GroupSchemeFunctions
