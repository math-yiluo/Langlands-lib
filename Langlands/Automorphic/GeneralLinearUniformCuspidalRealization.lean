import Langlands.Automorphic.GeneralLinearUniformOperatorRealization
import Langlands.Automorphic.GeneralLinearParabolicCuspidalEquivalence
import Langlands.Automorphic.GroupSchemeCuspidalForms
import Langlands.Automorphic.CuspidalOperatorRealization

/-! # Cuspidal operator realizations of `GL_n` in the actual uniform cusp forms

A realization inside the uniform realization maps injectively into the actual uniform forms,
intertwining finite translation and the enveloping action. The largest cuspidal realization
inside the uniform realization is constructed, and cuspidal realizations land in the actual
uniform cusp forms. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance uniformCuspidalGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance uniformCuspidalGeneralLinearSmooth : Smooth (GLG).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

local instance uniformCuspidalPlotAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
  Module.addCommMonoidToAddCommGroup ℂ

local instance uniformCuspidalRationalAddCommGroup :
    AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _

local instance uniformCuspidalContinuousAddCommGroup :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _

local instance uniformCuspidalFiniteSmoothAddCommGroup :
    AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _

local instance uniformCuspidalFormsAddCommGroup :
    AddCommGroup (Langlands.Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _

local instance uniformCuspidalStableAddCommGroup :
    AddCommGroup (Langlands.Automorphic.StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

variable {N : ℕ}
  (rho : GroupScheme.MatrixRepresentation
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) (Fin N))
  (hN : 0 < N)

/-- Membership in the uniform realization is matrix-side uniform growth of the same function. -/
theorem mem_uniformGeneralLinearOperatorRealization_iff
    (f : Langlands.Automorphic.StableAutomorphicFunctions F n) :
    f ∈ uniformGeneralLinearOperatorRealization F n rho hN ↔
      IsGeneralLinearUniformGrowth F n rho f.val := by
  have h := (uniformGeneralLinearOperatorRealization F n rho hN).mem_fullFormImage_iff
    (Langlands.Automorphic.stableAutomorphicEquiv F n f)
  rw [ContinuousLinearEquiv.symm_apply_apply,
    uniformGeneralLinearOperatorRealization_fullFormImage] at h
  exact h.symm

/-- The continuous function of a realized vector is its underlying function. -/
theorem operatorRealization_toContinuous_eq
    (S : Langlands.Automorphic.OperatorRealization F n) (f : S.Space) :
    S.toContinuous f = f.val.val.val := rfl

variable {d : ℕ} (hsmooth : SmoothOfRelativeDimension d
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom)
  (hcalc : AdelicDifferentialCommutator F
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) hsmooth)
  (hrho : GroupScheme.IsClosedSubgroup rho)
  (hG : GroupScheme.IsConnectedReductive
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))

variable {F n rho hN}

/-- A realization inside the uniform realization maps into the actual uniform forms by the
inverse function equivalence. -/
def uniformRealizationAdelicFormMap (S : Langlands.Automorphic.OperatorRealization F n)
    (hS : S ≤ uniformGeneralLinearOperatorRealization F n rho hN) :
    S.Space →ₗ[ℂ] UniformGeneralLinearAdelicForms F n rho hsmooth hcalc hrho hN hG where
  toFun f := ⟨(finitePlotSmoothGeneralLinearEquiv F n).symm f.val.val, by
    apply (mem_uniformAdelicAutomorphic_iff_generalLinear F n rho hsmooth hcalc hrho hN hG
      _).mpr
    rw [LinearEquiv.apply_symm_apply]
    exact ⟨(Langlands.Automorphic.stableAutomorphicEquiv F n f.val).property,
      (mem_uniformGeneralLinearOperatorRealization_iff F n rho hN f.val).mp (hS f.property)⟩⟩
  map_add' f g := Subtype.ext (map_add (finitePlotSmoothGeneralLinearEquiv F n).symm
    f.val.val g.val.val)
  map_smul' c f := Subtype.ext (map_smul (finitePlotSmoothGeneralLinearEquiv F n).symm
    c f.val.val)

/-- The matrix function of the image is the realized vector's function. -/
@[simp]
theorem finitePlotSmoothGeneralLinearEquiv_uniformRealizationAdelicFormMap
    (S : Langlands.Automorphic.OperatorRealization F n)
    (hS : S ≤ uniformGeneralLinearOperatorRealization F n rho hN) (f : S.Space) :
    finitePlotSmoothGeneralLinearEquiv F n
        (uniformRealizationAdelicFormMap hsmooth hcalc hrho hG S hS f).val = f.val.val :=
  (finitePlotSmoothGeneralLinearEquiv F n).apply_symm_apply _

/-- The published uniform-form injection returns the realized form. -/
theorem uniformAdelicAutomorphicGeneralLinearMap_uniformRealizationAdelicFormMap
    (S : Langlands.Automorphic.OperatorRealization F n)
    (hS : S ≤ uniformGeneralLinearOperatorRealization F n rho hN) (f : S.Space) :
    uniformAdelicAutomorphicGeneralLinearMap F n hsmooth hcalc rho hrho hN hG
        (uniformRealizationAdelicFormMap hsmooth hcalc hrho hG S hS f) = S.formInclusion f :=
  Subtype.ext
    (finitePlotSmoothGeneralLinearEquiv_uniformRealizationAdelicFormMap hsmooth hcalc hrho hG
      S hS f)

theorem uniformRealizationAdelicFormMap_injective
    (S : Langlands.Automorphic.OperatorRealization F n)
    (hS : S ≤ uniformGeneralLinearOperatorRealization F n rho hN) :
    Function.Injective (uniformRealizationAdelicFormMap hsmooth hcalc hrho hG S hS) := by
  intro f g h
  apply S.formInclusion_injective
  rw [← uniformAdelicAutomorphicGeneralLinearMap_uniformRealizationAdelicFormMap hsmooth hcalc
      hrho hG S hS f,
    ← uniformAdelicAutomorphicGeneralLinearMap_uniformRealizationAdelicFormMap hsmooth hcalc
      hrho hG S hS g, h]

/-- The map carries the realization's finite operator to actual finite translation. -/
theorem uniformRealizationAdelicFormMap_finiteRightAction
    (S : Langlands.Automorphic.OperatorRealization F n)
    (hS : S ≤ uniformGeneralLinearOperatorRealization F n rho hN)
    (c : FiniteAdelicGroupPoints F GLG) (f : S.Space) :
    uniformRealizationAdelicFormMap hsmooth hcalc hrho hG S hS
        (S.finiteRepresentation (GeneralLinearGroupPoints.finiteHomeomorph F n c) f) =
      (uniformAdelicAutomorphicSubrepresentation F GLG
          (generalLinearStandardInfiniteCompact F n) rho hsmooth hcalc hG hrho
          (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN).toRepresentation c
        (uniformRealizationAdelicFormMap hsmooth hcalc hrho hG S hS f) := by
  apply uniformAdelicAutomorphicGeneralLinearMap_injective F n hsmooth hcalc rho hrho hN hG
  have h1 := uniformAdelicAutomorphicGeneralLinearMap_uniformRealizationAdelicFormMap
    hsmooth hcalc hrho hG S hS
    (S.finiteRepresentation (GeneralLinearGroupPoints.finiteHomeomorph F n c) f)
  have h2 := uniformAdelicAutomorphicGeneralLinearMap_finiteRightAction F n hsmooth hcalc rho
    hrho hN hG c (uniformRealizationAdelicFormMap hsmooth hcalc hrho hG S hS f)
  have h3 := uniformAdelicAutomorphicGeneralLinearMap_uniformRealizationAdelicFormMap
    hsmooth hcalc hrho hG S hS f
  have h4 : S.formInclusion
        (S.finiteRepresentation (GeneralLinearGroupPoints.finiteHomeomorph F n c) f) =
      Langlands.Automorphic.automorphicFiniteRightAction F n
        (GeneralLinearGroupPoints.finiteHomeomorph F n c) (S.formInclusion f) := rfl
  exact h1.trans (h4.trans ((congrArg (Langlands.Automorphic.automorphicFiniteRightAction F n
    (GeneralLinearGroupPoints.finiteHomeomorph F n c)) h3.symm).trans h2.symm))

/-- The map carries the realization's differential operator of the corresponding original
enveloping element to the actual enveloping action. -/
theorem uniformRealizationAdelicFormMap_envelopingAction
    (S : Langlands.Automorphic.OperatorRealization F n)
    (hS : S ≤ uniformGeneralLinearOperatorRealization F n rho hN)
    (a : AdelicEnvelopingAlgebra F GLG hsmooth) (f : S.Space) :
    uniformRealizationAdelicFormMap hsmooth hcalc hrho hG S hS
        (S.envelopingAction (GeneralLinearGroupPoints.infiniteEnvelopingEquiv F n hsmooth hcalc a)
          f) =
      uniformAdelicAutomorphicEnvelopingAction F GLG hsmooth hcalc
        (generalLinearStandardInfiniteCompact F n) rho hG hrho
        (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN a
        (uniformRealizationAdelicFormMap hsmooth hcalc hrho hG S hS f) := by
  apply uniformAdelicAutomorphicGeneralLinearMap_injective F n hsmooth hcalc rho hrho hN hG
  have h1 := uniformAdelicAutomorphicGeneralLinearMap_uniformRealizationAdelicFormMap
    hsmooth hcalc hrho hG S hS
    (S.envelopingAction (GeneralLinearGroupPoints.infiniteEnvelopingEquiv F n hsmooth hcalc a) f)
  have h2 := uniformAdelicAutomorphicGeneralLinearMap_envelopingAction F n hsmooth hcalc rho
    hrho hN hG a (uniformRealizationAdelicFormMap hsmooth hcalc hrho hG S hS f)
  have h3 := uniformAdelicAutomorphicGeneralLinearMap_uniformRealizationAdelicFormMap
    hsmooth hcalc hrho hG S hS f
  have h4 : S.formInclusion
        (S.envelopingAction (GeneralLinearGroupPoints.infiniteEnvelopingEquiv F n hsmooth hcalc a)
          f) =
      Langlands.Automorphic.automorphicEnvelopingAction F n
        (GeneralLinearGroupPoints.infiniteEnvelopingEquiv F n hsmooth hcalc a)
        (S.formInclusion f) := rfl
  exact h1.trans (h4.trans ((congrArg (Langlands.Automorphic.automorphicEnvelopingAction F n
    (GeneralLinearGroupPoints.infiniteEnvelopingEquiv F n hsmooth hcalc a)) h3.symm).trans
      h2.symm))

variable (F n rho hN)

variable [CompactSpace (AdeleQuotient F)]
  (hPD : GroupScheme.ParabolicDynamicStatement.{u})


/-- The largest realization in the uniform realization whose operator translates are all
cuspidal: every operator translate has uniform growth and vanishing constant terms. -/
def uniformCuspidalGeneralLinearOperatorRealization :
    Langlands.Automorphic.OperatorRealization F n where
  toSubmodule :=
    { carrier := {f | ∀ a : Langlands.Automorphic.automorphicOperatorAlgebra F n,
        IsGeneralLinearUniformGrowth F n rho (a.val f.val) ∧
          Langlands.Automorphic.IsCuspidal F n (a.val f.val).val}
      zero_mem' := fun a => by
        refine ⟨?_, ?_⟩
        · simpa only [ZeroMemClass.coe_zero, map_zero] using
            (IsGeneralLinearUniformGrowth.zero (F := F) (n := n) (rho := rho))
        · have h : Langlands.Automorphic.IsCuspidal F n 0 :=
            Submodule.zero_mem
              (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)).toSubmodule
          simpa only [ZeroMemClass.coe_zero, map_zero] using h
      add_mem' := fun {f g} hf hg a => by
        refine ⟨?_, ?_⟩
        · simpa only [Submodule.coe_add, map_add] using (hf a).1.add hN (hg a).1
        · have h : Langlands.Automorphic.IsCuspidal F n
              ((a.val f.val).val + (a.val g.val).val) :=
            Submodule.add_mem
              (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)).toSubmodule
              (hf a).2 (hg a).2
          simpa only [Submodule.coe_add, map_add] using h
      smul_mem' := fun c f hf a => by
        refine ⟨?_, ?_⟩
        · simpa only [Submodule.coe_smul, map_smul] using (hf a).1.smul c
        · have h : Langlands.Automorphic.IsCuspidal F n (c • (a.val f.val).val) :=
            Submodule.smul_mem
              (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)).toSubmodule
              c (hf a).2
          simpa only [Submodule.coe_smul, map_smul] using h }
  apply_mem_toSubmodule b _f hf a := hf (a * b)

theorem mem_uniformCuspidalGeneralLinearOperatorRealization_iff
    (f : Langlands.Automorphic.StableAutomorphicFunctions F n) :
    f ∈ uniformCuspidalGeneralLinearOperatorRealization F n rho hN ↔
      ∀ a : Langlands.Automorphic.automorphicOperatorAlgebra F n,
        IsGeneralLinearUniformGrowth F n rho (a.val f.val) ∧
          Langlands.Automorphic.IsCuspidal F n (a.val f.val).val := Iff.rfl

theorem uniformCuspidalGeneralLinearOperatorRealization_le :
    uniformCuspidalGeneralLinearOperatorRealization F n rho hN ≤
      uniformGeneralLinearOperatorRealization F n rho hN := fun f hf =>
  (mem_uniformGeneralLinearOperatorRealization_iff F n rho hN f).mpr (hf 1).1

theorem uniformCuspidalGeneralLinearOperatorRealization_isCuspidal :
    (uniformCuspidalGeneralLinearOperatorRealization F n rho hN).IsCuspidal :=
  (uniformCuspidalGeneralLinearOperatorRealization F n rho hN).isCuspidal_iff.mpr
    fun f => (f.property 1).2

/-- A realization lies in the uniform cuspidal one exactly when it lies in the uniform
realization and is cuspidal. -/
theorem le_uniformCuspidalGeneralLinearOperatorRealization_iff
    (S : Langlands.Automorphic.OperatorRealization F n) :
    S ≤ uniformCuspidalGeneralLinearOperatorRealization F n rho hN ↔
      S ≤ uniformGeneralLinearOperatorRealization F n rho hN ∧ S.IsCuspidal := by
  constructor
  · intro h
    exact ⟨h.trans (uniformCuspidalGeneralLinearOperatorRealization_le F n rho hN),
      S.isCuspidal_iff.mpr fun f => (h f.property 1).2⟩
  · rintro ⟨hu, hc⟩ f hf a
    have haf : Langlands.Automorphic.stableAutomorphicAction F n a f ∈ S :=
      S.apply_mem_toSubmodule a hf
    have h1 : IsGeneralLinearUniformGrowth F n rho
        (Langlands.Automorphic.stableAutomorphicAction F n a f).val :=
      (mem_uniformGeneralLinearOperatorRealization_iff F n rho hN _).mp (hu haf)
    have h2 := S.isCuspidal_iff.mp hc ⟨_, haf⟩
    rw [operatorRealization_toContinuous_eq] at h2
    exact ⟨h1, h2⟩

/-- An irreducible cuspidal realization of positive rank lies in the uniform cuspidal
realization exactly when it lies in the uniform realization. -/
theorem CuspidalOperatorRealization.realization_le_uniformCuspidal_iff {r : ℕ}
    (S : Langlands.Automorphic.CuspidalOperatorRealization F r)
    (rho : GroupScheme.MatrixRepresentation
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) (Fin N)) :
    S.realization ≤ uniformCuspidalGeneralLinearOperatorRealization F (r + 1) rho hN ↔
      S.realization ≤ uniformGeneralLinearOperatorRealization F (r + 1) rho hN := by
  rw [le_uniformCuspidalGeneralLinearOperatorRealization_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, S.cuspidal⟩⟩

/-- The actual uniform cusp forms for the transported standard maximal compact. -/
abbrev UniformGeneralLinearAdelicCuspidalForms :
    Submodule ℂ (FinitePlotSmoothRationalFunctions F GLG) :=
  (uniformAdelicCuspidalSubrepresentation F GLG (generalLinearStandardInfiniteCompact F n)
    rho hsmooth hcalc hPD hG hrho (generalLinearStandardInfiniteCompact_isMaximalCompact F n)
    hN).toSubmodule

/-- An actual uniform form is a uniform cusp form exactly when its original matrix function
is cuspidal. -/
theorem mem_uniformAdelicCuspidal_iff_generalLinear
    (f : FinitePlotSmoothRationalFunctions F GLG) :
    f ∈ UniformGeneralLinearAdelicCuspidalForms F n rho hN hsmooth hcalc hrho hG hPD ↔
      f ∈ UniformGeneralLinearAdelicForms F n rho hsmooth hcalc hrho hN hG ∧
        Langlands.Automorphic.IsCuspidal F n (continuousGeneralLinearEquiv F n f.val) := by
  have hc := mem_normalizedGeneralLinearParabolicCuspidal_iff F n hPD hG f.val
  constructor
  · rintro ⟨⟨ha, hp⟩, hu⟩
    exact ⟨⟨ha, hu⟩, hc.mp hp⟩
  · rintro ⟨⟨ha, hu⟩, hp⟩
    exact ⟨⟨ha, hc.mpr hp⟩, hu⟩

variable {F n rho hN}

/-- A cuspidal realization inside the uniform realization maps into the actual uniform cusp
forms. -/
def uniformRealizationAdelicCuspidalFormMap (S : Langlands.Automorphic.OperatorRealization F n)
    (hS : S ≤ uniformGeneralLinearOperatorRealization F n rho hN) (hc : S.IsCuspidal) :
    S.Space →ₗ[ℂ] UniformGeneralLinearAdelicCuspidalForms F n rho hN hsmooth hcalc hrho hG hPD :=
  LinearMap.codRestrict _
    ((UniformGeneralLinearAdelicForms F n rho hsmooth hcalc hrho hN hG).subtype.comp
      (uniformRealizationAdelicFormMap hsmooth hcalc hrho hG S hS))
    (fun f => (mem_uniformAdelicCuspidal_iff_generalLinear F n rho hN hsmooth hcalc hrho hG hPD
      (uniformRealizationAdelicFormMap hsmooth hcalc hrho hG S hS f).val).mpr
      ⟨(uniformRealizationAdelicFormMap hsmooth hcalc hrho hG S hS f).property, by
        have h := S.isCuspidal_iff.mp hc f
        rw [operatorRealization_toContinuous_eq] at h
        have he := congrArg Subtype.val
          (finitePlotSmoothGeneralLinearEquiv_uniformRealizationAdelicFormMap hsmooth hcalc hrho
            hG S hS f)
        change continuousGeneralLinearEquiv F n _ = _ at he
        rw [he]
        exact h⟩)

@[simp]
theorem uniformRealizationAdelicCuspidalFormMap_val
    (S : Langlands.Automorphic.OperatorRealization F n)
    (hS : S ≤ uniformGeneralLinearOperatorRealization F n rho hN) (hc : S.IsCuspidal)
    (f : S.Space) :
    (uniformRealizationAdelicCuspidalFormMap hsmooth hcalc hrho hG hPD S hS hc f).val =
      (uniformRealizationAdelicFormMap hsmooth hcalc hrho hG S hS f).val := rfl

theorem uniformRealizationAdelicCuspidalFormMap_injective
    (S : Langlands.Automorphic.OperatorRealization F n)
    (hS : S ≤ uniformGeneralLinearOperatorRealization F n rho hN) (hc : S.IsCuspidal) :
    Function.Injective
      (uniformRealizationAdelicCuspidalFormMap hsmooth hcalc hrho hG hPD S hS hc) :=
  fun f g h => by
    have h' := congrArg Subtype.val h
    exact uniformRealizationAdelicFormMap_injective hsmooth hcalc hrho hG S hS (Subtype.ext h')

/-- An irreducible cuspidal realization of positive rank inside the uniform realization gives
a nonzero actual uniform cusp form. -/
theorem CuspidalOperatorRealization.uniformAdelicCuspidalForms_ne_bot {r : ℕ}
    {rho : GroupScheme.MatrixRepresentation
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) (Fin N)}
    {hN : 0 < N}
    (hsmooth : SmoothOfRelativeDimension d
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)).X.hom)
    (hcalc : AdelicDifferentialCommutator F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) hsmooth)
    (hrho : GroupScheme.IsClosedSubgroup rho)
    (hG : GroupScheme.IsConnectedReductive
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))
    (S : Langlands.Automorphic.CuspidalOperatorRealization F r)
    (hS : S.realization ≤ uniformGeneralLinearOperatorRealization F (r + 1) rho hN) :
    UniformGeneralLinearAdelicCuspidalForms F (r + 1) rho hN hsmooth hcalc hrho hG hPD ≠ ⊥ := by
  obtain ⟨f, hf⟩ := exists_ne (0 : S.Space)
  intro hbot
  have hm := (Submodule.eq_bot_iff _).mp hbot _
    (uniformRealizationAdelicCuspidalFormMap hsmooth hcalc hrho hG hPD S.realization hS
      S.cuspidal f).property
  apply hf
  apply uniformRealizationAdelicCuspidalFormMap_injective hsmooth hcalc hrho hG hPD
    S.realization hS S.cuspidal
  rw [map_zero]
  exact Subtype.ext hm

end Langlands.Automorphic.GroupSchemeFunctions
