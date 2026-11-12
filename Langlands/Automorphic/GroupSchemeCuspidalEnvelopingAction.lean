import Langlands.Automorphic.GroupSchemeConstantTermEnvelopingStatement
import Langlands.Automorphic.GroupSchemeInfiniteTranslation
import Langlands.Automorphic.GeneralLinearUniformCuspidalRealization
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # The enveloping action on cusp forms, given constant-term preservation

Given `AdelicConstantTermEnvelopingStatement`, the actual uniform cusp forms carry the actual
enveloping action, compatible with the infinite subgroup by the adjoint covariance. For `GL_n`,
the original cuspidal forms are an invariant subspace of all forms, hence an existing
`OperatorRealization`, and the uniform cuspidal realization is the uniform cuspidal part. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme

section General

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (hCT : AdelicConstantTermEnvelopingStatement.{u})

local instance cuspidalEnvelopingAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

include hCT in
/-- Every actual enveloping derivative preserves the published parabolic cusp condition. -/
theorem normalizedParabolicCuspidal_actualEnvelopingAction
    (a : AdelicEnvelopingAlgebra F G hsmooth) {f : FinitePlotSmoothRationalFunctions F G}
    (hf : f.val ∈ normalizedParabolicCuspidalSubrepresentation F G hPD hG) :
    (actualAdelicEnvelopingAction F G hsmooth a f).val ∈
      normalizedParabolicCuspidalSubrepresentation F G hPD hG := by
  rw [mem_normalizedParabolicCuspidalSubrepresentation_iff] at hf ⊢
  intro P g
  exact hCT F G hsmooth hPD hG P a f (hf P) g

variable (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
  {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hrho : IsClosedSubgroup rho)
  (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf) (hN : 0 < N)

include hCT in
/-- Every actual enveloping derivative of a uniform cusp form is a uniform cusp form. -/
theorem actualAdelicEnvelopingAction_mem_uniformAdelicCuspidal
    (a : AdelicEnvelopingAlgebra F G hsmooth) (f : FinitePlotSmoothRationalFunctions F G)
    (hf : f ∈ uniformAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK
      hN) :
    actualAdelicEnvelopingAction F G hsmooth a f ∈
      uniformAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK hN := by
  obtain ⟨⟨hA, hC⟩, hU⟩ := hf
  obtain ⟨hA', hU'⟩ := actualAdelicEnvelopingAction_mem_uniformAutomorphic F G hsmooth hcalc
    Kinf rho hG hrho hK hN a f ⟨hA, hU⟩
  exact ⟨⟨hA', normalizedParabolicCuspidal_actualEnvelopingAction F G hsmooth hPD hG hCT a hC⟩,
    hU'⟩

/-- The actual enveloping action restricted to the uniform cusp forms. -/
def uniformAdelicCuspidalEnvelopingAction :
    AdelicEnvelopingAlgebra F G hsmooth →ₐ[ℂ]
      Module.End ℂ (uniformAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho
        hK hN).toSubmodule where
  toFun a :=
    { toFun := fun f => ⟨actualAdelicEnvelopingAction F G hsmooth a f.val,
        actualAdelicEnvelopingAction_mem_uniformAdelicCuspidal F G hsmooth hcalc hPD hG hCT Kinf
          rho hrho hK hN a f.val f.property⟩
      map_add' f g := Subtype.ext (map_add _ _ _)
      map_smul' z f := Subtype.ext (map_smul _ _ _) }
  map_zero' := by ext f; simp only [map_zero, LinearMap.zero_apply]; rfl
  map_one' := by ext f; simp only [map_one, Module.End.one_apply]; rfl
  map_add' := by intros; ext f; simp only [map_add, LinearMap.add_apply]; rfl
  map_mul' := by intros; ext f; simp only [map_mul, Module.End.mul_apply]; rfl
  commutes' := by intro z; ext f; simp only [AlgHom.commutes, Module.algebraMap_end_apply]; rfl

@[simp]
theorem uniformAdelicCuspidalEnvelopingAction_val (a : AdelicEnvelopingAlgebra F G hsmooth)
    (f : (uniformAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK
      hN).toSubmodule) :
    (uniformAdelicCuspidalEnvelopingAction F G hsmooth hcalc hPD hG hCT Kinf rho hrho hK hN a
      f).val = actualAdelicEnvelopingAction F G hsmooth a f.val := rfl

/-- On uniform cusp forms, the infinite subgroup and the enveloping action satisfy the adjoint
covariance `R(k) D_a = D_(Ad(k) a) R(k)`. -/
theorem uniformAdelicCuspidalInfiniteSubrepresentation_envelopingAction (k : Kinf)
    (a : AdelicEnvelopingAlgebra F G hsmooth)
    (f : (uniformAdelicCuspidalSubrepresentation F G Kinf rho hsmooth hcalc hPD hG hrho hK
      hN).toSubmodule) :
    (uniformAdelicCuspidalInfiniteSubrepresentation F G hsmooth hcalc rho Kinf hG hrho hK hN
        hPD).toRepresentation k
        (uniformAdelicCuspidalEnvelopingAction F G hsmooth hcalc hPD hG hCT Kinf rho hrho hK hN a
          f) =
      uniformAdelicCuspidalEnvelopingAction F G hsmooth hcalc hPD hG hCT Kinf rho hrho hK hN
        (adelicEnvelopingConjugation F G hsmooth k.val a)
        ((uniformAdelicCuspidalInfiniteSubrepresentation F G hsmooth hcalc rho Kinf hG hrho hK hN
          hPD).toRepresentation k f) :=
  Subtype.ext (finitePlotSmoothRightAction_actualAdelicEnvelopingAction F G hsmooth k.val a f.val)

end General

section GeneralLinear

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance cuspidalEnvelopingGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance cuspidalEnvelopingGeneralLinearSmooth : Smooth (GLG).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

local instance cuspidalEnvelopingPlotAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
  Module.addCommMonoidToAddCommGroup ℂ

local instance cuspidalEnvelopingRationalAddCommGroup :
    AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _

local instance cuspidalEnvelopingContinuousAddCommGroup :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _

local instance cuspidalEnvelopingFiniteSmoothAddCommGroup :
    AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _

local instance cuspidalEnvelopingFormsAddCommGroup :
    AddCommGroup (Langlands.Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _

local instance cuspidalEnvelopingStableAddCommGroup :
    AddCommGroup (Langlands.Automorphic.StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

variable [CompactSpace (AdeleQuotient F)] (hCT : AdelicConstantTermEnvelopingStatement.{u})

include hCT in
/-- Every original enveloping derivative of a cuspidal original `GL_n` function is cuspidal.
All group-scheme hypotheses are discharged by published `GL_n` results. -/
theorem generalLinearCuspidal_envelopingAction (b : ArchimedeanGL.EnvelopingAlgebra F n)
    {f : Langlands.Automorphic.FiniteSmoothRationalFunctions F n}
    (hf : Langlands.Automorphic.IsCuspidal F n f.val) :
    Langlands.Automorphic.IsCuspidal F n
      (Langlands.Automorphic.finiteSmoothEnvelopingAction F n b f).val := by
  have hG := isConnectedReductive_generalLinear F (Fin n)
  have hsmooth := hG.smoothDimension_spec
  have hcalc := adelicDifferentialCommutator_of_smooth F GLG hsmooth
  have hPD : ParabolicDynamicStatement.{u} := parabolicDynamic
  obtain ⟨a, rfl⟩ :=
    (GeneralLinearGroupPoints.infiniteEnvelopingEquiv F n hsmooth hcalc).surjective b
  obtain ⟨g, rfl⟩ := (finitePlotSmoothGeneralLinearEquiv F n).surjective f
  have hg : g.val ∈ normalizedParabolicCuspidalSubrepresentation F GLG hPD hG :=
    (mem_normalizedGeneralLinearParabolicCuspidal_iff F n hPD hG g.val).mpr hf
  have h1 := normalizedParabolicCuspidal_actualEnvelopingAction F GLG hsmooth hPD hG hCT a hg
  have h2 := (mem_normalizedGeneralLinearParabolicCuspidal_iff F n hPD hG _).mp h1
  rw [← finitePlotSmoothGeneralLinearEquiv_actualEnvelopingAction F n hsmooth hcalc a g]
  exact h2

/-- Cuspidal functions as a subspace of the original finite-smooth carrier. -/
def generalLinearCuspidalFiniteSmoothSubmodule :
    Submodule ℂ (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)).toSubmodule.comap
    (Langlands.Automorphic.finiteSmoothRationalSubrepresentation F n).toSubmodule.subtype

include hCT in
/-- The whole concrete operator algebra preserves cuspidality. -/
theorem generalLinearCuspidalFiniteSmoothSubmodule_operator_invariant
    (a : Langlands.Automorphic.automorphicOperatorAlgebra F n)
    (f : Langlands.Automorphic.FiniteSmoothRationalFunctions F n)
    (hf : f ∈ generalLinearCuspidalFiniteSmoothSubmodule F n) :
    a.val f ∈ generalLinearCuspidalFiniteSmoothSubmodule F n :=
  ((Langlands.Automorphic.operator_invariant_iff F n _).mpr
    ⟨fun d _ hf => (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)
        ).apply_mem_toSubmodule (AdelicGL.ofFinite F n d) hf,
      fun k _ hf => (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)
        ).apply_mem_toSubmodule (AdelicGL.ofInfinite F n k.val) hf,
      fun b _ hf => generalLinearCuspidal_envelopingAction F n hCT b hf⟩) a f hf

/-- The cuspidal forms are an invariant subspace of all original forms. -/
def cuspidalGeneralLinearFormSubrepresentation :
    Subrepresentation (Langlands.Automorphic.fullAutomorphicAction F n) where
  toSubmodule := (generalLinearCuspidalFiniteSmoothSubmodule F n).comap
    (Langlands.Automorphic.automorphicSubrepresentation F n).toSubmodule.subtype
  apply_mem_toSubmodule a f hf :=
    generalLinearCuspidalFiniteSmoothSubmodule_operator_invariant F n hCT a f.val hf

theorem mem_cuspidalGeneralLinearFormSubrepresentation
    (f : Langlands.Automorphic.AutomorphicForms F n) :
    f ∈ cuspidalGeneralLinearFormSubrepresentation F n hCT ↔
      Langlands.Automorphic.IsCuspidal F n f.val.val := Iff.rfl

/-- The existing operator realization whose all-form image is the cuspidal forms. -/
def cuspidalGeneralLinearOperatorRealization :
    Langlands.Automorphic.OperatorRealization F n :=
  (Langlands.Automorphic.operatorRealizationFullFormOrderIso F n).symm
    (cuspidalGeneralLinearFormSubrepresentation F n hCT)

@[simp]
theorem cuspidalGeneralLinearOperatorRealization_fullFormImage :
    (cuspidalGeneralLinearOperatorRealization F n hCT).fullFormImage =
      cuspidalGeneralLinearFormSubrepresentation F n hCT :=
  (Langlands.Automorphic.operatorRealizationFullFormOrderIso F n).apply_symm_apply _

theorem mem_cuspidalGeneralLinearOperatorRealization_iff
    (f : Langlands.Automorphic.StableAutomorphicFunctions F n) :
    f ∈ cuspidalGeneralLinearOperatorRealization F n hCT ↔
      Langlands.Automorphic.IsCuspidal F n f.val.val := by
  have h := (cuspidalGeneralLinearOperatorRealization F n hCT).mem_fullFormImage_iff
    (Langlands.Automorphic.stableAutomorphicEquiv F n f)
  rw [ContinuousLinearEquiv.symm_apply_apply,
    cuspidalGeneralLinearOperatorRealization_fullFormImage] at h
  exact h.symm

/-- The cuspidal realization is the largest cuspidal operator realization. -/
theorem le_cuspidalGeneralLinearOperatorRealization_iff
    (S : Langlands.Automorphic.OperatorRealization F n) :
    S ≤ cuspidalGeneralLinearOperatorRealization F n hCT ↔ S.IsCuspidal := by
  constructor
  · intro h
    refine S.isCuspidal_iff.mpr fun f => ?_
    rw [operatorRealization_toContinuous_eq]
    exact (mem_cuspidalGeneralLinearOperatorRealization_iff F n hCT _).mp (h f.property)
  · intro h f hf
    have hc := S.isCuspidal_iff.mp h ⟨f, hf⟩
    rw [operatorRealization_toContinuous_eq] at hc
    exact (mem_cuspidalGeneralLinearOperatorRealization_iff F n hCT f).mpr hc

theorem cuspidalGeneralLinearOperatorRealization_isCuspidal :
    (cuspidalGeneralLinearOperatorRealization F n hCT).IsCuspidal :=
  (le_cuspidalGeneralLinearOperatorRealization_iff F n hCT _).mp le_rfl

/-- The uniform cuspidal realization is exactly the uniform cuspidal part. -/
theorem uniformCuspidalGeneralLinearOperatorRealization_eq {N : ℕ}
    (rho : GroupScheme.MatrixRepresentation GLG (Fin N)) (hN : 0 < N) :
    uniformCuspidalGeneralLinearOperatorRealization F n rho hN =
      uniformGeneralLinearOperatorRealization F n rho hN ⊓
        cuspidalGeneralLinearOperatorRealization F n hCT := by
  apply le_antisymm
  · exact le_inf (uniformCuspidalGeneralLinearOperatorRealization_le F n rho hN)
      ((le_cuspidalGeneralLinearOperatorRealization_iff F n hCT _).mpr
        (uniformCuspidalGeneralLinearOperatorRealization_isCuspidal F n rho hN))
  · exact (le_uniformCuspidalGeneralLinearOperatorRealization_iff F n rho hN _).mpr
      ⟨inf_le_left, (le_cuspidalGeneralLinearOperatorRealization_iff F n hCT _).mp inf_le_right⟩

end GeneralLinear

end Langlands.Automorphic.GroupSchemeFunctions
