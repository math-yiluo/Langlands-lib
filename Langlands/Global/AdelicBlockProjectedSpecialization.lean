import Langlands.Global.AdelicBlockAutomorphicSections
import Langlands.Global.AdelicBlockSmoothEnvelopingDeformation
import Langlands.Global.AdelicEisensteinProjectedSpecialization

/-! # Projected Eisenstein specialization on the smooth block sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Filter
open scoped CategoryTheory.MonObj Topology

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions
open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
open Langlands.GeneralLinear (BlockShape)
open AdelicBlockEisensteinGeometry AdelicGroupPoints GeneralLinearGroupPoints
open EisensteinJet PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] (r : ℕ) (B : BlockShape (r + 1))
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local notation "𝕜" => CommRingCat.of F
local notation "n" => r + 1
local notation "GLG" => groupScheme (Fin n) 𝕜
local notation "std" => MatrixRepresentation.standard (Fin n) 𝕜
local notation "wt" => blockShapeWeight B
local notation "P" => blockParabolicScheme (Fin n) 𝕜 wt
local notation "p" => blockParabolicHom (Fin n) 𝕜 wt
local notation "V" => FiniteSmoothRealizedSections F B S
local notation "W" => smoothCompactFiniteSections F B S
local notation "Stable" => StableAutomorphicFunctions F n
local notation "Ops" => FreeOperatorAlgebra F n
local notation "hG" => isConnectedReductive_generalLinear F (Fin n)
local notation "hs" => (hG).smoothDimension_spec
local notation "hc" => adelicDifferentialCommutator_of_smooth F GLG hs
local notation "hK" => isIwasawaCompact_blockParabolic F B
local notation "T" => blockRootData F B
local notation "e" => (T).parameterCoordinates
local notation "E" => (Fin (Module.finrank ℂ (ComplexCharacterParameter F P)) → ℂ)
local notation "R" => fun t : E => deformedSmoothFiniteAction F B S (e t)
local notation "Kact" => smoothCompactAction F B S
local notation "D" => fun t : E => deformedSmoothSectionEnvelopingAction F B S hs hc (e t)

local instance blockSpecializationIsAffine : IsAffine (GLG).X.left :=
  isAffine_groupScheme (Fin n) 𝕜
local instance blockSpecializationParabolicAffine : IsAffine (P).X.left :=
  blockParabolic_isAffine F B
local instance blockSpecializationParabolicClosed : IsClosedImmersion (p).hom.hom.left :=
  isClosedSubgroup_blockParabolicHom (Fin n) 𝕜 wt
local instance blockSpecializationTorusMono : Mono (T).root.data.i.hom.hom.left :=
  (T).torus_mono
local instance blockSpecializationFactorMono :
    Mono (CommGroupScheme.groupHom (T).root.data.f).hom.hom.left :=
  (T).factor_mono
local instance blockSpecializationWeylFinite : Fintype (relativeWeylGroup (T).root.data.i) :=
  @Fintype.ofFinite _ (T).finite_weylGroup
local instance blockSpecializationVAGroup : AddCommGroup V := Submodule.addCommGroup _
local instance blockSpecializationWAGroup : AddCommGroup W := Submodule.addCommGroup _
local instance blockSpecializationRationalGroup :
    AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance blockSpecializationContinuousGroup :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance blockSpecializationFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance blockSpecializationStableGroup : AddCommGroup Stable := Submodule.addCommGroup _
local instance blockSpecializationStableModule : Module ℂ Stable := Submodule.module _

/-- The fixed-carrier family of actual finite, compact and enveloping
operators in the full block-parabolic parameter coordinates. -/
def blockSectionOperatorAction (t : E) : Ops →ₐ[ℂ] Module.End ℂ W :=
  sectionOperatorAction R Kact D t

theorem blockSectionOperatorAction_finite_at_zero (g : FiniteAdelicGL F n) :
    blockSectionOperatorAction F r B S 0 (FreeAlgebra.ι ℂ (Sum.inl (Sum.inl g))) =
      smoothCompactFiniteAction F B S g := by
  simp only [blockSectionOperatorAction, sectionOperatorAction, FreeAlgebra.lift_ι_apply,
    Sum.elim_inl, map_zero, deformedSmoothFiniteAction_zero]

theorem blockSectionOperatorAction_finiteIntegral (t : E) (g : FiniteAdelicGL F n)
    (hg : g ∈ FiniteAdelicGL.standardIntegral F n) :
    blockSectionOperatorAction F r B S t (FreeAlgebra.ι ℂ (Sum.inl (Sum.inl g))) =
      smoothCompactFiniteAction F B S g := by
  simp only [blockSectionOperatorAction, sectionOperatorAction, FreeAlgebra.lift_ι_apply,
    Sum.elim_inl, deformedSmoothFiniteAction_of_mem_standardIntegral F B S _ _ hg]

theorem blockSectionOperatorAction_compact (t : E) (k : standardInfiniteCompact F n) :
    blockSectionOperatorAction F r B S t (FreeAlgebra.ι ℂ (Sum.inl (Sum.inr k))) = Kact k := by
  simp only [blockSectionOperatorAction, sectionOperatorAction, FreeAlgebra.lift_ι_apply,
    Sum.elim_inl, Sum.elim_inr]

theorem blockSectionOperatorAction_enveloping_at_zero (a : ArchimedeanGL.EnvelopingAlgebra F n) :
    blockSectionOperatorAction F r B S 0 (FreeAlgebra.ι ℂ (Sum.inr a)) =
      sectionEnvelopingAction F B S a := by
  simp only [blockSectionOperatorAction, sectionOperatorAction, FreeAlgebra.lift_ι_apply,
    Sum.elim_inr, map_zero, deformedSmoothSectionEnvelopingAction_zero]

/-- Injectivity on the projected seed space in the sufficiently regular
convergence region, for the actual block-parabolic family. -/
def BlockEisensteinInjectiveOnAnchor (π : Module.End ℂ W) : Prop :=
  ∀ᶠ t in eisensteinConvergenceAnchorFilter (T).root (T).splitComponent (T).splitTorus e,
    EisensteinSeriesInjectiveOn F r (hK) (e t) (smoothSectionOnScheme F B S) π.range

/-- The actual block section family specializes a jointly admissible
simple quotient at zero to stable automorphic forms. The analytic inputs
are exact continuation and convergence-region injectivity. -/
theorem exists_freeOperatorQuotient_of_block_projected_specialization
    (hS : ∀ i, (S i).IsJointlyAdmissible)
    (π : Module.End ℂ W) [FiniteDimensional ℂ π.range]
    (hcont : EisensteinMeromorphicContinuationStatement.{u})
    (hinj : BlockEisensteinInjectiveOnAnchor F r B S π)
    (hProjection : ∀ U : Submodule ℂ W, FiniteDimensional ℂ U →
      ∃ b : Ops, ∀ t w, w ∈ U → blockSectionOperatorAction F r B S t b w = π w)
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (aY : Ops →ₐ[ℂ] Module.End ℂ Y) (ha : Representation.IsIrreducible aY.toMonoidHom) :
    letI := moduleOfAlgebraAction (blockSectionOperatorAction F r B S 0)
    letI := moduleOfAlgebraAction aY
    letI := moduleOfAlgebraAction (stableFreeOperatorAction F n)
    ∀ (U : Submodule Ops W) (q : U →ₗ[Ops] Y), Function.Surjective q →
      ∀ y : Y, y ≠ 0 →
        (∀ x : U, q x = y → ∃ x' : U, x'.val = π x.val ∧ q x' = y) →
        ∃ U' : Submodule Ops Stable, ∃ u : U' →ₗ[Ops] Y, Function.Surjective u := by
  have hrho : IsClosedSubgroup std := by
    change IsClosedImmersion (𝟙 (GLG).X.left)
    infer_instance
  have hKinfty (k : standardInfiniteCompact F n) :
      ofInfinite F GLG ((infiniteHomeomorph F n).symm k.val) ∈ standardCompactPoints F n := by
    have hk : (infiniteHomeomorph F n).symm k.val ∈ generalLinearStandardInfiniteCompact F n := by
      change infiniteHomeomorph F n ((infiniteHomeomorph F n).symm k.val) ∈ standardInfiniteCompact F n
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact k.property
    exact ofInfinite_mem_standardCompactPoints F ⟨_, hk⟩
  exact exists_freeOperatorQuotient_of_adelic_projected_specialization F r π
    std hs hc (Nat.succ_pos r) hrho (hG) (T).root (T).splitComponent (T).splitTorus
    (blockUnipotentInclusion_isLeviGeometricUnipotentRadical F B)
    (hK) (standardCompactPoints_isMaximalCompact F n) (standardCompactPoints_comap_ofInfinite F n)
    hKinfty e (smoothSectionOnScheme F B S)
    (SchemeSection.isAutomorphicFunctionOn F B S (Nat.succ_pos r) hS hs hc)
    (hasSmoothHeightPairings_blockParabolic F B hs) (smoothSectionOnScheme_hasSmoothSlices F B S hs)
    R Kact D
    (deformedSmoothFiniteAction_mem_finiteHolomorphicSections F B S (e).toLinearMap)
    (deformedSmoothSectionEnvelopingAction_real_generator_mem_finiteHolomorphicSections F B S hs hc (e).toLinearMap)
    (fun t => smoothSectionOnScheme_deformedFiniteAction F B S (e t))
    (smoothSectionOnScheme_compactAction F B S)
    (fun t => deformedSmoothSectionEnvelopingAction_real_generator_onScheme F B S hs hc (e t))
    hcont hinj hProjection 0 aY ha

end Langlands.Global.AdelicBlockScalarSections
