import Langlands.Shimura.PEL.HarrisTaylorCMNormalKernelPair
import Langlands.Shimura.Coefficients.Etale

/-! # Geometric torsor input from the exact CM normal comparison -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme

universe u

/-- A morphism from a nonempty one-point scheme factors through exactly one
summand of the actual scheme coproduct. -/
private theorem existsUnique_coproductFactor {I : Type u} (X : I → Scheme.{u})
    {Z : Scheme.{u}} [Subsingleton Z] [Nonempty Z] (f : Z ⟶ ∐ X) :
    ∃! i : I, ∃ a : Z ⟶ X i, a ≫ Sigma.ι X i = f := by
  classical
  let z : Z := Classical.ofNonempty
  obtain ⟨⟨i, x⟩, hx⟩ := (AlgebraicGeometry.sigmaMk X).surjective (f z)
  have hx' : Sigma.ι X i x = f z := by
    simpa only [AlgebraicGeometry.sigmaMk_mk] using hx
  have hrange : Set.range f ⊆ Set.range (Sigma.ι X i) := by
    rintro _ ⟨w, rfl⟩
    exact ⟨x, hx'.trans (congrArg f (Subsingleton.elim z w))⟩
  refine ⟨i, ⟨IsOpenImmersion.lift (Sigma.ι X i) f hrange,
    IsOpenImmersion.lift_fac _ _ _⟩, ?_⟩
  rintro j ⟨a, ha⟩
  have hj : Sigma.ι X j (a z) = f z := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun q : Z ⟶ ∐ X => q z) ha
  exact congrArg Sigma.fst ((AlgebraicGeometry.sigmaι_eq_iff X j i _ _).mp (hj.trans hx'.symm))

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)


variable {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})


local notation "schemes" => representedCMSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "quotientAction" => representedCMNormalQuotientAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "projection" => representedCMNormalProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

variable (R : ∀ U : SmallCMLevel D,
  CMLevelRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U)
  (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

local notation "kernelComparison" => representedCMNormalKernelComparison D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "graph" => representedCMNormalGraph D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- Invertibility of the concrete normal comparison gives unique original
residual transport on every field-valued fiber. -/
theorem representedCMNormal_existsUnique_transport
    [IsIso (kernelComparison R U V hVU)]
    (Ω : Type) [Field Ω]
    (a b : Spec (CommRingCat.of Ω) ⟶ (schemes R).obj V)
    (hab : a ≫ projection R U V hVU = b ≫ projection R U V hVU) :
    ∃! g : SmallCMResidualGroup D U V, a ≫ (quotientAction R U V hVU).ρ g = b := by
  let c := pullback.lift a b hab
  let t := c ≫ inv (kernelComparison R U V hVU)
  obtain ⟨g, ⟨d, hd⟩, hg⟩ := existsUnique_coproductFactor
    (fun _ : SmallCMResidualGroup D U V => (schemes R).obj V) t
  have hdc : d ≫ graph R U V hVU g = c := by
    rw [← representedCMNormalKernelComparison_ι, ← Category.assoc, hd]
    simp only [t, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hda : d = a := by
    have he := congrArg (fun q => q ≫ pullback.fst
      (projection R U V hVU) (projection R U V hVU)) hdc
    simpa only [Category.assoc, representedCMNormalGraph_fst, Category.comp_id,
      c, pullback.lift_fst] using he
  have hgb : a ≫ (quotientAction R U V hVU).ρ g = b := by
    have he := congrArg (fun q => q ≫ pullback.snd
      (projection R U V hVU) (projection R U V hVU)) hdc
    simpa only [hda, Category.assoc, representedCMNormalGraph_snd,
      c, pullback.lift_snd] using he
  refine ⟨g, hgb, ?_⟩
  intro g' hg'
  apply hg g'
  refine ⟨a, ?_⟩
  apply (cancel_mono (kernelComparison R U V hVU)).mp
  rw [Category.assoc, representedCMNormalKernelComparison_ι]
  have hc : a ≫ graph R U V hVU g' = c := by
    apply pullback.hom_ext
    · simp only [Category.assoc, representedCMNormalGraph_fst, Category.comp_id,
        c, pullback.lift_fst]
    · simpa only [Category.assoc, representedCMNormalGraph_snd, c,
        pullback.lift_snd] using hg'
  rw [hc]
  simp only [t, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The original residual action as an object of the actual coarse scheme's
small etale category, under the exact etaleness premise for original forgetting. -/
def representedCMNormalEtaleAction [Etale (projection R U V hVU)] :
    Action ((schemes R).obj U).Etale (SmallCMResidualGroup D U V) where
  V := Scheme.Etale.mk (projection R U V hVU)
  ρ :=
    { toFun := fun g => MorphismProperty.Over.homMk ((quotientAction R U V hVU).ρ g)
        (representedCMNormalProjection_invariant D C preservation composition
          unitCoherence associativity comparison symmetry stability square universality
          dualityNaturality polarizationStability compatibility h htor R U V hVU g)
      map_one' := by
        apply MorphismProperty.Over.Hom.ext
        exact (quotientAction R U V hVU).ρ.map_one
      map_mul' := fun g g' => by
        apply MorphismProperty.Over.Hom.ext
        exact (quotientAction R U V hVU).ρ.map_mul g g' }

local notation "etaleAction" => representedCMNormalEtaleAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- The underlying etale object is exactly the original fine scheme. -/
@[simp] theorem representedCMNormalEtaleAction_left
    [Etale (projection R U V hVU)] :
    (etaleAction R U V hVU).V.left = (schemes R).obj V := rfl

/-- Its structural map is exactly original forgetting. -/
@[simp] theorem representedCMNormalEtaleAction_hom
    [Etale (projection R U V hVU)] :
    (etaleAction R U V hVU).V.hom = projection R U V hVU := rfl

/-- The etale action uses the original inverse-right residual translations. -/
@[simp] theorem representedCMNormalEtaleAction_ρ_left
    [Etale (projection R U V hVU)] (g : SmallCMResidualGroup D U V) :
    ((etaleAction R U V hVU).ρ g).left = (quotientAction R U V hVU).ρ g := rfl

/-- The exact geometric premises for the original normal cover supply the
existing finite-geometric-torsor input used by coefficient descent. -/
theorem representedCMNormalEtaleAction_isFiniteGeometricTorsor
    [Etale (projection R U V hVU)]
    [IsFinite (projection R U V hVU)]
    [IsIso (kernelComparison R U V hVU)]
    (hsurj : Function.Surjective (projection R U V hVU)) :
    Coefficients.IsFiniteGeometricTorsor ((schemes R).obj U) (etaleAction R U V hVU) := by
  refine ⟨smallCMResidualGroup_finite D U V,
    (inferInstance : IsFinite (projection R U V hVU)), hsurj, ?_⟩
  intro Ω _ _ a b hab
  exact representedCMNormal_existsUnique_transport D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor R U V hVU Ω a b hab

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

local notation "chosen" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

/-- The original normal action in the small etale category for the exact
existing CM representability target, with the same original forgetting premise. -/
def cmNormalEtaleAction [Etale (projection chosen U V hVU)] :=
  etaleAction chosen U V hVU

/-- Exact CM representability and the stated geometric premises give precisely
the existing torsor predicate; none of those premises is proved here. -/
theorem cmNormalEtaleAction_isFiniteGeometricTorsor
    [Etale (projection chosen U V hVU)]
    [IsFinite (projection chosen U V hVU)]
    [IsIso (kernelComparison chosen U V hVU)]
    (hsurj : Function.Surjective (projection chosen U V hVU)) :
    Coefficients.IsFiniteGeometricTorsor ((schemes chosen).obj U)
      (cmNormalEtaleAction D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor U V hVU q) :=
  representedCMNormalEtaleAction_isFiniteGeometricTorsor D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor chosen U V hVU hsurj

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
