import Langlands.Shimura.PEL.HarrisTaylorCMDivisionCriteria
import Mathlib.RingTheory.Smooth.Field

/-! # Artinian test lifting with a section -/

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AlgebraicGeometry

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
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

local notation "test" => specTest D C preservation composition unitCoherence associativity
  comparison symmetry stability square universality
local notation "testMap" => specTestMap D C preservation composition unitCoherence associativity
  comparison symmetry stability square universality
local notation "moduli" => smallLevelClassPresheafTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- A section compatible with the structure map lifts every normalized class. -/
theorem surjective_specTestMap_of_section (U : SmallCMLevel D)
    {B' B : Type} [CommRing B'] [CommRing B] [IsNoetherianRing B'] [IsNoetherianRing B]
    (φ : B' →+* B) (β : Spec (.of B') ⟶ Spec (.of F)) (σ : B →+* B')
    (hφσ : φ.comp σ = RingHom.id B)
    (hβ : Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom φ) ≫ β = β) :
    Function.Surjective (((moduli).obj U).map (testMap φ β).op) := by
  let X := test B (Spec.map (CommRingCat.ofHom φ) ≫ β)
  let Y := test B' β
  let i : X ⟶ Y := testMap φ β
  let r : Y ⟶ X := ObjectProperty.homMk (Over.homMk (Spec.map (CommRingCat.ofHom σ)) hβ)
  have hir : i ≫ r = 𝟙 X := by
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom σ) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφσ, CommRingCat.ofHom_id, Spec.map_id]
  let P := (moduli).obj U
  intro x
  refine ⟨P.map r.op x, ?_⟩
  have hr : r.op ≫ i.op = 𝟙 _ := congrArg Quiver.Hom.op hir
  have hmap : P.map r.op ≫ P.map i.op = 𝟙 _ := by
    rw [← P.map_comp, hr]
    exact P.map_id _
  exact ConcreteCategory.congr_hom hmap x

private theorem field_formallySmooth (K k : Type) [Field K] [CharZero K] [Field k]
    [Algebra K k] : _root_.Algebra.FormallySmooth K k := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K k
  let := hs.isAlgebraic_field
  exact _root_.Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

/-- The field-valued tests of the normalized small-level Artinian lifting criterion. -/
def CMLevelArtinianFieldTargetLiftingStatement (U : SmallCMLevel D) : Prop :=
  ∀ (B' B : Type) [CommRing B'] [IsLocalRing B'] [IsArtinianRing B'] [Field B]
    (φ : B' →+* B), Function.Surjective φ →
      maximalIdeal B' * RingHom.ker φ = ⊥ →
      ∀ β : Spec (.of B') ⟶ Spec (.of F),
        Function.Surjective (((moduli).obj U).map (testMap φ β).op)

/-- Every field-valued test in the Artinian lifting statement has a lift. -/
theorem cmLevelArtinianFieldTargetLifting (U : SmallCMLevel D) :
    CMLevelArtinianFieldTargetLiftingStatement D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor U := by
  intro B' B _ _ _ _ φ hφ hker β
  let β' : F →+* B' := (Spec.preimage β).hom
  let : Algebra F B' := β'.toAlgebra
  let : Algebra F B := (φ.comp β').toAlgebra
  let q : B' →ₐ[F] B := ⟨φ, fun _ => rfl⟩
  have hnil : IsNilpotent (RingHom.ker φ) := by
    refine ⟨2, ?_⟩
    rw [pow_two]
    exact (congrArg (· * RingHom.ker φ) (ker_eq_maximalIdeal φ hφ)).trans hker
  let := field_formallySmooth F B
  let σ := _root_.Algebra.FormallySmooth.liftOfSurjective (AlgHom.id F B) q hφ hnil
  have hφσ : φ.comp σ.toRingHom = RingHom.id B := by
    ext b
    exact _root_.Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id F B) q hφ hnil b
  have hσβ : σ.toRingHom.comp (φ.comp β') = β' := by
    ext b
    exact σ.commutes b
  have hβ' : Spec.map (CommRingCat.ofHom β') = β := Spec.map_preimage β
  apply surjective_specTestMap_of_section D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor U φ β σ.toRingHom hφσ
  rw [← hβ', ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, hσβ]

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
