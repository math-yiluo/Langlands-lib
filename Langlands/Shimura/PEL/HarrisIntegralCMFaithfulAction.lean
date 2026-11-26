import Langlands.Shimura.PEL.HarrisIntegralCMPolarizedAction
import Langlands.Shimura.PEL.HarrisTaylorCMBaseAdmissibility
import Langlands.AbelianScheme.Tate.IntegralReflectionAlgebra
import Langlands.AlgebraicGeometry.Picard.MumfordUnit
import Langlands.AlgebraicGeometry.RelativeDimensionLoci
import Langlands.AlgebraicGeometry.SmoothPureDimensionProof

/-! # Faithfulness of Harris action families from their dimension -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- A positive-dimensional abelian scheme on a nonempty base where every
positive integer is a unit has a nontrivial rational endomorphism ring. -/
theorem rationalEnd_nontrivial_of_relativeDimension
    {S : Scheme.{0}} (B : AbelianScheme S) (hS : Nonempty S)
    (hu : ∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
    (g : ℕ) (hg : 0 < g) (hdim : B.HasRelativeDimension g) :
    Nontrivial (Rationalization.End B) := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have he : Rationalization.ofEnd B 1 = Rationalization.ofEnd B 0 := by
    rw [map_one, map_zero, h]
  have he' : Rationalization.ofHom (𝟙 B) = Rationalization.ofHom (0 : B ⟶ B) :=
    congrArg CategoryTheory.End.asHom he
  have hid : 𝟙 B = (0 : B ⟶ B) := (Tate.ofHom_injective hu B B) he'
  have hsection : B.X.hom ≫ unitSection B = 𝟙 B.X.left := by
    rw [← hom_id, hid]
    exact (unitPoint_left B B.X).symm
  let : IsIso B.X.hom := ⟨⟨unitSection B, hsection, unitSection_comp B⟩⟩
  let x : B.X.left := unitSection B (Classical.choice hS)
  have hg' := Langlands.AlgebraicGeometry.smoothPureDimension.2 B.X.left S B.X.hom g hdim
  have h0 := (hasPureDimensionFibers_zero_iff_locallyQuasiFinite B.X.hom).mpr
    (inferInstance : LocallyQuasiFinite B.X.hom)
  have heq := ((hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq _ _).mp hg' x).symm.trans
    ((hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq _ _).mp h0 x)
  exact hg.ne' (by exact_mod_cast heq)

end Langlands.AbelianScheme

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

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
    (P : Prerequisites.{0})
    {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
    (B : AbelianScheme S) (W : DualWitness B)
    (lam : B ⟶ W.dual P) (hLam : W.IsPolarization P lam)
    (T : Over S) [QuasiSeparatedSpace T.left] (hT : Nonempty T.left)
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n)
    (a : D.harrisHodgePELIntegralOrder C →+*
      CategoryTheory.End ((baseChange T.hom).obj B))
    (ha : harrisIntegralCMFullActionCondition D C P p B W lam T a)

local notation "BT" => (baseChange T.hom).obj B
local notation "WT" => W.pullback P T.hom
local notation "lamT" => W.pullbackMap P T.hom WT lam
local notation "iT" => D.harrisHodgePELRationalAction C BT a

include p hT hdim in
omit [IsCMField F] [IsScalarTower ℚ F A] [QuasiSeparatedSpace T.left] in
/-- The rational extension of the actual order action is faithful on
a nonempty test for a family of the specified Harris dimension. -/
theorem harrisIntegralCMAction_injective_of_dimension :
    Function.Injective iT := by
  let : IsSimpleRing A := D.simple
  have hn : 0 < n := lt_trans Nat.zero_lt_one D.rank_gt_one
  have hg : 0 < Module.finrank ℚ E * n ^ 2 :=
    mul_pos Module.finrank_pos (pow_pos hn 2)
  let : Nontrivial (Rationalization.End BT) :=
    rationalEnd_nontrivial_of_relativeDimension BT hT
      (HarrisTaylorCMWeilLevel.cmBaseTorsionUnit (T.hom ≫ p)) _ hg
      (HarrisTaylor.prescribedRelativeDimension_baseChange E B n hdim T.hom)
  exact RingHom.injective (iT).toRingHom

/-- The full Harris action condition on a nonempty test of the prescribed
dimension gives the actual faithful polarized family used by the Weil tower. -/
def harrisIntegralCMFullActionPolarizedActionOfDimension :
    letI := auxiliaryStarRing D C
    PolarizedWeilLevel.PolarizedAction P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      T.left A := by
  letI := auxiliaryStarRing D C
  exact {
    actionObj := RationalAlgebraAction.of BT iT
    hasDual := (WT).hasDual
    geometry := (WT).geometry
    inversePoincare := (WT).inverseBundle
    evaluation := (WT).evaluation
    dualEndAdditivity := relativeDualSchemeMapAdditivity P.preservation P.stability
      T.left BT BT (WT).hasDual (WT).hasDual
    polarization := lamT
    isPolarization := P.polarizationBaseChange P.preservation P.square P.universality
      P.stability P.composition P.unitCoherence P.associativity P.comparison P.symmetry
      P.compatibility S T.left T.hom B W.hasDual W.geometry W.inverseBundle W.evaluation
      (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation lam hLam
    faithful := harrisIntegralCMAction_injective_of_dimension D C p B T hT hdim a
    involutionCompatible :=
      (harrisIntegralCMFullActionCondition_involutionCompatible
        D C P p B W lam T a ha).1 }

local notation "X" => harrisIntegralCMFullActionPolarizedActionOfDimension
  D C P p B W lam hLam T hT hdim a ha

omit [IsCMField F] in
/-- The action family satisfies the original normalized determinant and
dimension condition on the same test and for the same reflex map. -/
theorem harrisIntegralCMFullActionPolarizedActionOfDimension_condition :
    letI := auxiliaryStarRing D C
    D.HarrisTaylorCMDeterminantDimensionCondition C (T.hom ≫ p)
      (X).actionObj.abelianScheme (X).actionObj.action := by
  let := auxiliaryStarRing D C
  exact ⟨ha.2, HarrisTaylor.prescribedRelativeDimension_baseChange E B n hdim T.hom⟩

variable (h : Global.RationalProfiniteIntegerAdeleComparison)
    {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ T.left)
    (heta : Nonempty (letI := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
      Tate.AdelicFrame BT h iT ((Global.FiniteAdeles ℚ) ⊗[ℚ] A) s))

/-- Where a frame is given, both constructions have the same action,
dual data and polarization on the same family. -/
theorem harrisIntegralCMFullActionPolarizedActionOfDimension_eq_of_frame :
    letI := auxiliaryStarRing D C
    X = harrisIntegralCMFullActionPolarizedAction D C P p B W lam hLam T a ha h s heta :=
  rfl

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
