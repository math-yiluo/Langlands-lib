import Langlands.AbelianScheme.ProjectiveIntegralActionScheme
import Langlands.Shimura.PEL.HarrisIntegralCMClosedActionLocus

/-! # Actual CM action schemes for projective families over noetherian affine bases -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel.ProjectiveCMAction

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F]
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
    (R : Type) [CommRing R] [IsNoetherianRing R]
    (p : Spec (.of R) ⟶ Spec (.of F))
    (B : Langlands.AbelianScheme (Spec (.of R)))
    (hB : Langlands.AlgebraicGeometry.IsHProjective B.X.hom)
    (W : DualWitness B) (lam : B ⟶ W.dual P)

local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "basisO" => D.harrisHodgePELIntegralBasis C
local notation "endScheme" => ProjectiveIntegralAction.endomorphismScheme R B hB
local notation "endIso" => ProjectiveIntegralAction.endomorphismSchemeLocallyNoetherianIso R B hB
local notation "raw" => ProjectiveIntegralAction.scheme R B hB basisO
local notation "rawAction" => ProjectiveIntegralAction.universalAction R B hB basisO

/-- The actual joint CM action scheme. Its endomorphism representative is
constructed from the projective family, rather than supplied as an input. -/
def scheme : Over (Spec (.of R)) :=
  harrisIntegralCMClosedActionLocus D C P p B W lam endScheme endIso

local notation "Z" => scheme D C P R p B hB W lam

/-- The actual closed inclusion into the finite integral-action equation scheme. -/
def inclusion : Z ⟶ raw :=
  harrisIntegralCMClosedActionLocusInclusion D C P p B W lam endScheme endIso

local notation "inc" => inclusion D C P R p B hB W lam

instance inclusion_isClosedImmersion : IsClosedImmersion (inc).left :=
  inferInstanceAs (IsClosedImmersion
    (harrisIntegralCMClosedActionLocusInclusion D C P p B W lam endScheme endIso).left)

instance scheme_locallyOfFiniteType : LocallyOfFiniteType (Z).hom :=
  inferInstanceAs (LocallyOfFiniteType
    (harrisIntegralCMClosedActionLocus D C P p B W lam endScheme endIso).hom)

instance scheme_isSeparated : IsSeparated (Z).hom :=
  inferInstanceAs (IsSeparated
    (harrisIntegralCMClosedActionLocus D C P p B W lam endScheme endIso).hom)

instance scheme_isLocallyNoetherian : IsLocallyNoetherian (Z).left :=
  LocallyOfFiniteType.isLocallyNoetherian (Z).hom

/-- The joint scheme naturally represents full actual Rosati equations and the
unchanged normalized determinant on all locally noetherian tests. -/
def schemeIso :
    (locallyNoetherianTestInclusion (Spec (.of R))).op ⋙ uliftYoneda.{0}.obj Z ≅
      (harrisIntegralCMFullActionSubfunctor D C P p B W lam).toFunctor :=
  harrisIntegralCMClosedActionLocusFullIso D C P p B W lam endScheme endIso

/-- The actual universal integral action on the direct pullback of the original family. -/
def universalAction :
    O →+* CategoryTheory.End ((baseChange (Z).hom).obj B) :=
  (relativeEndRestrict B inc).comp rawAction

local notation "aZ" => universalAction D C P R p B hB W lam

variable
    (T : ObjectProperty.FullSubcategory
      (fun T : Over (Spec (.of R)) => IsLocallyNoetherian T.left))

local instance test_isLocallyNoetherian : IsLocallyNoetherian T.obj.left := T.property

/-- Classification is an equivalence with actual integral actions on the original
direct test family, without any representability input. -/
def homEquiv :
    (T.obj ⟶ Z) ≃
      {a : O →+* CategoryTheory.End ((baseChange T.obj.hom).obj B) //
        harrisIntegralCMFullActionCondition D C P p B W lam T.obj a} :=
  harrisIntegralCMClosedActionLocusFullHomEquiv D C P p B W lam endScheme endIso T

/-- This equivalence restricts the actual universal action along the actual test morphism. -/
theorem homEquiv_apply (k : T.obj ⟶ Z) :
    (homEquiv D C P R p B hB W lam T k).val =
      (relativeEndRestrict B k).comp aZ := by
  have hv := harrisIntegralCMClosedActionLocusFullHomEquiv_apply
    D C P p B W lam endScheme endIso T k
  refine hv.trans ?_
  ext a
  change Langlands.GroupScheme.Cartier.restrict B.toCommGroupScheme B.toCommGroupScheme
      (k ≫ inc) (rawAction a) =
    Langlands.GroupScheme.Cartier.restrict B.toCommGroupScheme B.toCommGroupScheme k
      (Langlands.GroupScheme.Cartier.restrict B.toCommGroupScheme B.toCommGroupScheme
        inc (rawAction a))
  exact Langlands.GroupScheme.Cartier.restrict_comp B.toCommGroupScheme B.toCommGroupScheme
    k inc (rawAction a)

/-- Every full joint action has exactly one actual classifying morphism,
specified by literal equality with the restriction of the universal action. -/
theorem universalAction_existsUnique
    (a : O →+* CategoryTheory.End ((baseChange T.obj.hom).obj B))
    (ha : harrisIntegralCMFullActionCondition D C P p B W lam T.obj a) :
    ∃! k : T.obj ⟶ Z, (relativeEndRestrict B k).comp aZ = a := by
  let e := homEquiv D C P R p B hB W lam T
  let k := e.symm ⟨a, ha⟩
  have value := homEquiv_apply D C P R p B hB W lam T
  have hk : (relativeEndRestrict B k).comp aZ = a :=
    (value k).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩))
  refine ⟨k, hk, ?_⟩
  intro l hl
  apply e.injective
  apply Subtype.ext
  exact ((value l).trans hl).trans ((value k).trans hk).symm

/-- Every actual classifying morphism gives the full original action condition. -/
theorem universalAction_restrict_condition (k : T.obj ⟶ Z) :
    harrisIntegralCMFullActionCondition D C P p B W lam T.obj
      ((relativeEndRestrict B k).comp aZ) := by
  rw [← homEquiv_apply D C P R p B hB W lam T k]
  exact (homEquiv D C P R p B hB W lam T k).property

omit T in
/-- The actual universal action itself satisfies the full original equations
and normalized determinant, with the canonical direct pullback dual and map. -/
theorem universalAction_condition :
    harrisIntegralCMFullActionCondition D C P p B W lam Z aZ := by
  let Q : ObjectProperty.FullSubcategory
      (fun T : Over (Spec (.of R)) => IsLocallyNoetherian T.left) :=
    ⟨Z, inferInstance⟩
  have hc := universalAction_restrict_condition D C P R p B hB W lam Q (𝟙 Z)
  have he : (relativeEndRestrict B (𝟙 Z)).comp aZ = aZ := by
    ext a
    exact Langlands.GroupScheme.Cartier.restrict_id B.toCommGroupScheme
      B.toCommGroupScheme Z (aZ a)
  rw [he] at hc
  exact hc

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel.ProjectiveCMAction
