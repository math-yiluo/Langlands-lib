import Langlands.Shimura.PEL.HarrisTaylorCMOrdinaryClasses
import Langlands.Shimura.PEL.HarrisTaylorCMTateDisconnectedPresheaf

/-! # The ordinary normalized CM presheaf on the full original test category -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open HarrisPolarizedWeilLevel HarrisNumericalWeilLevel
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
  (P : Prerequisites.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "Bases" => AdmissibleCMBaseCategory D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
local notation "DisBases" => ComponentwiseAdmissibleCMBaseCategory D C
  P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability P.square P.universality
local notation "OClassesAt" X:max a:max =>
  TateNormalizedCMOrdinaryIsoClass D C P compatibility h htor X a
local notation "classEquiv" => tateNormalizedCMOrdinaryClassEquiv D C P compatibility h htor
local notation "NMove" => tateNormalizedCMGeometricComparison D C P compatibility h htor
local notation "NFamily" => TateNormalizedCMGeometricFamily D C P compatibility h htor
local notation "NFamilyPull" => tateNormalizedCMFamilyPullback D C P
  dualityNaturality polarizationStability compatibility h htor
local notation "NDisFamily" => TateNormalizedCMComponentwiseFamily D C P compatibility h htor
local notation "NDisPull" => tateNormalizedCMDisconnectedPullback D C P
  dualityNaturality polarizationStability compatibility h htor
local notation "NPresheaf" => tateNormalizedCMDisconnectedPresheaf D C P
  dualityNaturality polarizationStability compatibility h htor
local notation "component" => componentCMBase D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
local notation "componentHom" => componentCMBaseHomTo D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
local notation "lev" U:max => (hodgeLevelFunctor D C).obj U

/-- Canonical ordinary point comparison uses actual representative transport
along any geometric path; path independence removes this choice on classes. -/
def tateNormalizedCMOrdinaryGeometricComparison (X : Bases)
    (a b : HarrisGeometricPoint X.obj.left) (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    (OClassesAt X a) U hU ≃ (OClassesAt X b) U hU :=
  tateNormalizedCMOrdinaryClassPointEquiv D C P compatibility h htor X a b
    (Classical.choice (geometricPathExists a.hom b.hom a.finiteFibers b.finiteFibers)) U hU

local notation "move" => tateNormalizedCMOrdinaryGeometricComparison D C P
  compatibility h htor

/-- The identity-on-models equivalence commutes with canonical point comparison. -/
@[simp] theorem tateNormalizedCMOrdinaryClassEquiv_geometricComparison (X : Bases)
    (a b : HarrisGeometricPoint X.obj.left) (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (q : (OClassesAt X a) U hU) :
    classEquiv X b U hU (move X a b U hU q) =
      NMove X a b U (classEquiv X a U hU q) :=
  tateNormalizedCMOrdinaryClassEquiv_pointMap D C P compatibility h htor X a b _ U hU q

/-- Ordinary compatible families retain the actual-isomorphism class at every
geometric point and require the actual canonical comparison equations. -/
def TateNormalizedCMOrdinaryGeometricFamily (X : Bases) (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) : Type 1 :=
  {x : (a : HarrisGeometricPoint X.obj.left) → (OClassesAt X a) U hU //
    ∀ a b, move X a b U hU (x a) = x b}

local notation "Family" => TateNormalizedCMOrdinaryGeometricFamily D C P
  compatibility h htor

/-- Compatible ordinary and unchanged normalized families are equivalent by the
identity on actual models at every geometric point. -/
def tateNormalizedCMOrdinaryFamilyEquiv (X : Bases) (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    Family X U hU ≃ NFamily X U where
  toFun x := ⟨fun a => classEquiv X a U hU (x.val a), by
    intro a b
    rw [← tateNormalizedCMOrdinaryClassEquiv_geometricComparison, x.property a b]⟩
  invFun x := ⟨fun a => (classEquiv X a U hU).symm (x.val a), by
    intro a b
    apply (classEquiv X b U hU).injective
    rw [tateNormalizedCMOrdinaryClassEquiv_geometricComparison,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact x.property a b⟩
  left_inv x := by
    apply Subtype.ext
    funext a
    exact (classEquiv X a U hU).symm_apply_apply (x.val a)
  right_inv x := by
    apply Subtype.ext
    funext a
    exact (classEquiv X a U hU).apply_symm_apply (x.val a)

local notation "familyEquiv" => tateNormalizedCMOrdinaryFamilyEquiv D C P
  compatibility h htor

/-- Pullback uses actual ordinary quotient base change at every pushed point. -/
def tateNormalizedCMOrdinaryFamilyPullback {X Y : Bases} (f : Y ⟶ X)
    (U : HarrisLevel D) (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    Family X U hU → Family Y U hU :=
  fun x => ⟨fun a => tateNormalizedCMOrdinaryClassBaseChange D C P compatibility h htor
    dualityNaturality polarizationStability f a U hU (x.val (a.comp f.hom.left)), by
      intro a b
      apply (classEquiv Y b U hU).injective
      rw [tateNormalizedCMOrdinaryClassEquiv_geometricComparison,
        tateNormalizedCMOrdinaryClassEquiv_baseChange,
        tateNormalizedCMOrdinaryClassEquiv_baseChange]
      exact (NFamilyPull f U (familyEquiv X U hU x)).property a b⟩

local notation "familyPull" => tateNormalizedCMOrdinaryFamilyPullback D C P
  dualityNaturality polarizationStability compatibility h htor

/-- Pointwise identity comparison commutes with actual family pullback. -/
@[simp] theorem tateNormalizedCMOrdinaryFamilyEquiv_pullback {X Y : Bases} (f : Y ⟶ X)
    (U : HarrisLevel D) (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x : Family X U hU) :
    familyEquiv Y U hU (familyPull f U hU x) =
      NFamilyPull f U (familyEquiv X U hU x) := by
  apply Subtype.ext
  funext a
  exact tateNormalizedCMOrdinaryClassEquiv_baseChange D C P compatibility h htor
    dualityNaturality polarizationStability f a U hU (x.val (a.comp f.hom.left))

/-- Actual ordinary families on all the actual connected component schemes. -/
def TateNormalizedCMOrdinaryComponentwiseFamily (X : DisBases) (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) : Type 1 :=
  ∀ c : _root_.ConnectedComponents X.obj.left, Family (component X c) U hU

local notation "DisFamily" => TateNormalizedCMOrdinaryComponentwiseFamily D C P
  compatibility h htor

/-- The pointwise identity comparison on every actual component is an equivalence. -/
def tateNormalizedCMOrdinaryComponentwiseEquiv (X : DisBases) (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    DisFamily X U hU ≃ NDisFamily X U :=
  Equiv.piCongrRight (fun c => familyEquiv (component X c) U hU)

local notation "componentwiseEquiv" => tateNormalizedCMOrdinaryComponentwiseEquiv D C P
  compatibility h htor

/-- Pullback uses actual restricted component morphisms and actual ordinary
class pullback at each of their pushed geometric points. -/
def tateNormalizedCMOrdinaryDisconnectedPullback {X Y : DisBases} (f : Y ⟶ X)
    (U : HarrisLevel D) (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    DisFamily X U hU → DisFamily Y U hU :=
  fun x c => familyPull (componentHom f c (componentMap f.hom.left c) rfl) U hU
    (x (componentMap f.hom.left c))

local notation "pull" => tateNormalizedCMOrdinaryDisconnectedPullback D C P
  dualityNaturality polarizationStability compatibility h htor

/-- The componentwise comparison is natural for every original test morphism. -/
@[simp] theorem tateNormalizedCMOrdinaryComponentwiseEquiv_pullback {X Y : DisBases}
    (f : Y ⟶ X) (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) (x : DisFamily X U hU) :
    componentwiseEquiv Y U hU (pull f U hU x) =
      NDisPull f U (componentwiseEquiv X U hU x) := by
  funext c
  exact tateNormalizedCMOrdinaryFamilyEquiv_pullback D C P dualityNaturality
    polarizationStability compatibility h htor
    (componentHom f c (componentMap f.hom.left c) rfl) U hU (x (componentMap f.hom.left c))

/-- Actual ordinary componentwise pullback preserves identities. -/
@[simp] theorem tateNormalizedCMOrdinaryDisconnectedPullback_id (X : DisBases)
    (U : HarrisLevel D) (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x : DisFamily X U hU) : pull (𝟙 X) U hU x = x := by
  apply (componentwiseEquiv X U hU).injective
  rw [tateNormalizedCMOrdinaryComponentwiseEquiv_pullback]
  exact tateNormalizedCMDisconnectedPullback_id D C P dualityNaturality
    polarizationStability compatibility h htor X U _

/-- Actual ordinary componentwise pullback composes on the full test category. -/
theorem tateNormalizedCMOrdinaryDisconnectedPullback_comp {X Y Z : DisBases}
    (f : Y ⟶ X) (g : Z ⟶ Y) (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) (x : DisFamily X U hU) :
    pull g U hU (pull f U hU x) = pull (g ≫ f) U hU x := by
  apply (componentwiseEquiv Z U hU).injective
  simp only [tateNormalizedCMOrdinaryComponentwiseEquiv_pullback]
  exact tateNormalizedCMDisconnectedPullback_comp D C P dualityNaturality
    polarizationStability compatibility h htor f g U _

/-- At a fixed source-stabilizing original level, ordinary actual-isomorphism
classes form a presheaf on the full original componentwise admissible category. -/
def tateNormalizedCMOrdinaryDisconnectedPresheaf (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) : DisBasesᵒᵖ ⥤ Type 1 where
  obj X := DisFamily X.unop U hU
  map f := ↾(pull f.unop U hU)
  map_id X := by
    ext x
    exact tateNormalizedCMOrdinaryDisconnectedPullback_id D C P dualityNaturality
      polarizationStability compatibility h htor X.unop U hU x
  map_comp f g := by
    ext x
    exact (tateNormalizedCMOrdinaryDisconnectedPullback_comp D C P dualityNaturality
      polarizationStability compatibility h htor f.unop g.unop U hU x).symm

local notation "presheaf" => tateNormalizedCMOrdinaryDisconnectedPresheaf D C P
  dualityNaturality polarizationStability compatibility h htor

/-- The identity on actual models gives an unconditional natural isomorphism
between ordinary and unchanged normalized presheaves at this fixed level. -/
def tateNormalizedCMOrdinaryDisconnectedNormalizedIso (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    presheaf U hU ≅ NPresheaf U :=
  NatIso.ofComponents (fun X => (componentwiseEquiv X.unop U hU).toIso) (by
    intro X Y f
    ext x
    exact tateNormalizedCMOrdinaryComponentwiseEquiv_pullback D C P dualityNaturality
      polarizationStability compatibility h htor f.unop U hU x)

/-- The ordinary presheaf returns the identical original CM classes naturally. -/
def tateNormalizedCMOrdinaryDisconnectedForget (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :=
  (tateNormalizedCMOrdinaryDisconnectedNormalizedIso D C P dualityNaturality
    polarizationStability compatibility h htor U hU).hom ≫
      tateNormalizedCMDisconnectedForget D C P dualityNaturality
        polarizationStability compatibility h htor U

/-- The empty base has the unique empty product of ordinary families. -/
abbrev tateNormalizedCMOrdinaryComponentwiseEmptyUnique (X : DisBases)
    [IsEmpty X.obj.left] (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    Unique (DisFamily X U hU) := by
  letI := componentIndex_isEmpty X.obj.left
  exact { default := fun c => isEmptyElim c, uniq := fun x => funext (fun c => isEmptyElim c) }

section Existence

variable (fibreAmple : ProperFibreAmpleAffineOpenStatement.{0})
  (realize : Tate.CommensurableInvariantLatticeRealizationStatement.{0})

/-- Under the explicit generic normalization prerequisites, ordinary actual
models represent the same presheaf values as the original rational CM classes. -/
def tateNormalizedCMOrdinaryDisconnectedIso (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :=
  tateNormalizedCMOrdinaryDisconnectedNormalizedIso D C P dualityNaturality
    polarizationStability compatibility h htor U hU ≪≫
      tateNormalizedCMDisconnectedIso D C P dualityNaturality polarizationStability
        compatibility h htor fibreAmple realize U hU

/-- The full-category natural comparison's forward map is literal forgetting. -/
@[simp] theorem tateNormalizedCMOrdinaryDisconnectedIso_hom (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    (tateNormalizedCMOrdinaryDisconnectedIso D C P dualityNaturality polarizationStability
      compatibility h htor fibreAmple realize U hU).hom =
      tateNormalizedCMOrdinaryDisconnectedForget D C P dualityNaturality
        polarizationStability compatibility h htor U hU := rfl

end Existence

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
