import Langlands.Shimura.PEL.HarrisIntegralCMLevelBaseChange

/-! # Base naturality of actual integral Harris normalized classes -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.AbelianScheme Langlands.AlgebraicGeometry.Picard
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.GroupScheme.Tate (Index)

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra

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
    {S : Scheme.{0}} (B : Langlands.AbelianScheme S) (W : DualWitness B)
    (lam : B ⟶ W.dual P)
    {T T' : Over S} [QuasiSeparatedSpace T.left] [QuasiSeparatedSpace T'.left]
    (f : T' ⟶ T)
    (a : D.harrisHodgePELIntegralOrder C →+*
      CategoryTheory.End ((AbelianScheme.baseChange T.hom).obj B))

local notation "aD" => (relativeEndRestrict B f).comp a

variable
    (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    {Ω : Type} [Field Ω] (t : Spec (.of Ω) ⟶ T'.left)
    (ht : ∀ Y : Cover T'.left, Finite (Fiber t Y))
    (hs : ∀ Y : Cover T.left, Finite (Fiber (t ≫ f.left) Y))
    (htor : TorsionFiniteEtaleStatement.{0})
    (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    (huD : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T'.left, ⊤)))
    [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμetT : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]
    [hμfinD : ∀ k : Index (fun _ => True), IsFinite (mu T'.left k.val).X.hom]
    [hμetD : ∀ k : Index (fun _ => True), Etale (mu T'.left k.val).X.hom]

local notation "duals" => harrisIntegralCMLevelPullbackDualData D C P f
local notation "restriction" => harrisIntegralCMFullActionLevelRestriction
  D C P B W lam f a compatibility h t ht hs htor huT huD

variable (p : S ⟶ Spec (.of F)) (hLam : W.IsPolarization P lam)
    (ha : harrisIntegralCMFullActionCondition D C P p B W lam T a)
    (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
    (addD : PositivePairAdditivity D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      (S := T'.left))

local notation "haD" => harrisIntegralCMFullActionCondition_restrict D C P p B W lam f a ha
variable
    (lieT : LieBaseChangeNaturalityStatement T.left)
    (addT : PositivePairAdditivity D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      (S := T.left))

local notation "toOriginalT" => harrisIntegralCMFullActionLevelOriginalClassNatTrans
  D C P p B W lam hLam T a ha compatibility h htor huT addT
local notation "toOriginalD" => harrisIntegralCMFullActionLevelOriginalClassNatTrans
  D C P p B W lam hLam T' aD haD compatibility h htor huD addD
local notation "baseTriangle" => show f.left ≫ (T.hom ≫ p) = T'.hom ≫ p by
  rw [← Category.assoc, Over.w f]
local notation "pullClassWith" => HarrisTaylorCMWeilLevel.classTowerBaseChangeAlong
  D C P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability P.square P.universality dualityNaturality
  P.polarizationBaseChange compatibility h htor f.left (T.hom ≫ p) (T'.hom ≫ p)
  (t ≫ f.left) t baseTriangle rfl hs ht lieT huT huD

local notation "pullClass" => pullClassWith duals addT addD

/-- Restrict a raw integral Harris orbit and take its original normalized CM class. -/
def harrisIntegralCMFullActionLevelOriginalClassRestriction
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n) :=
  Functor.whiskerRight restriction uliftFunctor.{1} ≫ toOriginalD hdim t ht

local notation "restrictClass" => harrisIntegralCMFullActionLevelOriginalClassRestriction
  D C P B W lam f a compatibility h t ht hs htor huT huD p hLam ha addD

/-- Passing to the unchanged normalized CM class commutes with actual restriction,
including the equality transport of the two displayed structural maps. -/
theorem harrisIntegralCMFullActionLevelOriginalClassNatTrans_baseChange
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n) :
    restrictClass hdim =
      toOriginalT hdim (t ≫ f.left) hs ≫ pullClass := by
  let := auxiliaryStarRing D C
  unfold harrisIntegralCMFullActionLevelOriginalClassRestriction
  rw [HarrisTaylorCMWeilLevel.classTowerBaseChangeAlong_eq
    D C P.preservation P.composition P.unitCoherence P.associativity P.comparison
    P.symmetry P.stability P.square P.universality dualityNaturality
    P.polarizationBaseChange compatibility h htor f.left (T.hom ≫ p) (T'.hom ≫ p)
    (t ≫ f.left) t baseTriangle rfl hs ht lieT huT huD duals addT addD hs]
  simp only [HarrisTaylorCMWeilLevel.classTowerPresentationEq_refl,
    Category.id_comp]
  ext U q
  apply Subtype.ext
  apply Subtype.ext
  simp only [NatTrans.comp_app, types_comp, TypeCat.Fun.toFun_apply,
    Function.comp_apply, TypeCat.ofHom_apply,
    harrisIntegralCMFullActionLevelOriginalClassNatTrans,
    HarrisTaylorCMWeilLevel.classTowerPresentationEq_app,
    HarrisTaylorCMWeilLevel.classPresentationEq_val_val,
    HarrisTaylorCMWeilLevel.classTowerBaseChange,
    HarrisTaylorCMWeilLevel.classBaseChange_val_val,
    HarrisNumericalWeilLevel.classBaseChange_val, harrisClassBaseChange_val,
    ambientClassPointEq]
  exact Quotient.sound
    (harrisIntegralCMFullActionLevelRestriction_related D C P B W lam f a
      compatibility h t ht hs htor huT huD p hLam ha dualityNaturality addD U q.down)

/-- The normalized-class square is independent of the constrained pulled dual data. -/
theorem harrisIntegralCMFullActionLevelOriginalClassNatTrans_baseChange_dualData
    (dualData : ∀ X : PositivePolarizedAction D C P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
      P.universality (S := T.left),
      PositivePullbackDualData D C P.preservation P.composition P.unitCoherence
        P.associativity P.comparison P.symmetry P.stability P.square
        P.universality f.left X)
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n) :
    restrictClass hdim =
      toOriginalT hdim (t ≫ f.left) hs ≫ pullClassWith dualData addT addD := by
  rw [← HarrisTaylorCMWeilLevel.classTowerBaseChangeAlong_dualData
    D C P.preservation P.composition P.unitCoherence P.associativity P.comparison
    P.symmetry P.stability P.square P.universality dualityNaturality
    P.polarizationBaseChange compatibility h htor f.left (T.hom ≫ p) (T'.hom ≫ p)
    (t ≫ f.left) t baseTriangle rfl hs ht lieT huT huD duals addT addD dualData]
  exact harrisIntegralCMFullActionLevelOriginalClassNatTrans_baseChange
    D C P B W lam f a compatibility h t ht hs htor huT huD p hLam ha
    dualityNaturality addD lieT addT hdim

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
