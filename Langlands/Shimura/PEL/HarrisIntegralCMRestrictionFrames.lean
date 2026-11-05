import Langlands.Shimura.PEL.HarrisIntegralCMRestrictionComposition
import Langlands.Shimura.PEL.HarrisIntegralCMLevelMonodromy
import Langlands.Shimura.PEL.HarrisIntegralCMLevelOrbitCoverLevels
import Langlands.AbelianScheme.Tate.WeilFrameBaseChangeCoherence

/-! # Actual frame transport for Harris test restriction -/

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

section ModuleEquality

variable {R₀ K₀ X₀ Y₀ Z₀ : Type}
    [CommRing R₀] [Ring K₀]
    [AddCommGroup X₀] [Module R₀ X₀] [Module K₀ X₀]
    [AddCommGroup Y₀] [Module R₀ Y₀]
    [AddCommGroup Z₀] [Module R₀ Z₀]

private def formIsoModuleEqMap (m m' : Module K₀ Y₀) (hm : m = m')
    (ψ : X₀ →ₗ[R₀] X₀ →ₗ[R₀] R₀) (φ : Y₀ →ₗ[R₀] Y₀ →ₗ[R₀] Z₀)
    (eta : letI := m; FormIso K₀ ψ φ) : letI := m'; FormIso K₀ ψ φ := by
  letI := m'
  exact ⟨{ toFun := fun x => eta.1 x
           invFun := fun x => eta.1.symm x
           left_inv := by subst m'; exact eta.1.left_inv
           right_inv := by subst m'; exact eta.1.right_inv
           map_add' := eta.1.map_add'
           map_smul' := by subst m'; exact eta.1.map_smul' }, eta.2⟩

private def formIsoModuleEq (m m' : Module K₀ Y₀) (hm : m = m')
    (ψ : X₀ →ₗ[R₀] X₀ →ₗ[R₀] R₀) (φ : Y₀ →ₗ[R₀] Y₀ →ₗ[R₀] Z₀) :
    (letI := m; FormIso K₀ ψ φ) ≃ (letI := m'; FormIso K₀ ψ φ) where
  toFun := formIsoModuleEqMap m m' hm ψ φ
  invFun := formIsoModuleEqMap m' m hm.symm ψ φ
  left_inv eta := by
    apply Subtype.ext
    exact LinearEquiv.ext (fun _ => rfl)
  right_inv eta := by
    apply Subtype.ext
    exact LinearEquiv.ext (fun _ => rfl)

end ModuleEquality

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


local notation "BT" => (AbelianScheme.baseChange T.hom).obj B
local notation "BD" => (AbelianScheme.baseChange T'.hom).obj B
local notation "BC" => (AbelianScheme.baseChange f.left).obj BT
local notation "WT" => W.pullback P T.hom
local notation "WD" => W.pullback P T'.hom
local notation "WC" => (WT).pullback P f.left
local notation "lamT" => W.pullbackMap P T.hom WT lam
local notation "lamD" => W.pullbackMap P T'.hom WD lam
local notation "lamC" => (WT).pullbackMap P f.left WC lamT
local notation "aD" => (relativeEndRestrict B f).comp a
local notation "iT" => D.harrisHodgePELRationalAction C BT a
local notation "iD" => D.harrisHodgePELRationalAction C BD aD
local notation "iC" => (rationalBaseChangeEnd f.left BT).comp iT
local notation "e" => relativeIntegralActionRationalComparisonIso B
  (D.harrisHodgePELIntegralBasis C) f a
local notation "addDC" => relativeDualSchemeMapAdditivity P.preservation P.stability
  T'.left BD BC (WD).hasDual (WC).hasDual

variable (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    {Ω : Type} [Field Ω] (t : Spec (.of Ω) ⟶ T'.left)

local notation "FrameD" => harrisIntegralCMWeilFrame
  D C P B W lam T' aD compatibility h t
local notation "FrameT" => harrisIntegralCMWeilFrame
  D C P B W lam T a compatibility h (t ≫ f.left)
local notation "H" => ScalarExtensionSimilitudes A A
  (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)
local notation "FrameAt" T₀:max a₀:max s₀:max => harrisIntegralCMWeilFrame
  D C P B W lam T₀ a₀ compatibility h s₀
local notation "rightAt" T₀:max a₀:max s₀:max =>
  Tate.weilAdelicFrameRightAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability
    (W.pullback P (T₀).hom).hasDual (W.pullback P (T₀).hom).geometry
    (W.pullback P (T₀).hom).inverseBundle (W.pullback P (T₀).hom).evaluation
    compatibility (W.pullbackMap P (T₀).hom (W.pullback P (T₀).hom) lam) h
    (D.harrisHodgePELRationalAction C ((AbelianScheme.baseChange (T₀).hom).obj B) a₀)
    A (D.harrisHodgePELForm C) s₀
local notation "RawAt" T₀:max a₀:max s₀:max U₀:max =>
  @RightOrbit H _ (FrameAt T₀ a₀ s₀) (rightAt T₀ a₀ s₀) U₀
local notation "frameCompare" => Tate.weilAdelicFrameIsogeny
  P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability (WD).hasDual (WC).hasDual (WD).geometry (WC).geometry
  (WD).inverseBundle (WD).evaluation (WC).inverseBundle (WC).evaluation
  addDC lamD lamC compatibility rationalWeilFunctoriality h iD iC A
  (D.harrisHodgePELForm C) t 1 (RationalAlgebraAction.underlyingIso e)
  (RationalAlgebraAction.intertwines (e).hom)
  (harrisIntegralCMFullActionRestriction_multiple D C P B W lam f a)
local notation "frameBC" => Tate.weilAdelicFrameBaseChange f.left BT P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.universality (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation
  (WC).hasDual (WC).geometry (WC).inverseBundle (WC).evaluation compatibility lamT
  h iT A (D.harrisHodgePELForm C) t

/-- Evaluate a frame on the direct restricted action in the original family. -/
def harrisIntegralCMRestrictionFrameEquiv : FrameD ≃ FrameT :=
  (frameCompare).trans frameBC

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The frame comparison is the actual family homomorphism followed by actual
rational Tate base change. -/
theorem harrisIntegralCMRestrictionFrameEquiv_apply (eta : FrameD)
    (x : (Global.FiniteAdeles ℚ) ⊗[ℚ] A) :
    (harrisIntegralCMRestrictionFrameEquiv D C P B W lam f a compatibility h t eta).1 x =
      Tate.rationalBaseChange f.left BT (Over.mk t) (fun _ => True)
        (Tate.rationalHomMap (Over.mk t) (fun _ => True)
          (homToHom0 (relativeBaseChangeComparisonIso B f).hom) (eta.1 x)) := rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Actual restriction of frames commutes with right precomposition. -/
theorem harrisIntegralCMRestrictionFrameEquiv_right :
    letI := rightAt T' aD t
    letI := rightAt T a (t ≫ f.left)
    ∀ (eta : FrameD) (z : H),
      harrisIntegralCMRestrictionFrameEquiv D C P B W lam f a compatibility h t
          (right eta z) =
        right (harrisIntegralCMRestrictionFrameEquiv D C P B W lam f a
          compatibility h t eta) z := by
  let := rightAt T' aD t
  let := rightAt T a (t ≫ f.left)
  intro eta z
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rfl

/-- The actual frame comparison descends to every right subgroup orbit set. -/
def harrisIntegralCMRestrictionRawEquiv (U : Subgroup H) :
    letI := rightAt T' aD t
    letI := rightAt T a (t ≫ f.left)
    RightOrbit FrameD U ≃ RightOrbit FrameT U := by
  let := rightAt T' aD t
  let := rightAt T a (t ≫ f.left)
  exact RightOrbit.equiv U
    (harrisIntegralCMRestrictionFrameEquiv D C P B W lam f a compatibility h t)
    (harrisIntegralCMRestrictionFrameEquiv_right D C P B W lam f a compatibility h t)

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- On a representative, raw evaluation is the actual frame comparison. -/
theorem harrisIntegralCMRestrictionRawEquiv_mk (U : Subgroup H) :
    letI := rightAt T' aD t
    letI := rightAt T a (t ≫ f.left)
    ∀ eta : FrameD,
      harrisIntegralCMRestrictionRawEquiv D C P B W lam f a compatibility h t U
          (RightOrbit.mk U eta) =
        RightOrbit.mk U
          (harrisIntegralCMRestrictionFrameEquiv D C P B W lam f a
            compatibility h t eta) := by
  let := rightAt T' aD t
  let := rightAt T a (t ≫ f.left)
  intro eta
  rfl

/-- Equality of the given integral actions transports their actual Weil frames. -/
def harrisIntegralCMWeilFrameActionEq
    (a' : D.harrisHodgePELIntegralOrder C →+* CategoryTheory.End BT) (ha : a = a')
    (s : Spec (.of Ω) ⟶ T.left) :
    harrisIntegralCMWeilFrame D C P B W lam T a compatibility h s ≃
      harrisIntegralCMWeilFrame D C P B W lam T a' compatibility h s := by
  letI := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
  letI := GroupScheme.Tate.finiteAdeleModule (BT).toGrp (Over.mk s) (fun _ => True) h
  letI := TateTwist.Divisibility.finiteAdeleModule Γ((Over.mk s).left, ⊤)
    (fun _ => True) h
  exact formIsoModuleEq
    (Tate.finiteAdeleAlgebraModule BT (Over.mk s) (fun _ => True) h
      (D.harrisHodgePELRationalAction C BT a))
    (Tate.finiteAdeleAlgebraModule BT (Over.mk s) (fun _ => True) h
      (D.harrisHodgePELRationalAction C BT a'))
    (congrArg (fun b => Tate.finiteAdeleAlgebraModule BT (Over.mk s) (fun _ => True) h
      (D.harrisHodgePELRationalAction C BT b)) ha) _ _

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Action equality leaves each actual rational Tate value unchanged. -/
theorem harrisIntegralCMWeilFrameActionEq_apply
    (a' : D.harrisHodgePELIntegralOrder C →+* CategoryTheory.End BT) (ha : a = a')
    (s : Spec (.of Ω) ⟶ T.left)
    (eta : harrisIntegralCMWeilFrame D C P B W lam T a compatibility h s)
    (x : (Global.FiniteAdeles ℚ) ⊗[ℚ] A) :
    (harrisIntegralCMWeilFrameActionEq D C P B W lam a compatibility h a' ha s eta).1 x =
      eta.1 x := rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Equality of actions also preserves right precomposition. -/
theorem harrisIntegralCMWeilFrameActionEq_right
    (a' : D.harrisHodgePELIntegralOrder C →+* CategoryTheory.End BT) (ha : a = a')
    (s : Spec (.of Ω) ⟶ T.left) :
    letI := rightAt T a s
    letI := rightAt T a' s
    ∀ (eta : FrameAt T a s) (z : H),
      harrisIntegralCMWeilFrameActionEq D C P B W lam a compatibility h a' ha s
          (right eta z) =
        right (harrisIntegralCMWeilFrameActionEq D C P B W lam a compatibility h
          a' ha s eta) z := by
  let := rightAt T a s
  let := rightAt T a' s
  intro eta z
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rfl

/-- Action equality induces an equivalence of actual right orbit classes. -/
def harrisIntegralCMWeilRawActionEq
    (a' : D.harrisHodgePELIntegralOrder C →+* CategoryTheory.End BT) (ha : a = a')
    (s : Spec (.of Ω) ⟶ T.left) (U : Subgroup H) :
    letI := rightAt T a s
    letI := rightAt T a' s
    RightOrbit (FrameAt T a s) U ≃ RightOrbit (FrameAt T a' s) U := by
  let := rightAt T a s
  let := rightAt T a' s
  exact RightOrbit.equiv U
    (harrisIntegralCMWeilFrameActionEq D C P B W lam a compatibility h a' ha s)
    (harrisIntegralCMWeilFrameActionEq_right D C P B W lam a compatibility h a' ha s)

section Composition

variable {T'' : Over S} [QuasiSeparatedSpace T''.left] (g : T'' ⟶ T')

include D C a in
omit [IsCMField F] [IsScalarTower ℚ F A]
  [QuasiSeparatedSpace T.left] [QuasiSeparatedSpace T'.left]
  [QuasiSeparatedSpace T''.left] P W lam compatibility h t in
private theorem restriction_tate_comp (Q : Over T''.left) (K : ℕ → Prop)
    (x : Tate.Rational ((AbelianScheme.baseChange T''.hom).obj B) Q K) :
    Tate.rationalBaseChange f.left BT ((Over.map g.left).obj Q) K
        (Tate.rationalHomMap ((Over.map g.left).obj Q) K
          (homToHom0 (relativeBaseChangeComparisonIso B f).hom)
          (Tate.rationalBaseChange g.left BD Q K
            (Tate.rationalHomMap Q K
              (homToHom0 (relativeBaseChangeComparisonIso B g).hom) x))) =
      GroupScheme.Tate.rationalTestRestrict (BT).toGrp K
        ((Over.mapComp g.left f.left).inv.app Q)
        (Tate.rationalBaseChange (g ≫ f).left BT Q K
          (Tate.rationalHomMap Q K
            (homToHom0 (relativeBaseChangeComparisonIso B (g ≫ f)).hom) x)) := by
  have cmp := harrisIntegralCMRestrictionRationalComparison_comp D C B f g a
  change Rationalization.comp _ _ _
      (homToHom0 (relativeBaseChangeComparisonIso B (g ≫ f)).hom)
      (homToHom0 (AbelianScheme.baseChangeCompIso f.left g.left BT).hom) =
    Rationalization.comp _ _ _ (homToHom0 (relativeBaseChangeComparisonIso B g).hom)
      (rationalBaseChangeHom g.left
        (homToHom0 (relativeBaseChangeComparisonIso B f).hom)) at cmp
  have mapcmp := LinearMap.congr_fun (congrArg (Tate.rationalHomMap Q K) cmp) x
  simp only [Tate.rationalHomMap_comp, LinearMap.comp_apply] at mapcmp
  rw [← Tate.rationalBaseChange_homMap, ← mapcmp]
  have bc := GroupScheme.Tate.rationalBaseChange_base_comp (BT).toGrp
    f.left g.left Q K
    (Tate.rationalHomMap Q K
      (homToHom0 (AbelianScheme.baseChangeCompIso f.left g.left BT).hom)
      (Tate.rationalHomMap Q K
        (homToHom0 (relativeBaseChangeComparisonIso B (g ≫ f)).hom) x))
  simp only [homToHom0, Tate.rationalHomMap_ofHom] at bc
  change _ = GroupScheme.Tate.rationalTestRestrict (BT).toGrp K
    ((Over.mapComp g.left f.left).inv.app Q)
    (Langlands.AbelianScheme.Tate.rationalBaseChange (g ≫ f).left BT Q K
      (Langlands.AbelianScheme.Tate.rationalMap Q K
        (AbelianScheme.baseChangeCompIso f.left g.left BT).inv
        (Langlands.AbelianScheme.Tate.rationalMap Q K
          (AbelianScheme.baseChangeCompIso f.left g.left BT).hom
          (Langlands.AbelianScheme.Tate.rationalMap Q K
            (relativeBaseChangeComparisonIso B (g ≫ f)).hom x)))) at bc
  simp only [← LinearMap.comp_apply, ← Langlands.AbelianScheme.Tate.rationalMap_comp,
    Iso.hom_inv_id, Langlands.AbelianScheme.Tate.rationalMap_id, LinearMap.id_apply] at bc
  simp only [homToHom0, Tate.rationalHomMap_ofHom]
  convert bc using 1 <;> rfl

/-- The literal action composition law identifies direct and successive
restricted frames on the original family over the final test. -/
def harrisIntegralCMRestrictionFrameCompEquiv (u : Spec (.of Ω) ⟶ T''.left) :
    harrisIntegralCMWeilFrame D C P B W lam T''
        ((relativeEndRestrict B (g ≫ f)).comp a) compatibility h u ≃
      harrisIntegralCMWeilFrame D C P B W lam T''
        ((relativeEndRestrict B g).comp aD) compatibility h u :=
  harrisIntegralCMWeilFrameActionEq D C P B W lam
    ((relativeEndRestrict B (g ≫ f)).comp a) compatibility h
    ((relativeEndRestrict B g).comp aD)
    (harrisIntegralCMRestrictionAction_comp D C B f g a).symm u

omit [IsCMField F] [IsScalarTower ℚ F A]
  [QuasiSeparatedSpace T.left] [QuasiSeparatedSpace T'.left] in
/-- The comparison of restricted actions preserves every actual frame value. -/
theorem harrisIntegralCMRestrictionFrameCompEquiv_apply
    (u : Spec (.of Ω) ⟶ T''.left)
    (eta : harrisIntegralCMWeilFrame D C P B W lam T''
      ((relativeEndRestrict B (g ≫ f)).comp a) compatibility h u)
    (x : (Global.FiniteAdeles ℚ) ⊗[ℚ] A) :
    (harrisIntegralCMRestrictionFrameCompEquiv D C P B W lam f a compatibility h
      g u eta).1 x = eta.1 x := rfl

/-- The literal action composition law identifies raw classes of direct and
successively restricted frames. -/
def harrisIntegralCMRestrictionRawCompEquiv
    (u : Spec (.of Ω) ⟶ T''.left) (U : Subgroup H) :
    RawAt T'' ((relativeEndRestrict B (g ≫ f)).comp a) u U ≃
      RawAt T'' ((relativeEndRestrict B g).comp aD) u U :=
  harrisIntegralCMWeilRawActionEq D C P B W lam
    ((relativeEndRestrict B (g ≫ f)).comp a) compatibility h
    ((relativeEndRestrict B g).comp aD)
    (harrisIntegralCMRestrictionAction_comp D C B f g a).symm u U

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Successive restriction evaluates the same actual frame as composite
restriction, with the canonical associativity identification of its point. -/
theorem harrisIntegralCMRestrictionFrame_comp
    (u : Spec (.of Ω) ⟶ T''.left)
    (eta : harrisIntegralCMWeilFrame D C P B W lam T''
      ((relativeEndRestrict B (g ≫ f)).comp a) compatibility h u) :
    harrisIntegralCMRestrictionFrameEquiv D C P B W lam f a compatibility h
        (u ≫ g.left)
        (harrisIntegralCMRestrictionFrameEquiv D C P B W lam g aD compatibility h u
          (harrisIntegralCMRestrictionFrameCompEquiv D C P B W lam f a
            compatibility h g u eta)) =
      Tate.weilAdelicFramePointEq P.preservation P.composition P.unitCoherence
        P.associativity P.comparison P.symmetry P.stability (WT).hasDual
        (WT).geometry (WT).inverseBundle (WT).evaluation compatibility lamT h iT A
        (D.harrisHodgePELForm C) (Category.assoc u g.left f.left).symm
        (harrisIntegralCMRestrictionFrameEquiv D C P B W lam (g ≫ f) a
          compatibility h u eta) := by
  let := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
  apply Subtype.ext
  rw [Tate.weilAdelicFramePointEq_underlying P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability
    (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation compatibility
    lamT h iT A (D.harrisHodgePELForm C) (Category.assoc u g.left f.left).symm
    ((Over.mapComp g.left f.left).app (Over.mk u)) rfl]
  apply LinearEquiv.ext
  intro x
  simp only [harrisIntegralCMRestrictionFrameEquiv_apply,
    harrisIntegralCMRestrictionFrameCompEquiv_apply, Tate.adelicFrameTestIso_apply]
  convert restriction_tate_comp D C B f a g (Over.mk u) (fun _ => True) (eta.1 x)
    using 1 <;> rfl

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Successive evaluation agrees with composite evaluation on actual raw
classes, with the canonical associativity comparison of the point. -/
theorem harrisIntegralCMRestrictionRaw_comp
    (u : Spec (.of Ω) ⟶ T''.left) (U : Subgroup H) :
    ∀ q : RawAt T'' ((relativeEndRestrict B (g ≫ f)).comp a) u U,
      harrisIntegralCMRestrictionRawEquiv D C P B W lam f a compatibility h
          (u ≫ g.left) U
          (harrisIntegralCMRestrictionRawEquiv D C P B W lam g aD compatibility h u U
            (harrisIntegralCMRestrictionRawCompEquiv D C P B W lam f a
              compatibility h g u U q)) =
        Tate.weilAdelicFrameRightOrbitPointEq P.preservation P.composition
          P.unitCoherence P.associativity P.comparison P.symmetry P.stability
          (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation compatibility
          lamT h iT A (D.harrisHodgePELForm C) (Category.assoc u g.left f.left).symm U
          (harrisIntegralCMRestrictionRawEquiv D C P B W lam (g ≫ f) a
            compatibility h u U q) := by
  let := rightAt T a ((u ≫ g.left) ≫ f.left)
  intro q
  induction q using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U)
      (harrisIntegralCMRestrictionFrame_comp D C P B W lam f a compatibility h g u eta)

end Composition

section OriginalEvaluation

variable
    (ht : ∀ Y : Cover T'.left, Finite (Fiber t Y))
    (hs : ∀ Y : Cover T.left, Finite (Fiber (t ≫ f.left) Y))
    (htor : TorsionFiniteEtaleStatement.{0})
    (huD : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T'.left, ⊤)))
    [hμfinD : ∀ k : Index (fun _ => True), IsFinite (mu T'.left k.val).X.hom]
    [hμetD : ∀ k : Index (fun _ => True), Etale (mu T'.left k.val).X.hom]

local notation "rawD" => harrisIntegralCMFullActionLevelTower
  D C P B W lam T' aD compatibility h t ht htor huD
local notation "rightC" => Tate.weilAdelicFrameRightAction P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  (WC).hasDual (WC).geometry (WC).inverseBundle (WC).evaluation compatibility
  lamC h iC A (D.harrisHodgePELForm C) t
local notation "frameCompareRight" => Tate.weilAdelicFrameIsogeny_right
  P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability (WD).hasDual (WC).hasDual (WD).geometry (WC).geometry
  (WD).inverseBundle (WD).evaluation (WC).inverseBundle (WC).evaluation
  addDC lamD lamC compatibility rationalWeilFunctoriality h iD iC A
  (D.harrisHodgePELForm C) t 1 (RationalAlgebraAction.underlyingIso e)
  (RationalAlgebraAction.intertwines (e).hom)
  (harrisIntegralCMFullActionRestriction_multiple D C P B W lam f a)
local notation "frameBCRight" => Tate.weilAdelicFrameBaseChange_right f.left BT
  P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability P.universality (WT).hasDual (WT).geometry
  (WT).inverseBundle (WT).evaluation (WC).hasDual (WC).geometry
  (WC).inverseBundle (WC).evaluation compatibility lamT h iT A
  (D.harrisHodgePELForm C) t

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The published original raw evaluation is exactly the descended actual
frame comparison applied to the underlying class of the original direct level. -/
theorem harrisIntegralCMRestrictionRawClass_eq_rawEquiv
    (V : HarrisLevel D) (r : (rawD).obj V) :
    harrisIntegralCMRestrictionRawClass D C P B W lam f a compatibility h
        t ht htor huD (t ≫ f.left) rfl hs V r =
      harrisIntegralCMRestrictionRawEquiv D C P B W lam f a compatibility h t
        ((hodgeLevelFunctor D C).obj V).subgroup r.val := by
  let := rightAt T' aD t
  let := rightC
  let := rightAt T a (t ≫ f.left)
  change RightOrbit.map _ frameBC frameBCRight
      (RightOrbit.map _ frameCompare frameCompareRight r.val) =
    RightOrbit.map _ ((frameCompare).trans frameBC)
      (harrisIntegralCMRestrictionFrameEquiv_right D C P B W lam f a compatibility h t)
      r.val
  exact RightOrbit.map_comp _ frameCompare frameBC frameCompareRight frameBCRight r.val

section FixedRestriction

variable
    (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμetT : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]

local notation "rawT" => harrisIntegralCMFullActionLevelTower
  D C P B W lam T a compatibility h (t ≫ f.left) hs htor huT
local notation "restriction" => harrisIntegralCMFullActionLevelRestriction
  D C P B W lam f a compatibility h t ht hs htor huT huD
local notation "compare" => harrisIntegralCMFullActionRestrictionLevelIso
  D C P B W lam f a compatibility h t ht htor huD
local notation "levelBC" => Tate.weilAdelicCompactOpenLevelBaseChange f.left BT
  P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability P.universality (WT).hasDual (WT).geometry
  (WT).inverseBundle (WT).evaluation (WC).hasDual (WC).geometry
  (WC).inverseBundle (WC).evaluation compatibility lamT h iT A
  (D.harrisHodgePELForm C) t ht hs htor huT huD
local notation "orbitBC" => Tate.weilAdelicFrameRightOrbitBaseChange f.left BT
  P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability P.universality (WT).hasDual (WT).geometry
  (WT).inverseBundle (WT).evaluation (WC).hasDual (WC).geometry
  (WC).inverseBundle (WC).evaluation compatibility lamT h iT A
  (D.harrisHodgePELForm C) t

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The published actual level restriction recovers exactly the original
raw class under the descended frame evaluation. -/
theorem harrisIntegralCMFullActionLevelRestriction_rawValue
    (V : HarrisLevel D) (r : (rawT).obj V) :
    harrisIntegralCMRestrictionRawEquiv D C P B W lam f a compatibility h t
        ((hodgeLevelFunctor D C).obj V).subgroup
        ((restriction).app V r).val = r.val := by
  rw [← harrisIntegralCMRestrictionRawClass_eq_rawEquiv
    D C P B W lam f a compatibility h t ht hs htor huD V ((restriction).app V r)]
  let y := (levelBC).app ((hodgeLevelFunctor D C).obj V) r
  change (orbitBC _)
    ((compare).hom.app V ((compare).inv.app V y)).val = r.val
  have he := congrArg (fun k => k y) (NatTrans.congr_app (compare).inv_hom_id V)
  change (compare).hom.app V ((compare).inv.app V y) = y at he
  rw [he]
  exact Equiv.apply_symm_apply (orbitBC _) r.val

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- On underlying raw classes, original level restriction is the inverse
of the actual frame evaluation equivalence. -/
theorem harrisIntegralCMFullActionLevelRestriction_val
    (V : HarrisLevel D) (r : (rawT).obj V) :
    ((restriction).app V r).val =
      (harrisIntegralCMRestrictionRawEquiv D C P B W lam f a compatibility h t
        ((hodgeLevelFunctor D C).obj V).subgroup).symm r.val :=
  (Equiv.eq_symm_apply _).mpr
    (harrisIntegralCMFullActionLevelRestriction_rawValue
      D C P B W lam f a compatibility h t ht hs htor huD huT V r)

end FixedRestriction

end OriginalEvaluation

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
