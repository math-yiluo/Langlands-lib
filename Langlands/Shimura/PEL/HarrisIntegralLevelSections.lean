import Langlands.Shimura.PEL.HarrisIntegralFrameReductionMonodromy
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricContinuousActionEquivalenceProof
import Langlands.AbelianScheme.Tate.TestScheme
import Mathlib.CategoryTheory.Action.Concrete

/-! # Global finite torsion sections from an invariant normalized Harris orbit -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj FintypeCatDiscrete

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (P : Prerequisites.{0})
  {S : Scheme.{0}} [ConnectedSpace S] [IsLocallyNoetherian S]
  {Ω : Type} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))

local notation "PObj" =>
  letI := auxiliaryStarRing D C
  PositivePolarizedAction D C P.preservation P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability P.square P.universality (S := S)
local notation:max "BOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).actionObj.abelianScheme
local notation:max "GlobalTorsion" X:max m:max =>
  GroupScheme.Tate.Level (BOf X).toGrp (Over.mk (𝟙 S)) (m : Index (fun _ => True)).val
local notation:max "FT" X:max m:max => harrisIntegralFixedTorsion D C P s hs htor hu X m
local notation "atPoint" => (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S))
local notation:max "restrictLevel" X:max m:max =>
  GroupScheme.Tate.levelRestrict (BOf X).toGrp atPoint (m : Index (fun _ => True)).val

/-- Restriction of global finite torsion sections identifies them with the
monodromy-fixed finite torsion of this Harris datum at the geometric point. -/
def harrisIntegralGlobalTorsionEquiv (X : PObj) (m : Index (fun _ => True)) :
    GlobalTorsion X m ≃+ FT X m := by
  let B := BOf X
  let F := continuousActionFunctor s hs
  let _ : F.IsEquivalence := geometricContinuousActionEquivalence s hs
  let Y : Cover S := cover (𝟙 S)
  let Z : Cover S := Tate.torsionCover htor B m.val m.property.1 (hu m)
  let a : Fiber s Y := atPoint
  have ha (x : Fiber s Y) : x = a := Over.OverMorphism.ext (by
    change x.left = s
    have hx := x.w
    change x.left ≫ 𝟙 S = s at hx
    exact (Category.comp_id x.left).symm.trans hx)
  let kS := GroupScheme.Tate.kernelLevelEquiv B.toGrp (Over.mk (𝟙 S)) m.val
  let ks := GroupScheme.Tate.kernelLevelEquiv B.toGrp (Over.mk s) m.val
  have he (f : Y ⟶ Z) :
      restrictLevel X m (kS (Additive.ofMul f.hom)) =
        ks (Additive.ofMul (a ≫ f.hom)) :=
    GroupScheme.Tate.levelRestrict_kernelLevelEquiv B.toGrp a m.val (Additive.ofMul f.hom)
  have hfixed (v : GlobalTorsion X m) : restrictLevel X m v ∈ FT X m := by
    obtain ⟨w, rfl⟩ := kS.surjective v
    let f : Y ⟶ Z := ObjectProperty.homMk w.toMul
    intro gamma
    have hv : gamma.hom.app Z (a ≫ f.hom) = a ≫ f.hom :=
      (smul_naturality s hs f gamma a).trans (congrArg (fun y : Fiber s Y => y ≫ f.hom)
        (ha (gamma • a)))
    change Tate.levelMonodromy s hs htor B m.val m.property.1 (hu m) gamma
      (restrictLevel X m (kS w)) = restrictLevel X m (kS w)
    rw [show restrictLevel X m (kS w) = ks (Additive.ofMul (a ≫ f.hom)) from he f]
    exact (Tate.levelMonodromy_kernel s hs htor B m.val m.property.1 (hu m) gamma _).trans
      (congrArg (fun z : Fiber s Z => ks (Additive.ofMul z)) hv)
  let r := (restrictLevel X m).codRestrict (FT X m) hfixed
  refine AddEquiv.ofBijective r ⟨?_, ?_⟩
  · intro v w hvw
    obtain ⟨v', rfl⟩ := kS.surjective v
    obtain ⟨w', rfl⟩ := kS.surjective w
    let f : Y ⟶ Z := ObjectProperty.homMk v'.toMul
    let g : Y ⟶ Z := ObjectProperty.homMk w'.toMul
    have hvw' : restrictLevel X m (kS v') = restrictLevel X m (kS w') :=
      congrArg Subtype.val hvw
    have hfg : a ≫ f.hom = a ≫ g.hom := congrArg Additive.toMul
      (ks.injective ((he f).symm.trans (hvw'.trans (he g))))
    have hfg' : f = g := by
      apply F.map_injective
      apply ObjectProperty.hom_ext
      apply Action.hom_ext
      apply ConcreteCategory.hom_ext
      intro x
      change x ≫ f.hom = x ≫ g.hom
      rw [ha x, hfg]
    exact congrArg (fun f : Y ⟶ Z => kS (Additive.ofMul f.hom)) hfg'
  · intro t
    let z : Fiber s Z := (ks.symm t.val).toMul
    have hz (gamma : FundamentalGroup s hs) : gamma • z = z := by
      have ht : Tate.levelMonodromy s hs htor B m.val m.property.1 (hu m) gamma t.val = t.val :=
        t.property gamma
      change gamma.hom.app Z z = z
      exact (Tate.kernelPoint_levelMonodromy s hs htor B m.val m.property.1 (hu m) gamma
        t.val).symm.trans (congrArg (fun v => (ks.symm v).toMul) ht)
    let k : F.obj Y ⟶ F.obj Z := ObjectProperty.homMk
      { hom := FintypeCat.homMk (fun _ => z)
        comm := fun gamma => ConcreteCategory.hom_ext _ _ (fun _ => (hz gamma).symm) }
    let f := F.preimage k
    have hf : a ≫ f.hom = z := ConcreteCategory.congr_hom (F.map_preimage k) a
    refine ⟨kS (Additive.ofMul f.hom), Subtype.ext ?_⟩
    exact (he f).trans ((congrArg (fun z : Fiber s Z => ks (Additive.ofMul z)) hf).trans
      (ks.apply_symm_apply t.val))

local notation "globalEquiv" => harrisIntegralGlobalTorsionEquiv D C P s hs htor hu

@[simp] theorem harrisIntegralGlobalTorsionEquiv_apply (X : PObj) (m : Index (fun _ => True))
    (t : GlobalTorsion X m) : (globalEquiv X m t).val = restrictLevel X m t := rfl

@[simp] theorem harrisIntegralGlobalTorsionEquiv_symm_restrict
    (X : PObj) (m : Index (fun _ => True)) (t : FT X m) :
    restrictLevel X m ((globalEquiv X m).symm t) = t.val :=
  congrArg Subtype.val ((globalEquiv X m).apply_symm_apply t)

variable [QuasiSeparatedSpace S] (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]

local notation "ULevel" => FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)
local notation "Cong" => harrisIntegralAdeleCongruence D C
local notation:max "tower" X:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.levelTower P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    compatibility h A (D.harrisHodgePELForm C) s hs htor hu X
local notation "LevelNormalized" => HarrisIntegralLevelCondition D C P compatibility h s hs htor hu
local notation "orbitRed" => harrisIntegralLevelReduction D C P compatibility h s hs htor hu

/-- The actual global finite torsion sections obtained by reducing an existing
normalized invariant orbit at a level contained in principal congruence. -/
def harrisIntegralLevelSections (X : PObj) (m : Index (fun _ => True))
    (U : ULevel) (hU : U.toSubgroup ≤ Cong m.val) (x : (tower X).obj U)
    (hx : LevelNormalized X U x) : HarrisIntegralSourceMod D C m.val ≃+ GlobalTorsion X m := by
  let eta := Classical.choose hx
  have hn := (Classical.choose_spec hx).1
  have he := (Classical.choose_spec hx).2
  let r := orbitRed X m U hU x hx
  let e := harrisIntegralFrameTorsionEquiv D C P compatibility h s hu X m eta hn
  have ht (q : HarrisIntegralSourceMod D C m.val) : (r q).val = e q :=
    harrisIntegralLevelReduction_apply D C P compatibility h s hs htor hu X m U hU x hx eta hn he q
  have hb : Function.Bijective r := ⟨by
    intro a b hab
    exact e.injective ((ht a).symm.trans ((congrArg Subtype.val hab).trans (ht b))), by
    intro z
    obtain ⟨q, hq⟩ := e.surjective z.val
    exact ⟨q, Subtype.ext ((ht q).trans hq)⟩⟩
  exact (AddEquiv.ofBijective r hb).trans (globalEquiv X m).symm

/-- At the reference geometric point, the global section evaluates to the
reduction of the existing normalized invariant orbit. -/
@[simp] theorem harrisIntegralLevelSections_restrict (X : PObj) (m : Index (fun _ => True))
    (U : ULevel) (hU : U.toSubgroup ≤ Cong m.val) (x : (tower X).obj U)
    (hx : LevelNormalized X U x) (q : HarrisIntegralSourceMod D C m.val) :
    restrictLevel X m
      (harrisIntegralLevelSections D C P s hs htor hu compatibility h X m U hU x hx q) =
        (orbitRed X m U hU x hx q).val :=
  harrisIntegralGlobalTorsionEquiv_symm_restrict D C P s hs htor hu X m _

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
