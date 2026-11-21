import Langlands.Shimura.PEL.HarrisIntegralLevelSections
import Langlands.Shimura.PEL.HarrisIntegralSourceResidues
import Langlands.AbelianScheme.PolarizedFiniteLevel.FullLevel
import Langlands.AbelianScheme.Tate.FiniteTransport
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricPathProof
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof

/-! # Ordered full finite level of an invariant normalized Harris orbit -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

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

local notation "L" => D.harrisHodgePELIntegralLattice C
local notation "gH" => Module.finrank ℚ E * n ^ 2

variable [IsScalarTower ℚ E F] [IsScalarTower ℚ F A]

/-- The actual integer source lattice has rank twice the prescribed Harris genus. -/
theorem harrisIntegralSource_rank : Module.finrank ℤ L = 2 * gH := by
  have hL : Module.finrank ℤ L = Module.finrank ℚ A := by
    let b := (Module.finBasis ℤ L).extendOfIsLattice ℚ
    simpa only [Fintype.card_fin] using (Module.finrank_eq_card_basis b).symm
  rw [hL, ← Module.finrank_mul_finrank ℚ F A, ← Module.finrank_mul_finrank ℚ E F,
    D.dimension, IsQuadraticExtension.finrank_eq_two E F]
  ac_rfl

section Restriction

variable {S : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
  (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ω') ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y)) (ht : ∀ Y : Cover S, Finite (Fiber t Y))
  (htor : TorsionFiniteEtaleStatement.{0}) (B : AbelianScheme S)
  (m : Index (fun _ => True)) (hm : IsUnit (m.val : Γ(S, ⊤)))

local notation:max "pointMap" a:max => (Over.homMk a (by simp) : Over.mk a ⟶ Over.mk (𝟙 S))
local notation:max "restr" a:max => GroupScheme.Tate.levelRestrict B.toGrp (pointMap a) m.val

/-- The path between actual geometric fibre functors carries the value of a
fixed global section at the first point to its value at the second. -/
private theorem levelTransport_restrict_global (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (v : GroupScheme.Tate.Level B.toGrp (Over.mk (𝟙 S)) m.val) :
    Tate.levelTransport htor B m.val m.property.1 hm p (restr s v) = restr t v := by
  let Y : Cover S := cover (𝟙 S)
  let Z : Cover S := Tate.torsionCover htor B m.val m.property.1 hm
  let a : Fiber s Y := pointMap s
  let b : Fiber t Y := pointMap t
  let k := GroupScheme.Tate.kernelLevelEquiv B.toGrp (Over.mk (𝟙 S)) m.val
  obtain ⟨w, rfl⟩ := k.surjective v
  let f : Y ⟶ Z := ObjectProperty.homMk w.toMul
  have hb : p.hom.app Y a = b := Over.OverMorphism.ext (by
    change (p.hom.app Y a : Fiber t Y).left = t
    have hw := (show Fiber t Y from p.hom.app Y a).w
    change (p.hom.app Y a : Fiber t Y).left ≫ 𝟙 S = t at hw
    exact (Category.comp_id _).symm.trans hw)
  have hp : p.hom.app Z (a ≫ f.hom) = b ≫ f.hom :=
    (ConcreteCategory.congr_hom (p.hom.naturality f) a).trans
      (congrArg (fun x : Fiber t Y => x ≫ f.hom) hb)
  rw [GroupScheme.Tate.levelRestrict_kernelLevelEquiv,
    GroupScheme.Tate.levelRestrict_kernelLevelEquiv, Tate.levelTransport_kernel]
  exact congrArg (fun x : Fiber t Z => GroupScheme.Tate.kernelLevelEquiv B.toGrp (Over.mk t)
    m.val (Additive.ofMul x)) hp

end Restriction

variable (P : Prerequisites.{0})
  {S : Scheme.{0}} [QuasiSeparatedSpace S] [ConnectedSpace S] [IsLocallyNoetherian S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]

local notation "PObj" =>
  letI := auxiliaryStarRing D C
  PositivePolarizedAction D C P.preservation P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability P.square P.universality (S := S)
local notation:max "BOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).actionObj.abelianScheme
local notation "ULevel" => FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)
local notation "Cong" => harrisIntegralAdeleCongruence D C
local notation:max "tower" X:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.levelTower P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    compatibility h A (D.harrisHodgePELForm C) s hs htor hu X
local notation "LevelNormalized" => HarrisIntegralLevelCondition D C P compatibility h s hs htor hu

/-- The residue coordinates of the actual source and the global sections of the
existing normalized orbit give the ordered finite level on every geometric fibre. -/
def harrisIntegralOrderedFullLevel (X : PObj) (m : Index (fun _ => True))
    (U : ULevel) (hU : U.toSubgroup ≤ Cong m.val) (x : (tower X).obj U)
    (hx : LevelNormalized X U x) : FullLevel (BOf X) gH m.val := by
  let ixs : Fin (2 * gH) ≃ Fin (Module.finrank ℤ L) :=
    finCongr (harrisIntegralSource_rank D C).symm
  let reindex : (Fin (2 * gH) → ZMod m.val) ≃+ (Fin (Module.finrank ℤ L) → ZMod m.val) :=
    { toFun := fun f i => f (ixs.symm i)
      invFun := fun f i => f (ixs i)
      left_inv := fun f => funext fun i => congrArg f (ixs.symm_apply_apply i)
      right_inv := fun f => funext fun i => congrArg f (ixs.apply_symm_apply i)
      map_add' := fun _ _ => rfl }
  let coord := reindex.trans (harrisIntegralReducedSourceCoordinates D C h ⟨m.val, m.property.1⟩).symm
  let global := harrisIntegralLevelSections D C P s hs htor hu compatibility h X m U hU x hx
  let sections := coord.trans global
  refine ⟨fun i => sections (Pi.single i 1), ?_⟩
  intro Ω' _ _ t
  let ht : ∀ Y : Cover S, Finite (Fiber t Y) := geometricFiberFinite t
  obtain ⟨p⟩ := geometricPathExists s t hs ht
  let eta := Classical.choose hx
  have hnorm := (Classical.choose_spec hx).1
  have horbit := (Classical.choose_spec hx).2
  let er := harrisIntegralFrameTorsionEquiv D C P compatibility h s hu X m eta hnorm
  let e := (coord.trans er).trans (Tate.levelTransport htor (BOf X) m.val m.property.1 (hu m) p)
  let eLin : (Fin (2 * gH) → ZMod m.val) ≃ₗ[ZMod m.val]
      GroupScheme.Tate.Level (BOf X).toGrp (Over.mk t) m.val :=
    { e with map_smul' := ZMod.map_smul e.toAddMonoidHom }
  have hr (r : HarrisIntegralSourceMod D C m.val) :
      GroupScheme.Tate.levelRestrict (BOf X).toGrp (Over.homMk s (by simp)) m.val (global r) = er r :=
    (harrisIntegralLevelSections_restrict D C P s hs htor hu compatibility h X m U hU x hx r).trans
      (harrisIntegralLevelReduction_apply D C P compatibility h s hs htor hu X m U hU x hx
        eta hnorm horbit r)
  refine ⟨Module.Basis.ofEquivFun eLin.symm, fun i => ?_⟩
  have hb : (Module.Basis.ofEquivFun eLin.symm) i = eLin (Pi.single i 1) :=
    congrFun (Module.Basis.coe_ofEquivFun eLin.symm) i
  rw [hb]
  exact (congrArg (Tate.levelTransport htor (BOf X) m.val m.property.1 (hu m) p)
    (hr (coord (Pi.single i 1))).symm).trans
      (levelTransport_restrict_global s t hs ht htor (BOf X) m (hu m) p (sections (Pi.single i 1)))

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
