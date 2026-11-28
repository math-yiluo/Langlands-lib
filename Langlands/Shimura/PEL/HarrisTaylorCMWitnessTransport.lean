import Langlands.Shimura.PEL.HarrisTaylorCMWitnessBaseChange
import Langlands.Shimura.PEL.PolarizedWeilLevelPointTransport
import Langlands.AbelianScheme.Tate.WeilCompactOpenLevelPathBaseChange
import Langlands.Shimura.PEL.HarrisPolarizedBaseChangeComposition

/-! # Path transport of Harris polarized representatives and their witnesses -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.PolarizedWeilLevel

open Langlands.AbelianScheme Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

section Witness

universe u v w

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (square : MumfordBundlePicardZeroStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  {S : Scheme.{u}} {D : Type v} [Ring D] [Algebra ℚ D] [StarRing D]
  [QuasiSeparatedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S, Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S, Finite (Fiber r Y)}

local notation "Level" => FiniteAdelicScalarExtensionLevel D V ψ
local notation "dataAt" => LevelData preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ


local notation "move" => pointMapData preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ htor hu

variable (additivity : PairAdditivity preservation composition unitCoherence associativity
  comparison symmetry stability square universality (S := S) (D := D))

/-- Path transport of representatives keeps every witness of the polarized isogeny
relation: the same rational isomorphism and multiplier relate the transported
representatives. -/
theorem pointMapData_witness (p : fiberFunctor s hs ≅ fiberFunctor t ht) (K : Level)
    (x y : dataAt s hs htor hu K) (q : ℚˣ) (e : x.1.actionObj ≅ y.1.actionObj)
    (he : Multiple preservation composition unitCoherence associativity comparison symmetry
      stability square universality additivity x.1 y.1 q e)
    (hxy : levelIso preservation composition unitCoherence associativity comparison symmetry
      stability square universality compatibility h V ψ s hs htor hu additivity x.1 y.1 K q e
      he x.2 = y.2) :
    levelIso preservation composition unitCoherence associativity comparison symmetry
      stability square universality compatibility h V ψ t ht htor hu additivity x.1 y.1 K q e
      he (move p K x).2 = (move p K y).2 := by
  have sq := weilAdelicLevelIsogeny_transport preservation composition unitCoherence
    associativity comparison symmetry stability x.1.hasDual y.1.hasDual x.1.geometry
    y.1.geometry x.1.inversePoincare x.1.evaluation y.1.inversePoincare y.1.evaluation
    (additivity x.1 y.1) x.1.polarization y.1.polarization compatibility
    rationalWeilFunctoriality rationalWeilGeometricTransport h x.1.actionObj.action
    y.1.actionObj.action V ψ s hs htor hu K.toSubgroup q
    (RationalAlgebraAction.underlyingIso e) (RationalAlgebraAction.intertwines e.hom) he p x.2
  exact sq.symm.trans (congrArg (fun z =>
    (weilAdelicCompactOpenLevelTransport preservation composition unitCoherence
      associativity comparison symmetry stability compatibility y.1.hasDual y.1.geometry
      y.1.inversePoincare y.1.evaluation y.1.polarization h y.1.actionObj.action
      V ψ htor hu p).hom.app K z) hxy)

end Witness

end Langlands.Shimura.PEL.PolarizedWeilLevel

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
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
  {S T : Scheme.{0}} (b : T ⟶ S)


variable [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω Ω' : Type} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ T} {t : Spec (.of Ω') ⟶ T}
  (hs : ∀ Y : Cover T, Finite (Fiber s Y))
  (ht : ∀ Y : Cover T, Finite (Fiber t Y))
  (hsb : ∀ Y : Cover S, Finite (Fiber (s ≫ b) Y))
  (htb : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T k.val).X.hom]
  [hμetT : ∀ k : Index (fun _ => True), Etale (mu T k.val).X.hom]
  (dualData : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality b X)

local notation "indexFunctor" => hodgeLevelFunctor D C

/-- Actual pullback of Harris representatives commutes with path transport:
transporting along the pushed path on the old base and then pulling back
agrees with pulling back and then transporting along the path on the new base.
The polarized objects agree definitionally; the orbits agree by the actual
base-change/path square of Weil level towers. -/
theorem levelDataBaseChange_pointMapData (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : HarrisLevel D)
    (x : HarrisLevelData D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h (s ≫ b) hsb htor huS U) :
    letI := auxiliaryStarRing D C
    levelDataBaseChange D C preservation composition unitCoherence associativity comparison
        symmetry stability square universality dualityNaturality polarizationStability b
        compatibility h t ht htb htor huS huT dualData U
        (PolarizedWeilLevel.pointMapData preservation composition unitCoherence associativity
          comparison symmetry stability square universality compatibility h A
          (D.harrisHodgePELForm C) htor huS (pathPushforward b hsb htb p)
          ((indexFunctor).obj U) x) =
      PolarizedWeilLevel.pointMapData preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h A
        (D.harrisHodgePELForm C) htor huT p ((indexFunctor).obj U)
        (levelDataBaseChange D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability b compatibility h s hs hsb htor huS huT dualData U x) := by
  let := auxiliaryStarRing D C
  let W := dualData x.1
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  exact congrArg (fun k => k.app ((indexFunctor).obj U) x.2)
    (Tate.weilAdelicCompactOpenLevelBaseChange_transport b x.1.actionObj.abelianScheme
      preservation composition unitCoherence associativity comparison symmetry stability
      universality x.1.hasDual x.1.geometry x.1.inversePoincare x.1.evaluation
      W.hasDual W.geometry W.inversePoincare W.evaluation compatibility x.1.polarization h
      x.1.actionObj.action A (D.harrisHodgePELForm C) htor hsb htb huS huT p)


/-- Orbit form of the commutation of pullback with path transport, for
representatives transported from a base point of the old base. -/
theorem levelDataBaseChange_pointMapData_snd
    {Ω₀ : Type} [Field Ω₀] {s₀ : Spec (.of Ω₀) ⟶ S}
    (hs₀ : ∀ Y : Cover S, Finite (Fiber s₀ Y))
    (p₁ : fiberFunctor s₀ hs₀ ≅ fiberFunctor (s ≫ b) hsb)
    (p₂ : fiberFunctor s₀ hs₀ ≅ fiberFunctor (t ≫ b) htb)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (U : HarrisLevel D)
    (z : HarrisLevelData D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h s₀ hs₀ htor huS U) :
    letI := auxiliaryStarRing D C
    (levelDataBaseChange D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability b compatibility h t ht htb htor huS huT dualData U
        (PolarizedWeilLevel.pointMapData preservation composition unitCoherence
          associativity comparison symmetry stability square universality compatibility h A
          (D.harrisHodgePELForm C) htor huS p₂ ((indexFunctor).obj U) z)).2 =
      (PolarizedWeilLevel.pointMapData preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h A
        (D.harrisHodgePELForm C) htor huT p ((indexFunctor).obj U)
        (levelDataBaseChange D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability b compatibility h s hs hsb htor huS huT dualData U
          (PolarizedWeilLevel.pointMapData preservation composition unitCoherence
            associativity comparison symmetry stability square universality compatibility h A
            (D.harrisHodgePELForm C) htor huS p₁ ((indexFunctor).obj U) z))).2 := by
  let := auxiliaryStarRing D C
  let W := dualData z.1
  have e1 := congrArg (fun k => k.hom.app ((indexFunctor).obj U) z.2)
    ((Tate.weilAdelicCompactOpenLevelTransport_path_independent preservation composition
      unitCoherence associativity comparison symmetry stability compatibility z.1.hasDual
      z.1.geometry z.1.inversePoincare z.1.evaluation z.1.polarization h
      z.1.actionObj.action A (D.harrisHodgePELForm C) htor huS p₂
      (p₁ ≪≫ pathPushforward b hsb htb p)).trans
      (Tate.weilAdelicCompactOpenLevelTransport_trans preservation composition
        unitCoherence associativity comparison symmetry stability compatibility z.1.hasDual
        z.1.geometry z.1.inversePoincare z.1.evaluation z.1.polarization h
        z.1.actionObj.action A (D.harrisHodgePELForm C) htor huS p₁
        (pathPushforward b hsb htb p)))
  have e2 := congrArg (fun k => k.app ((indexFunctor).obj U)
      ((Tate.weilAdelicCompactOpenLevelTransport preservation composition unitCoherence
        associativity comparison symmetry stability compatibility z.1.hasDual z.1.geometry
        z.1.inversePoincare z.1.evaluation z.1.polarization h z.1.actionObj.action A
        (D.harrisHodgePELForm C) htor huS p₁).hom.app ((indexFunctor).obj U) z.2))
    (Tate.weilAdelicCompactOpenLevelBaseChange_transport b z.1.actionObj.abelianScheme
      preservation composition unitCoherence associativity comparison symmetry stability
      universality z.1.hasDual z.1.geometry z.1.inversePoincare z.1.evaluation
      W.hasDual W.geometry W.inversePoincare W.evaluation compatibility z.1.polarization h
      z.1.actionObj.action A (D.harrisHodgePELForm C) htor hsb htb huS huT p)
  simp only [Iso.trans_hom, NatTrans.comp_app] at e1 e2
  exact (congrArg ((Tate.weilAdelicCompactOpenLevelBaseChange b z.1.actionObj.abelianScheme
      preservation composition unitCoherence associativity comparison symmetry stability
      universality z.1.hasDual z.1.geometry z.1.inversePoincare z.1.evaluation
      W.hasDual W.geometry W.inversePoincare W.evaluation compatibility z.1.polarization h
      z.1.actionObj.action A (D.harrisHodgePELForm C) t ht htb htor huS huT).app
      ((indexFunctor).obj U)) e1).trans e2

/-- The polarized object of a pulled-back representative does not depend on the
geometric point at which it is presented, nor on its orbit. -/
theorem levelDataBaseChange_fst_eq (U : HarrisLevel D)
    (z : HarrisLevelData D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h (s ≫ b) hsb htor huS U)
    (z' : HarrisLevelData D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h (t ≫ b) htb htor huS U)
    (hz : z.1 = z'.1) :
    (levelDataBaseChange D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability b compatibility h s hs hsb htor huS huT dualData U z).1 =
      (levelDataBaseChange D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability b compatibility h t ht htb htor huS huT dualData U z').1 := by
  obtain ⟨X, o⟩ := z
  obtain ⟨X', o'⟩ := z'
  cases hz
  rfl

set_option maxHeartbeats 3200000 in
/-- Witnesses of the pulled-back relation move between geometric points of the new
base. The representatives at the second point are given by the same polarized
objects with their own orbits, together with the identification of their pulled
back orbits with the transports of the pulled-back orbits at the first point. -/
theorem levelDataBaseChange_witness_move
    (addT : PositivePairAdditivity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (S := T))
    {U : HarrisLevel D}
    (z w : HarrisLevelData D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h (s ≫ b) hsb htor huS U)
    (oz : letI := auxiliaryStarRing D C
      (PolarizedWeilLevel.levelTower preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h A
        (D.harrisHodgePELForm C) (t ≫ b) htb htor huS z.1).obj ((indexFunctor).obj U))
    (ow : letI := auxiliaryStarRing D C
      (PolarizedWeilLevel.levelTower preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h A
        (D.harrisHodgePELForm C) (t ≫ b) htb htor huS w.1).obj ((indexFunctor).obj U))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (hz : letI := auxiliaryStarRing D C
      (levelDataBaseChange D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability b compatibility h t ht htb htor huS huT dualData U ⟨z.1, oz⟩).2 =
      (PolarizedWeilLevel.pointMapData preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h A
        (D.harrisHodgePELForm C) htor huT p ((indexFunctor).obj U)
        (levelDataBaseChange D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability b compatibility h s hs hsb htor huS huT dualData U z)).2)
    (hw : letI := auxiliaryStarRing D C
      (levelDataBaseChange D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability b compatibility h t ht htb htor huS huT dualData U ⟨w.1, ow⟩).2 =
      (PolarizedWeilLevel.pointMapData preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h A
        (D.harrisHodgePELForm C) htor huT p ((indexFunctor).obj U)
        (levelDataBaseChange D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability b compatibility h s hs hsb htor huS huT dualData U w)).2) :
    letI := auxiliaryStarRing D C
    ∀ (q : ℚˣ) (e : (RationalAlgebraAction.pullback b).obj z.1.actionObj ≅
        (RationalAlgebraAction.pullback b).obj w.1.actionObj),
      (∃ he : PolarizedWeilLevel.Multiple preservation composition unitCoherence associativity
          comparison symmetry stability square universality addT
          (levelDataBaseChange D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality dualityNaturality
            polarizationStability b compatibility h s hs hsb htor huS huT dualData U z).1
          (levelDataBaseChange D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality dualityNaturality
            polarizationStability b compatibility h s hs hsb htor huS huT dualData U w).1 q e,
        PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
            comparison symmetry stability square universality compatibility h A
            (D.harrisHodgePELForm C) s hs htor huT addT
            (levelDataBaseChange D C preservation composition unitCoherence associativity
              comparison symmetry stability square universality dualityNaturality
              polarizationStability b compatibility h s hs hsb htor huS huT dualData U z).1
            (levelDataBaseChange D C preservation composition unitCoherence associativity
              comparison symmetry stability square universality dualityNaturality
              polarizationStability b compatibility h s hs hsb htor huS huT dualData U w).1
            ((indexFunctor).obj U) q e he
            (levelDataBaseChange D C preservation composition unitCoherence associativity
              comparison symmetry stability square universality dualityNaturality
              polarizationStability b compatibility h s hs hsb htor huS huT dualData U z).2 =
          (levelDataBaseChange D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality dualityNaturality
            polarizationStability b compatibility h s hs hsb htor huS huT dualData U w).2) →
      ∃ he : PolarizedWeilLevel.Multiple preservation composition unitCoherence associativity
          comparison symmetry stability square universality addT
          (levelDataBaseChange D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality dualityNaturality
            polarizationStability b compatibility h t ht htb htor huS huT dualData U
            ⟨z.1, oz⟩).1
          (levelDataBaseChange D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality dualityNaturality
            polarizationStability b compatibility h t ht htb htor huS huT dualData U
            ⟨w.1, ow⟩).1 q e,
        PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
            comparison symmetry stability square universality compatibility h A
            (D.harrisHodgePELForm C) t ht htor huT addT
            (levelDataBaseChange D C preservation composition unitCoherence associativity
              comparison symmetry stability square universality dualityNaturality
              polarizationStability b compatibility h t ht htb htor huS huT dualData U
              ⟨z.1, oz⟩).1
            (levelDataBaseChange D C preservation composition unitCoherence associativity
              comparison symmetry stability square universality dualityNaturality
              polarizationStability b compatibility h t ht htb htor huS huT dualData U
              ⟨w.1, ow⟩).1
            ((indexFunctor).obj U) q e he
            (levelDataBaseChange D C preservation composition unitCoherence associativity
              comparison symmetry stability square universality dualityNaturality
              polarizationStability b compatibility h t ht htb htor huS huT dualData U
              ⟨z.1, oz⟩).2 =
          (levelDataBaseChange D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality dualityNaturality
            polarizationStability b compatibility h t ht htb htor huS huT dualData U
            ⟨w.1, ow⟩).2 := by
  let := auxiliaryStarRing D C
  rintro q e ⟨he, hl⟩
  have hmove := PolarizedWeilLevel.pointMapData_witness preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h A
    (D.harrisHodgePELForm C) htor huT addT p ((indexFunctor).obj U)
    (levelDataBaseChange D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability b compatibility h s hs hsb htor huS huT dualData U z)
    (levelDataBaseChange D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability b compatibility h s hs hsb htor huS huT dualData U w) q e he hl
  exact ⟨he, (congrArg _ hz).trans (hmove.trans hw.symm)⟩

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel


namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

section Composition

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
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
  {S T R : Scheme.{0}} (b : T ⟶ S) (c : R ⟶ T)

variable [QuasiSeparatedSpace S] [QuasiSeparatedSpace T] [QuasiSeparatedSpace R]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (t : Spec (.of Ω) ⟶ R)
  (ht : ∀ Y : Cover R, Finite (Fiber t Y))
  (htc : ∀ Y : Cover T, Finite (Fiber (t ≫ c) Y))
  (hs : ∀ Y : Cover S, Finite (Fiber ((t ≫ c) ≫ b) Y))
  (hd : ∀ Y : Cover S, Finite (Fiber (t ≫ (c ≫ b)) Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  (huR : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(R, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T k.val).X.hom]
  [hμetT : ∀ k : Index (fun _ => True), Etale (mu T k.val).X.hom]
  [hμfinR : ∀ k : Index (fun _ => True), IsFinite (mu R k.val).X.hom]
  [hμetR : ∀ k : Index (fun _ => True), Etale (mu R k.val).X.hom]
  (dualB : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality b X)
  (dualC : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T),
    PositivePullbackDualData D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality c X)
  (dualD : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality (c ≫ b) X)

local notation "DataS" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  ((t ≫ c) ≫ b) hs htor huS
local notation "indexFunctor" => hodgeLevelFunctor D C
local notation "pullB" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h (t ≫ c) htc hs htor huS huT dualB
local notation "pullC" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability c compatibility h t ht htc htor huT huR dualC
local notation "pullD" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability (c ≫ b) compatibility h t ht hd htor huS huR dualD
local notation "moveData" => levelDataPointEq D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor huS

local notation "compAction" => levelDataBaseChangeCompIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b c compatibility h t ht htc hs hd htor
  huS huT huR dualB dualC dualD

variable
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))
  (addR : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := R))


/-- The canonical direct-to-successive comparison is an explicit witness of the
polarized isogeny relation between the directly and successively pulled
representatives, with multiplier one. -/
theorem levelDataBaseChange_comp_witness (U : HarrisLevel D) (x : DataS U) :
    letI := auxiliaryStarRing D C
    PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h A
      (D.harrisHodgePELForm C) t ht htor huR addR
      (pullD U (moveData (Category.assoc t c b) hs hd U x)).1
      (pullC U (pullB U x)).1 ((indexFunctor).obj U) 1
      (compAction U x)
      (levelDataBaseChange_comp_multiple D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability b c compatibility h t ht htc hs hd htor huS huT huR
        dualB dualC dualD addR U x)
      (pullD U (moveData (Category.assoc t c b) hs hd U x)).2 =
    (pullC U (pullB U x)).2 := by
  let := auxiliaryStarRing D C
  rw [levelIso_pullbackComp D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b c compatibility h t ht htc hs hd htor huS huT huR
    dualB dualC dualD addR U x]
  exact Tate.weilAdelicLevelBaseChange_comp preservation composition unitCoherence
    associativity comparison symmetry stability x.1.hasDual x.1.geometry
    x.1.inversePoincare x.1.evaluation compatibility x.1.polarization h
    x.1.actionObj.action A (D.harrisHodgePELForm C) b c universality
    (dualB x.1).hasDual (dualB x.1).geometry (dualB x.1).inversePoincare
    (dualB x.1).evaluation
    (dualD x.1).hasDual (dualD x.1).geometry (dualD x.1).inversePoincare
    (dualD x.1).evaluation
    (dualC (pullB U x).1).hasDual (dualC (pullB U x).1).geometry
    (dualC (pullB U x).1).inversePoincare (dualC (pullB U x).1).evaluation
    t ht htor huR huS huT htc hs hd ((indexFunctor).obj U).toSubgroup x.2

end Composition

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

section PointEq

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
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
  {S : Scheme.{0}}


variable [QuasiSeparatedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]

/-- Re-presenting a transported representative along an equality of geometric
points is transport along any path to the new presentation. -/
theorem levelDataPointEq_pointMapData {Ω Ω' : Type} [Field Ω] [Field Ω']
    {t : Spec (.of Ω') ⟶ S} (ht : ∀ Y : Cover S, Finite (Fiber t Y))
    {s r : Spec (.of Ω) ⟶ S} (hsr : s = r)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y)) (hr : ∀ Y : Cover S, Finite (Fiber r Y))
    (U : HarrisLevel D) (p : fiberFunctor t ht ≅ fiberFunctor s hs)
    (p' : fiberFunctor t ht ≅ fiberFunctor r hr)
    (x : HarrisLevelData D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h t ht htor huS U) :
    letI := auxiliaryStarRing D C
    levelDataPointEq D C preservation composition unitCoherence associativity comparison
        symmetry stability square universality compatibility h htor huS hsr hs hr U
        (PolarizedWeilLevel.pointMapData preservation composition unitCoherence associativity
          comparison symmetry stability square universality compatibility h A
          (D.harrisHodgePELForm C) htor huS p ((hodgeLevelFunctor D C).obj U) x) =
      PolarizedWeilLevel.pointMapData preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h A
        (D.harrisHodgePELForm C) htor huS p' ((hodgeLevelFunctor D C).obj U) x := by
  let := auxiliaryStarRing D C
  subst hsr
  exact PolarizedWeilLevel.pointMapData_path_independent preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h A (D.harrisHodgePELForm C) htor huS p p' ((hodgeLevelFunctor D C).obj U) x

end PointEq

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
