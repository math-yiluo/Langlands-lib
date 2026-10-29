import Langlands.AbelianScheme.Tate.WeilFrame
import Langlands.AbelianScheme.Tate.WeilGeometricTransportStatement

/-! # Actual geometric monodromy on Weil-compatible adelic frames -/

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme.Tate

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme Langlands.Shimura.PEL
open GroupScheme.Tate (Index)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (geometricCompatibility : RationalWeilGeometricTransportStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (polarizationMap : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
    evaluationA stability composition unitCoherence associativity comparison symmetry)
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (P : ℕ → Prop) (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index P, IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index P, Etale (mu S n.val).X.hom]

local notation "pairing" => adelicWeilAlongHomBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility (Over.mk s) polarizationMap P h

/-- Actual Tate monodromy and actual twist monodromy preserve the pairing together,
conditional on the named geometric compatibility proposition. -/
def weilFiniteAdeleTwistedMonodromyRepresentation :
    letI := finiteAdeleAlgebraModule A (Over.mk s) P h i
    letI := GroupScheme.Tate.finiteAdeleModule A.toGrp (Over.mk s) P h
    letI := TateTwist.Divisibility.finiteAdeleModule Γ((Over.mk s).left, ⊤) P h
    FundamentalGroup s hs →*
      twistedSimilitudes (D ⊗[ℚ] Global.FiniteAdeles ℚ) pairing := by
  letI := finiteAdeleAlgebraModule A (Over.mk s) P h i
  letI := GroupScheme.Tate.finiteAdeleModule A.toGrp (Over.mk s) P h
  letI := TateTwist.Divisibility.finiteAdeleModule Γ((Over.mk s).left, ⊤) P h
  let τ := finiteAdeleAlgebraMonodromyRepresentation s hs htor A P hu h i
  let χ := TateTwist.Geometry.sectionFiniteAdeleRepresentation (s := s) (hs := hs) P
    (hμfin := hμfin) (hμet := hμet) h
  refine {
    toFun := fun g => ⟨(τ g, χ g), ?_⟩
    map_one' := Subtype.ext (Prod.ext (map_one τ) (map_one χ))
    map_mul' := fun g k => Subtype.ext (Prod.ext (map_mul τ g k) (map_mul χ g k)) }
  intro x y
  change pairing (rationalMonodromy s hs htor A P hu g x)
      (rationalMonodromy s hs htor A P hu g y) =
    TateTwist.Geometry.sectionFiniteAdeleRepresentation P
      (hμfin := hμfin) (hμet := hμet) h g (pairing x y)
  rw [← TateTwist.Geometry.sectionFiniteAdeleTransport_aut]
  simpa only [adelicWeilAlongHomBilinearMap_apply,
    TateTwist.Geometry.sectionFiniteAdeleTransport_apply, rationalTransport_aut] using
    ((geometricCompatibility preservation composition unitCoherence associativity
    comparison symmetry stability compatibility S A hA geometryA MA evaluationA Ω Ω s s
      hs hs htor P hu hμfin hμet g).2 polarizationMap x y).symm

end Langlands.AbelianScheme.Tate

namespace Langlands.AbelianScheme.Tate

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme Langlands.Shimura.PEL
open GroupScheme.Tate (Index)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (geometricCompatibility : RationalWeilGeometricTransportStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (polarizationMap : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
    evaluationA stability composition unitCoherence associativity comparison symmetry)
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom]

local notation "FullFrame" => WeilAdelicFrame preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
  polarizationMap h i V ψ s

local notation "monodromy" => weilFiniteAdeleTwistedMonodromyRepresentation preservation
  composition unitCoherence associativity comparison symmetry stability compatibility
  geometricCompatibility hA geometryA MA evaluationA polarizationMap h i s hs htor
  (fun _ => True) hu (hμfin := hμfin) (hμet := hμet)

/-- The actual left geometric action on the restricted full frame space. -/
@[instance_reducible]
def weilAdelicFrameMonodromyAction : MulAction (FundamentalGroup s hs) FullFrame := by
  letI := scalarExtensionAlgebraModule D V (Global.FiniteAdeles ℚ)
  letI := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  letI := GroupScheme.Tate.finiteAdeleModule A.toGrp (Over.mk s) (fun _ => True) h
  letI := TateTwist.Divisibility.finiteAdeleModule Γ((Over.mk s).left, ⊤)
    (fun _ => True) h
  exact MulAction.compHom FullFrame monodromy

/-- Left monodromy commutes with the right source-similitude action. -/
theorem weilAdelicFrameActionsComm :
    letI := weilAdelicFrameRightAction preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
      polarizationMap h i V ψ s
    letI := weilAdelicFrameMonodromyAction preservation composition unitCoherence
      associativity comparison symmetry stability compatibility geometricCompatibility
      hA geometryA MA evaluationA polarizationMap h i V ψ s hs htor hu
      (hμfin := hμfin) (hμet := hμet)
    SMulCommClass (FundamentalGroup s hs)
      (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)ᵐᵒᵖ FullFrame := by
  let := weilAdelicFrameRightAction preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
    polarizationMap h i V ψ s
  let := weilAdelicFrameMonodromyAction preservation composition unitCoherence
    associativity comparison symmetry stability compatibility geometricCompatibility
    hA geometryA MA evaluationA polarizationMap h i V ψ s hs htor hu
    (hμfin := hμfin) (hμet := hμet)
  exact ⟨fun _ _ _ => by apply Subtype.ext; ext x; rfl⟩

/-- Level structures as geometrically fixed right orbits of actual Weil-compatible
frames. Compact open subgroup levels are special cases of this construction. -/
abbrev WeilAdelicLevel
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)) :=
  letI := weilAdelicFrameRightAction preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
    polarizationMap h i V ψ s
  letI := weilAdelicFrameMonodromyAction preservation composition unitCoherence
    associativity comparison symmetry stability compatibility geometricCompatibility
    hA geometryA MA evaluationA polarizationMap h i V ψ s hs htor hu
    (hμfin := hμfin) (hμet := hμet)
  letI := weilAdelicFrameActionsComm preservation composition unitCoherence associativity
    comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
    evaluationA polarizationMap h i V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
  InvariantOrbit (X := FullFrame) (FundamentalGroup s hs) U

end Langlands.AbelianScheme.Tate
