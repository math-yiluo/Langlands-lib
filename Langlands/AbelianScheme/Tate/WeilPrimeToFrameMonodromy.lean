import Langlands.AbelianScheme.Tate.WeilFrame
import Langlands.AbelianScheme.Tate.WeilGeometricTransportStatement

/-! # Actual geometric monodromy on prime-to-modulus Weil-compatible frames -/

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
  {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom]

local notation "pairing" => awayAdelicWeilAlongHomBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility (Over.mk s) polarizationMap hAway

/-- Actual Tate monodromy and actual twist monodromy preserve the pairing together,
conditional on the named geometric compatibility proposition. -/
def weilPrimeToFiniteAdeleTwistedMonodromyRepresentation :
    letI := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
    letI := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp (Over.mk s) hAway
    letI := TateTwist.Divisibility.primeToFiniteAdeleModule Γ((Over.mk s).left, ⊤) hAway
    FundamentalGroup s hs →*
      twistedSimilitudes (D ⊗[ℚ] Global.PrimeToFiniteAdeles m) pairing := by
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  letI := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp (Over.mk s) hAway
  letI := TateTwist.Divisibility.primeToFiniteAdeleModule Γ((Over.mk s).left, ⊤) hAway
  let τ := primeToFiniteAdeleAlgebraMonodromyRepresentation s hs htor A m hu hAway i
  let χ := TateTwist.Geometry.sectionPrimeToFiniteAdeleRepresentation (s := s) (hs := hs) hAway
    (hμfin := hμfin) (hμet := hμet)
  refine {
    toFun := fun g => ⟨(τ g, χ g), ?_⟩
    map_one' := Subtype.ext (Prod.ext (map_one τ) (map_one χ))
    map_mul' := fun g k => Subtype.ext (Prod.ext (map_mul τ g k) (map_mul χ g k)) }
  intro x y
  change pairing (rationalMonodromy s hs htor A (fun n => Nat.Coprime n m) hu g x)
      (rationalMonodromy s hs htor A (fun n => Nat.Coprime n m) hu g y) =
    TateTwist.Geometry.sectionPrimeToFiniteAdeleRepresentation hAway
      (hμfin := hμfin) (hμet := hμet) g (pairing x y)
  rw [← TateTwist.Geometry.sectionPrimeToFiniteAdeleTransport_aut]
  simpa only [awayAdelicWeilAlongHomBilinearMap_apply,
    TateTwist.Geometry.sectionPrimeToFiniteAdeleTransport_apply, rationalTransport_aut] using
    ((geometricCompatibility preservation composition unitCoherence associativity
    comparison symmetry stability compatibility S A hA geometryA MA evaluationA Ω Ω s s
      hs hs htor (fun n => Nat.Coprime n m) hu hμfin hμet g).2 polarizationMap x y).symm

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
  {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom]

local notation "AwayFrame" => WeilPrimeToAdelicFrame preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
  polarizationMap h i V ψ s hAway

local notation "monodromy" => weilPrimeToFiniteAdeleTwistedMonodromyRepresentation preservation
  composition unitCoherence associativity comparison symmetry stability compatibility
  geometricCompatibility hA geometryA MA evaluationA polarizationMap hAway i s hs htor hu (hμfin := hμfin) (hμet := hμet)

/-- The actual left geometric action on the restricted prime-to-modulus frame space. -/
@[instance_reducible]
def weilPrimeToAdelicFrameMonodromyAction : MulAction (FundamentalGroup s hs) AwayFrame := by
  letI := scalarExtensionAlgebraModule D V (Global.PrimeToFiniteAdeles m)
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  letI := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp (Over.mk s) hAway
  letI := TateTwist.Divisibility.primeToFiniteAdeleModule Γ((Over.mk s).left, ⊤) hAway
  exact MulAction.compHom AwayFrame monodromy

/-- Left monodromy commutes with the right source-similitude action. -/
theorem weilPrimeToAdelicFrameActionsComm :
    letI := weilPrimeToAdelicFrameRightAction preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
      polarizationMap h i V ψ s hAway
    letI := weilPrimeToAdelicFrameMonodromyAction preservation composition unitCoherence
      associativity comparison symmetry stability compatibility geometricCompatibility
      hA geometryA MA evaluationA polarizationMap hAway i V ψ s hs htor hu
      (hμfin := hμfin) (hμet := hμet)
    SMulCommClass (FundamentalGroup s hs)
      (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)ᵐᵒᵖ AwayFrame := by
  let := weilPrimeToAdelicFrameRightAction preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
    polarizationMap h i V ψ s hAway
  let := weilPrimeToAdelicFrameMonodromyAction preservation composition unitCoherence
    associativity comparison symmetry stability compatibility geometricCompatibility
    hA geometryA MA evaluationA polarizationMap hAway i V ψ s hs htor hu
    (hμfin := hμfin) (hμet := hμet)
  exact ⟨fun _ _ _ => by apply Subtype.ext; ext x; rfl⟩

/-- Level structures as geometrically fixed right orbits of actual Weil-compatible
frames. Compact open subgroup levels are special cases of this construction. -/
abbrev WeilPrimeToAdelicLevel
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)) :=
  letI := weilPrimeToAdelicFrameRightAction preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
    polarizationMap h i V ψ s hAway
  letI := weilPrimeToAdelicFrameMonodromyAction preservation composition unitCoherence
    associativity comparison symmetry stability compatibility geometricCompatibility
    hA geometryA MA evaluationA polarizationMap hAway i V ψ s hs htor hu
    (hμfin := hμfin) (hμet := hμet)
  letI := weilPrimeToAdelicFrameActionsComm preservation composition unitCoherence associativity
    comparison symmetry stability compatibility geometricCompatibility hA geometryA MA
    evaluationA polarizationMap hAway i V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)
  InvariantOrbit (X := AwayFrame) (FundamentalGroup s hs) U

end Langlands.AbelianScheme.Tate
