import Langlands.AbelianScheme.Tate.WeilRationalAlongHom
import Langlands.AbelianScheme.Tate.RationalTransport
import Langlands.AbelianScheme.Tate.TwistSectionTransport

/-! # Geometric path compatibility of the actual rational Weil pairing -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme
open GroupScheme.Tate (Index)

/-- The actual rational Weil pairing and every actual dual-hom pullback commute
with geometric path transport on both arguments and the roots-of-unity twist. -/
def RationalWeilGeometricTransportStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
    (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
    (symmetry : PullbackTensorSymmetryStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (compatibility : RelativeFiniteWeilTransitionStatement.{u})
    (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
    (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
      structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (Ω Ω' : Type u) [Field Ω] [Field Ω']
    (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ω') ⟶ S)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (ht : ∀ Y : Cover S, Finite (Fiber t Y))
    (htor : TorsionFiniteEtaleStatement.{u}) (P : ℕ → Prop)
    (hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))
    (hμfin : ∀ n : Index P, IsFinite (mu S n.val).X.hom)
    (hμet : ∀ n : Index P, Etale (mu S n.val).X.hom)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht),
    let DA := dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
      evaluationA stability composition unitCoherence associativity comparison symmetry
    (∀ (x : Tate.Rational A (Over.mk s) P) (y : Tate.Rational DA (Over.mk s) P),
      TateTwist.Geometry.sectionRationalTransport P (hμfin := hμfin) (hμet := hμet) p
          (rationalWeilBilinearMap preservation composition unitCoherence associativity
            comparison symmetry stability hA MA evaluationA compatibility (Over.mk s) P x y) =
        rationalWeilBilinearMap preservation composition unitCoherence associativity
          comparison symmetry stability hA MA evaluationA compatibility (Over.mk t) P
          (Tate.rationalTransport htor A P hu p x)
          (Tate.rationalTransport htor DA P hu p y)) ∧
    (∀ (lam : A ⟶ DA) (x y : Tate.Rational A (Over.mk s) P),
      TateTwist.Geometry.sectionRationalTransport P (hμfin := hμfin) (hμet := hμet) p
          (rationalWeilAlongHomBilinearMap preservation composition unitCoherence
            associativity comparison symmetry stability hA geometryA MA evaluationA
            compatibility (Over.mk s) lam P x y) =
        rationalWeilAlongHomBilinearMap preservation composition unitCoherence associativity
          comparison symmetry stability hA geometryA MA evaluationA compatibility
          (Over.mk t) lam P (Tate.rationalTransport htor A P hu p x)
          (Tate.rationalTransport htor A P hu p y))

end Langlands.AbelianScheme
