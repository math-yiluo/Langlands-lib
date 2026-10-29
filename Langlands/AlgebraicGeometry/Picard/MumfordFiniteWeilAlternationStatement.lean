import Langlands.AlgebraicGeometry.Picard.MumfordLineBundle
import Langlands.AlgebraicGeometry.Picard.FiniteWeilAlongHom

/-! # Alternation of the actual finite pairing along a Mumford map -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

/-- If a dual-valued homomorphism has the Mumford map of an actual line bundle on `A` as its
underlying scheme morphism, then the actual finite pairing along it is trivial on the diagonal
at every positive level. This is a relative theorem target (the theta-group argument), not a
proof. -/
def MumfordFiniteWeilAlternationStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (square : MumfordBundlePicardZeroStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
    (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
    (symmetry : PullbackTensorSymmetryStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S)
    (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
    (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
      structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (L : LineBundle A.X.left) (B : LineBundle S)
    (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅
      structureSheaf S)
    (M : LineBundle A.X.left)
    (evaluation : tensorObj (LineBundle.normalize preservation A.X.hom (unitSection A)
      (unitSection_comp A) L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left)
    (lam : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
      evaluationA stability composition unitCoherence associativity comparison symmetry),
      (groupHom lam).hom.hom =
          mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA →
      ∀ (n : ℕ), 0 < n →
        prod.lift (𝟙 _) (𝟙 _) ≫
          finiteWeilAlongHomPairing preservation composition unitCoherence associativity
            comparison symmetry stability hA geometryA MA evaluationA lam n =
        (1 : (kernelCommGroupScheme (multiplication A (n : ℤ))).X ⟶ (mu S n).X)

end Langlands.AbelianScheme
