import Langlands.GroupScheme.Adjoint.CenterQuotientStatement
import Langlands.GroupScheme.FppfQuotientTargetSmooth
import Langlands.GroupScheme.Rational.FppfQuotientAction
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.Reductive.CenterBaseChangeProof
import Langlands.GroupScheme.GeometricConnectedness

/-! # Reduction of the centre-quotient theorem to algebraically closed fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The geometric core of the centre-quotient theorem: over an algebraically closed field,
the target of an fppf homomorphism from a smooth connected affine group with trivial unipotent
radical, whose actual kernel is the full scheme-theoretic centre, has trivial unipotent
radical. -/
def CenterQuotientGeometricCoreStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (G Q : GroupScheme (Spec (CommRingCat.of K)))
    (q : G ⟶ Q),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
    HasTrivialUnipotentRadical G → IsAffineHom Q.X.hom → LocallyOfFiniteType Q.X.hom →
    RelativeRoot.IsFppfQuotient (center G) q → HasTrivialUnipotentRadical Q

/-- The full centre remains the actual kernel after an arbitrary base change. -/
theorem RelativeRoot.IsFppfQuotient.baseChange_center {S S' : Scheme.{u}} (b : S' ⟶ S)
    {G Q : GroupScheme S} {q : G ⟶ Q} (hq : RelativeRoot.IsFppfQuotient (center G) q) :
    RelativeRoot.IsFppfQuotient (center ((GroupScheme.baseChange b).obj G))
      ((GroupScheme.baseChange b).map q) := by
  rw [center_baseChange]
  exact hq.baseChange b

/-- The geometric core implies the centre-quotient theorem over every field. -/
theorem centerQuotientReductive_of_geometricCore
    (hcore : CenterQuotientGeometricCoreStatement.{u}) :
    CenterQuotientReductiveStatement.{u} := by
  intro k _ G Q q hG hQa hQf hq
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  let b := toAlgebraicClosure k
  have hGa : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (Limits.pullback.snd G.X.hom b)
    infer_instance
  have hGs : Smooth ((GroupScheme.baseChange b).obj G).X.hom := by
    change Smooth (Limits.pullback.snd G.X.hom b)
    infer_instance
  have hQa' : IsAffineHom ((GroupScheme.baseChange b).obj Q).X.hom := by
    change IsAffineHom (Limits.pullback.snd Q.X.hom b)
    infer_instance
  have hQf' : LocallyOfFiniteType ((GroupScheme.baseChange b).obj Q).X.hom := by
    change LocallyOfFiniteType (Limits.pullback.snd Q.X.hom b)
    infer_instance
  exact
    { smooth := hq.smooth_target
      isAffineHom := hQa
      connectedSpace := hq.connectedSpace
      hasTrivialGeometricUnipotentRadical :=
        hcore (AlgebraicClosure k) ((GroupScheme.baseChange b).obj G)
          ((GroupScheme.baseChange b).obj Q) ((GroupScheme.baseChange b).map q)
          hGs hGa hG.connectedSpace_toAlgebraicClosure hG.hasTrivialGeometricUnipotentRadical
          hQa' hQf' (hq.baseChange_center b) }

end Langlands.GroupScheme
