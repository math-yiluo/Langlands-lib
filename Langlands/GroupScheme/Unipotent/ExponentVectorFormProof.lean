import Langlands.GroupScheme.Unipotent.ExponentVectorFormStatement
import Langlands.GroupScheme.Unipotent.PerfectExponentVectorProof
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Rational.CommutativePTorsionGeometry

/-! # Groups of exponent `p` over a perfect closure -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Milne's Corollary 14.56: a smooth connected commutative affine group killed by `p`
becomes a vector group over a perfect closure. -/
theorem exponentVectorGroupForm : ExponentVectorGroupFormStatement.{u} := by
  intro k _ p _ _ K _ _ _ _ G _ _ _ hConnected hPower
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let H := (baseChange b).obj G
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have : ConnectedSpace G.X.left := hConnected
  have : Smooth H.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  have : IsAffineHom H.X.hom := inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  have : IsCommMonObj H.X := Functor.isCommMonObj_obj (F := Over.pullback b) (M := G.X)
  exact perfectFieldExponentVectorGroup K p H (G.connectedSpace_baseChange_of_smooth_affine b)
    (HasUniformPowerExponent.baseChange (G := G) hPower b)

end Langlands.GroupScheme
