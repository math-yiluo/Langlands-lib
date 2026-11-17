import Langlands.GroupScheme.Reductive.AffinePinnedModel
import Langlands.GroupScheme.Reductive.AlmostSimple
import Langlands.GroupScheme.Reductive.GeometricSimplyConnected
import Langlands.LinearAlgebra.SimplyConnectedCartanComponents
import Langlands.GroupScheme.Products

/-! # Supplied affine products of simple Cartan-component factors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open Langlands.LinearAlgebra.SimplyConnectedCartanComponents

/-- A supplied finite product presentation of an affine pinned model by
reductive groups whose geometric fibres are almost simple, indexed by its
actual constant Cartan components. This structure does not assert existence. -/
structure RootComponentProduct (M : AffinePinnedModel.{u}) where
  factor : Component M.basis → GroupScheme M.base
  reductive : ∀ c, IsReductive (factor c)
  almostSimple : ∀ c s, IsAlmostSimple (geometricFiber (factor c) s)
  iso : M.group ≅ GroupScheme.pi factor

namespace RootComponentProduct

variable {M : AffinePinnedModel.{u}} (D : RootComponentProduct M)

instance factor_isAffine (c : Component M.basis) : IsAffine (D.factor c).X.left := by
  let : IsAffineHom (D.factor c).X.hom := (D.reductive c).isAffineHom
  exact isAffine_of_isAffineHom (D.factor c).X.hom

instance factor_locallyOfFiniteType (c : Component M.basis) :
    LocallyOfFiniteType (D.factor c).X.hom := by
  let : Smooth (D.factor c).X.hom := (D.reductive c).smooth
  infer_instance

/-- The supplied product presentation induces the actual product presentation
on every chosen geometric fibre. -/
def geometricFiberIso (s : M.base) :
    geometricFiber M.group s ≅ pi (fun c => geometricFiber (D.factor c) s) :=
  (baseChange (geometricPoint M.base s)).mapIso D.iso ≪≫
    PreservesProduct.iso (baseChange (geometricPoint M.base s)) D.factor

include D in
/-- A nontrivial geometric fibre forces a nonempty Cartan-component index. -/
theorem nonempty_component_of_nontrivialGeometricFiber (s : M.base)
    (hs : HasNontrivialPoints (geometricFiber M.group s)) :
    Nonempty (Component M.basis) := by
  classical
  by_contra hn
  let : IsEmpty (Component M.basis) := not_nonempty_iff.mp hn
  obtain ⟨Z, x, hx⟩ := (hasNontrivialPoints_iff_of_iso (D.geometricFiberIso s)).mp hs
  apply hx
  apply (piPointsEquiv (fun c => geometricFiber (D.factor c) s) Z).injective
  funext c
  exact isEmptyElim c

end RootComponentProduct

end Langlands.GroupScheme
