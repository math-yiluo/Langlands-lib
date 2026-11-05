import Langlands.GroupScheme.GroupLikeActionAffine
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.AffineCoordinateEvaluation

/-! # Coordinates equal to one at the identity are non-zero-divisors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineCoordinates

variable {k : Type u} [Field k]

/-- The global sections of the identity test scheme over `Spec k` form a nontrivial ring. -/
theorem nontrivial_algΓ_identityTest :
    Nontrivial ((algΓ (CommRingCat.of k)).obj (Over.mk (𝟙 (Spec (CommRingCat.of k))))).unop := by
  change Nontrivial Γ(Spec (CommRingCat.of k), ⊤)
  exact (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toEquiv.nontrivial

variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance coordinateNonZeroDivisorInst : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- Evaluation of coordinates at the identity rational point, with values in the global
sections of the identity test scheme `Spec k → Spec k`. -/
def identityEvaluation :
    algebra G →ₐ[k] ((algΓ (CommRingCat.of k)).obj (Over.mk (𝟙 (Spec (CommRingCat.of k))))).unop :=
  pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) 1

theorem identityEvaluation_apply (d : algebra G) :
    identityEvaluation G d = pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) 1 d :=
  rfl

/-- Evaluation at the identity rational point is the counit followed by the structure map. -/
theorem identityEvaluation_eq :
    identityEvaluation G =
      (Algebra.ofId k _).comp (AffineLinearEmbedding.counit (corepresentation G)) :=
  pointAlgebraHom_one G _

/-- The coordinate algebra of a connected reductive group over a field is a domain. -/
theorem isDomain_of_isConnectedReductive (hG : IsConnectedReductive G) :
    IsDomain (algebra G) := by
  have := hG.smooth
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have := hG.connectedSpace
  have : IsIntegral G.X.left := CharacterLatticeProof.isIntegral_of_smooth k G.X.hom
  exact AutomorphicAction.coordinate_isDomain (H := G)

/-- A coordinate taking the value `1` at the identity rational point is nonzero. -/
theorem ne_zero_of_pointAlgebraHom_one {d : algebra G}
    (hd : pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) 1 d = 1) : d ≠ 0 := by
  have := nontrivial_algΓ_identityTest (k := k)
  rintro rfl
  rw [← identityEvaluation_apply, map_zero] at hd
  exact zero_ne_one hd

/-- On a connected reductive group, a coordinate taking the value `1` at the identity rational
point is a non-zero-divisor. -/
theorem mem_nonZeroDivisors_of_pointAlgebraHom_one (hG : IsConnectedReductive G)
    {d : algebra G}
    (hd : pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) 1 d = 1) :
    d ∈ nonZeroDivisors (algebra G) := by
  have := isDomain_of_isConnectedReductive G hG
  exact mem_nonZeroDivisors_of_ne_zero (ne_zero_of_pointAlgebraHom_one G hd)

/-- On a simply connected group, a coordinate taking the value `1` at the identity rational
point is a non-zero-divisor. -/
theorem mem_nonZeroDivisors_of_isSimplyConnected (hG : IsSimplyConnected G) {d : algebra G}
    (hd : pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) 1 d = 1) :
    d ∈ nonZeroDivisors (algebra G) :=
  mem_nonZeroDivisors_of_pointAlgebraHom_one G hG.isSemisimple.isConnectedReductive hd

end AffineCoordinates

end Langlands.GroupScheme
