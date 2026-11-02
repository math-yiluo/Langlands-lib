import Langlands.GroupScheme.Dynamic.LimitMap
import Langlands.Representation.Aubert.General.Parabolic

/-!
# Dynamic parabolic subgroups as semidirect decompositions

For a cocharacter `χ` of a group scheme `G` over `S` with separated structure
morphism, the published dynamic subgroups `P(χ)`, `Z(χ)` and `U(χ)` give, on the
points over every test scheme `T`, an actual semidirect decomposition
`P(χ)(T) = Z(χ)(T) ⋉ U(χ)(T)` in the sense of
`Langlands.Aubert.General.IsSemidirectDecomposition`, and its projection is the
published limit homomorphism. At the identity test object over `Spec k` these are
the rational points, so the normalized functors of `Aubert.General.Parabolic`
apply to them once the rational points carry their point topology.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

open Langlands.GroupScheme

variable {S : Scheme.{u}} {G : GroupScheme S} (χ : (Gm S).toGrp ⟶ G)

/-- The points of `P(χ)` normalize the points of `U(χ)`. -/
theorem dynamic_parabolic_le_normalizer (T : Over S) :
    (Dynamic.parabolic χ).carrier T ≤
      Subgroup.normalizer (((Dynamic.unipotent χ).carrier T : Subgroup (T ⟶ G.X)) :
        Set (T ⟶ G.X)) := by
  intro p hp u
  refine ⟨fun hu => Dynamic.conj_mem_unipotent χ hp hu, fun hu => ?_⟩
  have h := Dynamic.conj_mem_unipotent χ (inv_mem hp) hu
  rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
    mul_one] at h

variable [IsSeparated G.X.hom]

/-- `P(χ)(T) = Z(χ)(T) ⋉ U(χ)(T)` as actual subgroups of `G(T)`, from the published
complement theorem (Conrad–Gabber–Prasad, Proposition 2.1.8(2)). -/
theorem dynamic_isSemidirectDecomposition (T : Over S) :
    IsSemidirectDecomposition ((Dynamic.parabolic χ).carrier T)
      ((Dynamic.centralizer χ).carrier T) ((Dynamic.unipotent χ).carrier T) :=
  IsSemidirectDecomposition.of_isComplement'_symm (Dynamic.centralizer_le_parabolic χ T)
    (Dynamic.unipotent_le_parabolic χ T) (dynamic_parabolic_le_normalizer χ T)
    (Dynamic.isComplement'_unipotent_centralizer_of_isSeparated χ T)

/-- The projection of this decomposition is the published limit homomorphism
`P(χ)(T) →* Z(χ)(T)`. -/
theorem dynamic_projection_eq_limitHom (T : Over S) :
    (dynamic_isSemidirectDecomposition χ T).projection = Dynamic.limitHom χ T := by
  ext p : 1
  rw [IsSemidirectDecomposition.projection_eq_iff]
  have hl : Dynamic.limit χ p ∈ (Dynamic.parabolic χ).carrier T :=
    Dynamic.centralizer_le_parabolic χ T (Dynamic.limit_mem_centralizer χ p)
  have h := Dynamic.conj_mem_unipotent χ (inv_mem hl) (Dynamic.mul_inv_limit_mem_unipotent χ p)
  rw [inv_inv, mul_assoc, inv_mul_cancel_right] at h
  exact h

end Langlands.Aubert.General
