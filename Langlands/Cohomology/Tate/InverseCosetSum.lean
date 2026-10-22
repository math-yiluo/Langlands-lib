import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.GroupTheory.Coset.Basic

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G]
variable (H : Subgroup G) [Fintype (G ⧸ H)]

/-- The coefficient sum over inverses of the fixed left-coset representatives. -/
def inverseCosetSum (A : Rep.{u} R G) : A →ₗ[R] A :=
  ∑ q : G ⧸ H, A.ρ q.out⁻¹

lemma inverseCosetSum_apply (A : Rep.{u} R G) (a : A) :
    inverseCosetSum H A a = ∑ q : G ⧸ H, A.ρ q.out⁻¹ a := by
  simp only [inverseCosetSum, LinearMap.sum_apply]

lemma inverseCosetSum_naturality {A B : Rep.{u} R G} (f : A ⟶ B) (a : A) :
    f.hom (inverseCosetSum H A a) = inverseCosetSum H B (f.hom a) := by
  simp only [inverseCosetSum, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl (fun q _ => Rep.hom_comm_apply f q.out⁻¹ a)

end Langlands.Tate
