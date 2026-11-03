import Langlands.GroupScheme.Absolute.BorelPromotion

/-! # Borel embeddings inside an intermediate closed subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {B P G : GroupScheme (Spec (CommRingCat.of k))}

/-- The factor of a Borel through an actual closed subgroup is Borel. -/
theorem IsBorelSubgroup.of_closed_factor {i : P ⟶ G} (hi : IsClosedSubgroup i)
    {j : B ⟶ G} (hj : IsBorelSubgroup j) (f : B ⟶ P) (hf : f ≫ i = j) :
    IsBorelSubgroup f := by
  apply IsBorelSubgroup.of_comp hi
  rwa [hf]

/-- An actual factorization of one Borel embedding through another gives an isomorphism. -/
def IsBorelSubgroup.isoOfFactor {j : B ⟶ G} {i : P ⟶ G}
    (hj : IsBorelSubgroup j) (hi : IsBorelSubgroup i) (f : B ⟶ P)
    (hf : f ≫ i = j) : B ≅ P := by
  have : IsIso f := hj.maximal P i f hi.isClosedSubgroup hi.smooth
    hi.connectedSpace hi.isSolvableGroupScheme hf
  exact asIso f

@[simp] theorem IsBorelSubgroup.isoOfFactor_hom {j : B ⟶ G} {i : P ⟶ G}
    (hj : IsBorelSubgroup j) (hi : IsBorelSubgroup i) (f : B ⟶ P)
    (hf : f ≫ i = j) : (hj.isoOfFactor hi f hf).hom = f := rfl

/-- The constructed isomorphism commutes with the original Borel embeddings. -/
theorem IsBorelSubgroup.isoOfFactor_hom_comp {j : B ⟶ G} {i : P ⟶ G}
    (hj : IsBorelSubgroup j) (hi : IsBorelSubgroup i) (f : B ⟶ P)
    (hf : f ≫ i = j) : (hj.isoOfFactor hi f hf).hom ≫ i = j := hf

end Langlands.GroupScheme
