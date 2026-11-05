import Langlands.AbelianScheme.Kernel
import Langlands.GroupScheme.Products

/-! # Kernels under coordinate changes -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G G' H : GroupScheme S}

/-- An isomorphism of source coordinates preserving a homomorphism restricts
to an isomorphism of its actual group-scheme kernels. -/
def kernelCoordinateIso (f : G ⟶ H) (g : G' ⟶ H) (e : G' ≅ G)
    (he : e.hom ≫ f = g) : kernel g ≅ kernel f where
  hom := pullback.map _ _ _ _ e.hom (𝟙 _) (𝟙 _)
    (by simpa using he.symm) (by simp)
  inv := pullback.map _ _ _ _ e.inv (𝟙 _) (𝟙 _)
    (by rw [← he, Iso.inv_hom_id_assoc]; simp) (by simp)
  hom_inv_id := by
    apply pullback.hom_ext <;> simp [pullback.map, Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext <;> simp [pullback.map, Category.assoc]

@[reassoc (attr := simp)]
theorem kernelCoordinateIso_hom_ι (f : G ⟶ H) (g : G' ⟶ H) (e : G' ≅ G)
    (he : e.hom ≫ f = g) :
    (kernelCoordinateIso f g e he).hom ≫ kernelι f = kernelι g ≫ e.hom := by
  simp [kernelCoordinateIso, kernelι, pullback.map]

@[reassoc (attr := simp)]
theorem kernelCoordinateIso_inv_ι (f : G ⟶ H) (g : G' ⟶ H) (e : G' ≅ G)
    (he : e.hom ≫ f = g) :
    (kernelCoordinateIso f g e he).inv ≫ kernelι g = kernelι f ≫ e.inv := by
  simp [kernelCoordinateIso, kernelι, pullback.map]

end Langlands.GroupScheme
