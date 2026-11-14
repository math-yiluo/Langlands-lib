import Langlands.Geometry.Building.Kottwitz.ReductiveMap
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.Derived.KernelAnnihilation

/-! # Morphisms between supplied actual cocenters -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.Kottwitz
namespace Cocenter

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}
  (cH : Cocenter k H) (cG : Cocenter k G)

/-- Every map to a cocenter kills the full derived kernel of the source quotient. -/
theorem kernel_comp (f : H ⟶ G) :
    kernelι cH.quotient ≫ (f ≫ cG.quotient) = 0 := by
  let : IsAffineHom cH.torus.X.hom :=
    cH.isTorus.isConnectedReductive_of_fieldSplitting.isAffineHom
  let : IsAffineHom cG.torus.X.hom :=
    cG.isTorus.isConnectedReductive_of_fieldSplitting.isAffineHom
  have hd : IsDerivedSubgroup (kernelι cH.quotient) :=
    ⟨by
      change IsClosedImmersion (kernelι cH.quotient).hom.hom.left
      infer_instance, cH.isQuotient.2.2.2⟩
  exact hd.comp_eq_one (f ≫ cG.quotient)

/-- The actual map of cocenters exists uniquely by fpqc homomorphism descent. -/
theorem existsUnique_map (hH : IsConnectedReductive H) (f : H ⟶ G) :
    ∃! d : cH.torus ⟶ cG.torus,
      cH.quotient ≫ CommGroupScheme.groupHom d = f ≫ cG.quotient := by
  let : Flat cH.quotient.hom.hom.left := cH.isQuotient.1
  let : Surjective cH.quotient.hom.hom.left := cH.isQuotient.2.1
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : IsAffineHom cH.torus.X.hom :=
    cH.isTorus.isConnectedReductive_of_fieldSplitting.isAffineHom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : IsAffine cH.torus.X.left := isAffine_of_isAffineHom cH.torus.X.hom
  refine ⟨Additive.ofMul (FpqcHomDescent.hom cH.quotient
    (f ≫ cG.quotient) (cH.kernel_comp cG f)), ?_, ?_⟩
  · exact FpqcHomDescent.fac cH.quotient (f ≫ cG.quotient) (cH.kernel_comp cG f)
  · intro d hd
    exact congrArg Additive.ofMul
      (FpqcHomDescent.unique cH.quotient (f ≫ cG.quotient)
        (cH.kernel_comp cG f) (CommGroupScheme.groupHom d) hd)

/-- The morphism induced on any two supplied actual cocenters. -/
def map (hH : IsConnectedReductive H) (f : H ⟶ G) : cH.torus ⟶ cG.torus :=
  Classical.choose (cH.existsUnique_map cG hH f)

/-- The induced map commutes with the actual quotient morphisms. -/
@[reassoc]
theorem quotient_map (hH : IsConnectedReductive H) (f : H ⟶ G) :
    cH.quotient ≫ CommGroupScheme.groupHom (cH.map cG hH f) =
      f ≫ cG.quotient :=
  (Classical.choose_spec (cH.existsUnique_map cG hH f)).1

/-- A commuting quotient square determines the map of cocenters. -/
theorem map_unique (hH : IsConnectedReductive H) (f : H ⟶ G)
    (d : cH.torus ⟶ cG.torus)
    (hd : cH.quotient ≫ CommGroupScheme.groupHom d = f ≫ cG.quotient) :
    d = cH.map cG hH f :=
  (Classical.choose_spec (cH.existsUnique_map cG hH f)).2 d hd

end Cocenter
end Langlands.Geometry.Building.Kottwitz
