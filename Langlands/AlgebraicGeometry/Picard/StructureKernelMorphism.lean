import Langlands.AlgebraicGeometry.Picard.SquareZeroAmbientObstructionNaturality
import Langlands.AlgebraicGeometry.Picard.SquareZeroUnitNaturality

/-! # Actual ideal maps for commuting squares of scheme morphisms -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.StructureKernelMorphism

open StructureKernelModule Langlands.Scheme.Modules

variable {X X' Y Y' : Scheme.{u}} (f : X' ⟶ X)
  (i : Y ⟶ X) (i' : Y' ⟶ X') (g : Y' ⟶ Y)
  (w : i' ≫ f = g ≫ i)

private lemma nestedMap_ι :
    SquareZeroUnitNaturality.kernelModuleMap i g ≫ kernelModuleι (g ≫ i) =
      kernelModuleι i := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  rfl

private lemma ambientMap_ι :
    SquareZeroAmbientObstructionNaturality.kernelModuleMap f i' ≫
        (Scheme.Modules.pushforward f).map (kernelModuleι i') =
      kernelModuleι (i' ≫ f) ≫ unitToPushforwardUnit f := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  rfl

private lemma transport_ι {a b : Y' ⟶ X} (h : a = b) :
    eqToHom (congrArg kernelModule h) ≫ kernelModuleι b = kernelModuleι a := by
  cases h
  simp

/-- The actual map on ideal modules induced by a commuting square. It is
constructed by inclusion into the composite kernel followed by the ambient
structure map, with transport along the given equality of scheme arrows. -/
def kernelModuleMap :
    kernelModule i ⟶ (Scheme.Modules.pushforward f).obj (kernelModule i') :=
  SquareZeroUnitNaturality.kernelModuleMap i g ≫
    eqToHom (congrArg kernelModule w.symm) ≫
      SquareZeroAmbientObstructionNaturality.kernelModuleMap f i'

/-- The induced ideal map agrees with the actual structure homomorphism. -/
@[reassoc]
lemma kernelModuleMap_ι :
    kernelModuleMap f i i' g w ≫
        (Scheme.Modules.pushforward f).map (kernelModuleι i') =
      kernelModuleι i ≫ unitToPushforwardUnit f := by
  unfold kernelModuleMap
  rw [Category.assoc, Category.assoc, ambientMap_ι]
  rw [← Category.assoc (eqToHom (congrArg kernelModule w.symm)), transport_ι w.symm]
  rw [← Category.assoc, nestedMap_ι]

/-- Compatibility with the ideal inclusions uniquely determines the induced map. -/
lemma kernelModuleMap_unique
    (k : kernelModule i ⟶ (Scheme.Modules.pushforward f).obj (kernelModule i'))
    (hk : k ≫ (Scheme.Modules.pushforward f).map (kernelModuleι i') =
      kernelModuleι i ≫ unitToPushforwardUnit f) :
    k = kernelModuleMap f i i' g w := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  apply Subtype.ext
  exact congrArg (fun q : kernelModule i ⟶
    (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X'.ringCatSheaf) => q.app U a)
    (hk.trans (kernelModuleMap_ι f i i' g w).symm)

end Langlands.AlgebraicGeometry.Picard.StructureKernelMorphism
