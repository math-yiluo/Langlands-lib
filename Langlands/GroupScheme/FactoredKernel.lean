import Langlands.AbelianScheme.GroupScheme
import Langlands.AbelianScheme.Kernel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Actual kernels of factored group-scheme homomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace FactoredKernel

variable {S : Scheme.{u}} {G Q A : GroupScheme S}
    (f : G ⟶ A) (q : G ⟶ Q) (h : Q ⟶ A) (fac : q ≫ h = f)

/-- The homomorphism between the actual kernels of a factored homomorphism. -/
def map : kernel f ⟶ kernel h :=
  pullback.lift (kernelι f ≫ q) (pullback.snd f (kernelUnit A)) (by
    rw [Category.assoc, fac]
    exact pullback.condition)

@[reassoc (attr := simp)]
theorem map_comp : map f q h fac ≫ kernelι h = kernelι f ≫ q :=
  pullback.lift_fst _ _ _

/-- The full kernel of the original map is the inverse image of the full
kernel of its descended map. -/
theorem isPullback :
    IsPullback (kernelι f).hom.hom (map f q h fac).hom.hom
      q.hom.hom (kernelι h).hom.hom := by
  have hs : IsPullback (kernelι f).hom.hom
      ((map f q h fac).hom.hom ≫ toUnit (kernel h).X)
      (q.hom.hom ≫ h.hom.hom) η[A.X] := by
    simpa only [comp_toUnit, ← Grp.comp_hom_hom, fac] using kernel_isPullback f
  exact hs.of_bot (congrArg (fun z => z.hom.hom) (map_comp f q h fac)).symm
    (kernel_isPullback h)

theorem isPullback_scheme :
    IsPullback (kernelι f).hom.hom.left (map f q h fac).hom.hom.left
      q.hom.hom.left (kernelι h).hom.hom.left :=
  (isPullback f q h fac).map (Over.forget S)

instance smooth_map [Smooth q.hom.hom.left] :
    Smooth (map f q h fac).hom.hom.left :=
  MorphismProperty.of_isPullback (isPullback_scheme f q h fac) inferInstance

instance surjective_map [Surjective q.hom.hom.left] :
    Surjective (map f q h fac).hom.hom.left :=
  MorphismProperty.of_isPullback (isPullback_scheme f q h fac) inferInstance

end FactoredKernel

end Langlands.GroupScheme
