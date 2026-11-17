import Langlands.GroupScheme.KernelTriviality
import Langlands.AbelianScheme.TorsionFiniteEtale
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Presentation and affine geometry of full group-scheme kernels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- A group scheme's unit section is an immersion, without a separatedness hypothesis. -/
theorem unit_isImmersion (G : GroupScheme S) : IsImmersion η[G.X].left := by
  have : IsImmersion (η[G.X].left ≫ G.X.hom) := by
    rw [η[G.X].w]
    change IsImmersion (𝟙 S)
    infer_instance
  exact IsImmersion.of_comp _ G.X.hom

/-- The full kernel is always an immersed subgroup, even for a non-separated target. -/
theorem kernelι_isImmersion (f : H ⟶ G) : IsImmersion (kernelι f).hom.hom.left := by
  have : IsImmersion η[G.X].left := unit_isImmersion G
  exact MorphismProperty.of_isPullback (kernel_isPullback_scheme f).flip inferInstance

/-- Kernels are locally of finite presentation if the source is and either the base
is locally noetherian or the target is locally of finite type. -/
theorem locallyOfFinitePresentation_kernel_of_source (f : H ⟶ G)
    [LocallyOfFinitePresentation H.X.hom]
    (hbase : IsLocallyNoetherian S ∨ LocallyOfFiniteType G.X.hom) :
    LocallyOfFinitePresentation (kernel f).X.hom := by
  rcases hbase with hS | hG
  · let := hS
    have : IsImmersion (kernelι f).hom.hom.left := kernelι_isImmersion f
    have : LocallyOfFiniteType (kernel f).X.hom := by
      rw [← Over.w (kernelι f).hom.hom]
      infer_instance
    infer_instance
  · let := hG
    have : LocallyOfFinitePresentation (f.hom.hom.left ≫ G.X.hom) := by
      rw [Over.w]
      infer_instance
    have : LocallyOfFinitePresentation f.hom.hom.left :=
      Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp _ G.X.hom
    exact MorphismProperty.of_isPullback (kernel_isPullback_scheme f) inferInstance

/-- A closed full kernel in an affine source is affine over the base. -/
theorem isAffineHom_kernel_of_closed (f : H ⟶ G) [IsAffineHom H.X.hom]
    [IsClosedImmersion (kernelι f).hom.hom.left] :
    IsAffineHom (kernel f).X.hom := by
  rw [← Over.w (kernelι f).hom.hom]
  infer_instance

end Langlands.GroupScheme
