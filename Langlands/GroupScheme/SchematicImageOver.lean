import Langlands.AlgebraicGeometry.Picard.GenericSectionSchematicClosure
import Langlands.GroupScheme.AlgClosedFiniteKernelHomIsogeny
import Langlands.GroupScheme.ImageGenerationDominant
import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.FunctionDescent

/-! # Schematic images of morphisms over a scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.SchematicImageOver

variable {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)

/-- The scheme-theoretic image viewed over the original base. -/
def image : Over S := Over.mk (f.left.imageι ≫ Y.hom)

/-- The closed immersion of the image into the original target. -/
def inclusion : image f ⟶ Y := Over.homMk f.left.imageι rfl

/-- The original morphism with codomain restricted to its image. -/
def projection : X ⟶ image f :=
  Over.homMk f.left.toImage (by
    change f.left.toImage ≫ (f.left.imageι ≫ Y.hom) = X.hom
    rw [f.left.toImage_imageι_assoc, Over.w])

@[reassoc (attr := simp)]
theorem projection_inclusion : projection f ≫ inclusion f = f :=
  Over.OverMorphism.ext f.left.toImage_imageι

instance : IsClosedImmersion (inclusion f).left :=
  inferInstanceAs (IsClosedImmersion f.left.imageι)

instance : Mono (inclusion f) := Over.mono_of_mono_left _

instance [QuasiCompact f.left] : QuasiCompact (projection f).left :=
  inferInstanceAs (QuasiCompact f.left.toImage)

instance [QuasiCompact f.left] : IsSchemeTheoreticallyDominant (projection f).left :=
  Langlands.AlgebraicGeometry.toImage_schemeTheoreticallyDominant f.left

/-- A quasi-compact flat surjection has zero scheme-theoretic kernel. -/
theorem dominant_of_flat_surjective {A B : Scheme.{u}} (p : A ⟶ B)
    [QuasiCompact p] [Flat p] [Surjective p] : IsSchemeTheoreticallyDominant p := by
  rw [isSchemeTheoreticallyDominant_iff]
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top id (iSup_affineOpens_eq_top B) fun V => ?_
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).1
    (Langlands.Scheme.UnitCocycleDescent.app_injective p V.1)

/-- Two closed schematically dominant factorizations of the same map are isomorphic
over the source and target. -/
theorem exists_iso_of_dominant_factorizations {A B W Z : Over S}
    (p : Z ⟶ A) (q : Z ⟶ B) (i : A ⟶ W) (j : B ⟶ W)
    [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    [IsSchemeTheoreticallyDominant p.left] [IsSchemeTheoreticallyDominant q.left]
    (h : p ≫ i = q ≫ j) :
    ∃ e : A ≅ B, e.hom ≫ j = i ∧ p ≫ e.hom = q := by
  have : Mono i := Over.mono_of_mono_left _
  have : Mono j := Over.mono_of_mono_left _
  obtain ⟨a, ha⟩ := exists_over_factor_of_schematic_precomp j p i q h
  obtain ⟨b, hb⟩ := exists_over_factor_of_schematic_precomp i q j p h.symm
  refine ⟨⟨a, b, ?_, ?_⟩, ha, ?_⟩
  · apply (cancel_mono i).mp
    rw [Category.assoc, hb, ha, Category.id_comp]
  · apply (cancel_mono j).mp
    rw [Category.assoc, ha, hb, Category.id_comp]
  · apply (cancel_mono j).mp
    rwa [Category.assoc, ha]

end Langlands.GroupScheme.SchematicImageOver
