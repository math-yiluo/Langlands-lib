import Langlands.AlgebraicGeometry.Picard.LineBundleDualSectionEvaluation
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.ModuleDualPullbackLocalFree

/-! # Coherent pullback of actual dual line bundles -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.LineBundle

open Langlands.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- Transport an actual line-bundle isomorphism to the duals, in the same direction. -/
def dualIso {L M : LineBundle X} (e : L ≅ M) : L.dual ≅ M.dual :=
  ObjectProperty.isoMk _
    { hom := dualMap e.inv.hom
      inv := dualMap e.hom.hom
      hom_inv_id := by rw [← dualMap_comp]; simp [dual]
      inv_hom_id := by rw [← dualMap_comp]; simp [dual] }

@[simp]
lemma dualIso_refl (L : LineBundle X) : dualIso (Iso.refl L) = Iso.refl L.dual := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact dualMap_id L.obj

lemma dualIso_comp {L M N : LineBundle X} (e : L ≅ M) (f : M ≅ N) :
    dualIso e ≪≫ dualIso f = dualIso (e ≪≫ f) := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact (dualMap_comp f.inv.hom e.inv.hom).symm

@[simp]
lemma dualIso_symm {L M : LineBundle X} (e : L ≅ M) :
    dualIso e.symm = (dualIso e).symm := by
  rfl

/-- The canonical dual-pullback map is invertible for any actual line bundle. -/
instance isIso_dualPullbackComparison (f : X ⟶ Y) (L : LineBundle Y) :
    IsIso (dualPullbackComparison f L.obj) := by
  apply isIso_dualPullbackComparison_of_local
  intro y
  obtain ⟨U, hy, ⟨e⟩⟩ := L.property y
  refine ⟨U, hy, fun g => ?_⟩
  exact isIso_dualPullbackComparison_of_iso g e.symm
    (isIso_dualPullbackComparison_unit g)

/-- Pullback of the internal dual compared with the dual of the actual pullback. -/
def dualPullbackIso (f : X ⟶ Y) (L : LineBundle Y) :
    (pullback f).obj L.dual ≅ ((pullback f).obj L).dual :=
  ObjectProperty.isoMk _ (asIso (dualPullbackComparison f L.obj))

/-- The dual comparison is natural for actual line-bundle isomorphisms. -/
lemma dualPullbackIso_naturality (f : X ⟶ Y) {L M : LineBundle Y} (e : L ≅ M) :
    (pullback f).mapIso (dualIso e) ≪≫ dualPullbackIso f M =
      dualPullbackIso f L ≪≫ dualIso ((pullback f).mapIso e) := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact dualPullbackComparison_naturality f e.inv.hom

/-- Dual pullback respects the identity morphism of the base. -/
lemma dualPullbackIso_identity (L : LineBundle X) :
    dualPullbackIso (𝟙 X) L ≪≫ dualIso ((pullbackId X).app L) =
      (pullbackId X).app L.dual := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  change dualPullbackComparison (𝟙 X) L.obj ≫
      dualMap ((Scheme.Modules.pullbackId X).inv.app L.obj) =
    (Scheme.Modules.pullbackId X).hom.app (Langlands.Scheme.Modules.dual L.obj)
  rw [dualPullbackComparison_id, Category.assoc, ← dualMap_comp,
    Iso.inv_hom_id_app, dualMap_id]
  exact Category.comp_id _

/-- Dual pullback respects composition through the actual canonical comparisons. -/
lemma dualPullbackIso_composition (f : X ⟶ Y) (g : Y ⟶ Z) (L : LineBundle Z) :
    (pullback f).mapIso (dualPullbackIso g L) ≪≫
        dualPullbackIso f ((pullback g).obj L) ≪≫ dualIso ((pullbackComp f g).app L) =
      (pullbackComp f g).app L.dual ≪≫ dualPullbackIso (f ≫ g) L := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  change (Scheme.Modules.pullback f).map (dualPullbackComparison g L.obj) ≫
      dualPullbackComparison f ((Scheme.Modules.pullback g).obj L.obj) ≫
      dualMap ((Scheme.Modules.pullbackComp f g).inv.app L.obj) =
    (Scheme.Modules.pullbackComp f g).hom.app (Langlands.Scheme.Modules.dual L.obj) ≫
      dualPullbackComparison (f ≫ g) L.obj
  rw [dualPullbackComparison_comp]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

end Langlands.AlgebraicGeometry.Picard.LineBundle
