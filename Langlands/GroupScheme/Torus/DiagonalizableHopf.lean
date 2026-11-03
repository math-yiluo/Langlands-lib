import Langlands.GroupScheme.Torus.Diagonalizable
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Diagonalizable

variable (R : CommRingCat.{u}) (Λ : Type u) [AddCommGroup Λ]

/-- The standard Hopf algebra on the additive group algebra. -/
abbrev hopfAlgebra : CommHopfAlgCat.{u} R :=
  CommHopfAlgCat.of R (AddMonoidAlgebra R Λ)

/-- The standard Hopf counit classifies the identity character. -/
theorem counit_eq :
    CommAlgCat.ofHom (Bialgebra.counitAlgHom R (AddMonoidAlgebra R Λ)) =
      Corepresented.LinearEmbedding.counit (grpCorepresentation R Λ) := by
  apply CommAlgCat.hom_ext
  apply AddMonoidAlgebra.algHom_ext
  · intro γ
    change (Bialgebra.counitAlgHom R (AddMonoidAlgebra R Λ))
        (AddMonoidAlgebra.single γ 1) =
      (lift R Λ (1 : Multiplicative Λ →* (CommAlgCat.of R R)ˣ)).hom
        (AddMonoidAlgebra.single γ 1)
    rw [lift_single]
    simp
  · exact Subsingleton.elim _ _

/-- The standard Hopf comultiplication classifies the product character. -/
theorem comul_eq :
    CommAlgCat.ofHom (Bialgebra.comulAlgHom R (AddMonoidAlgebra R Λ)) =
      Corepresented.LinearEmbedding.comul (grpCorepresentation R Λ) := by
  apply CommAlgCat.hom_ext
  apply AddMonoidAlgebra.algHom_ext
  · intro γ
    rw [comul_single]
    simp
  · exact Subsingleton.elim _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Identity on the group algebra compares the two cogroup structures. -/
def hopfCogroupIso :
    ((commHopfAlgCatEquivCogrpCommAlgCat R).functor.obj (hopfAlgebra R Λ)).unop ≅
      Corepresented.cogroup (functor R Λ) (grpCorepresentation R Λ) := by
  refine Grp.mkIso (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id]
    apply Quiver.Hom.unop_inj
    exact counit_eq R Λ
  · simp only [Iso.refl_hom, MonoidalCategory.id_tensorHom_id, Category.comp_id,
      Category.id_comp]
    apply Quiver.Hom.unop_inj
    exact comul_eq R Λ

/-- The standard Hopf spectrum is the existing diagonalizable group scheme. -/
def hopfSpecIso : (hopfSpec R).obj (op (hopfAlgebra R Λ)) ≅ (groupScheme R Λ).toGrp :=
  (algSpec R).mapGrp.mapIso (hopfCogroupIso R Λ)

end Langlands.GroupScheme.Diagonalizable
