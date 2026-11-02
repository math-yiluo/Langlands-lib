import Langlands.AlgebraicGeometry.Modules.LineBundleSectionClearingProof
import Langlands.AlgebraicGeometry.Modules.CoherentEulerSequence
import Langlands.AlgebraicGeometry.ModuleLinear

/-! # Multiplication by a section of a twisting line bundle -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory
open Langlands.Scheme.Modules Langlands.SchemeModule Langlands.SchemeModule.SectionClearing

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules.SerreVanishing

section UnitEnd

variable {Y : Scheme.{u}}

local instance serreMulMonoidal : MonoidalCategory Y.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} Y.presheaf))

/-- Tensoring with an endomorphism of the structure sheaf is, through the right unitor,
multiplication by its coefficient. -/
lemma tensorMap_id_unitEnd (G : Y.Modules) (φ : structureSheaf Y ⟶ structureSheaf Y) :
    tensorMap (𝟙 G) φ ≫ (tensorRightUnitor G).hom =
      (tensorRightUnitor G).hom ≫ (unitEndCoefficient φ ⊤ • 𝟙 G) := by
  have hpre : (G.val ◁ φ.val) ≫ (ρ_ G.val).hom =
      (ρ_ G.val).hom ≫ (unitEndCoefficient φ ⊤ • 𝟙 G).val := by
    ext U : 1
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro g a
    change φ.app U.unop a • g = restrictScalar U.unop (unitEndCoefficient φ ⊤) • (a • g)
    have h1 := unitEndCoefficient_app φ U.unop a
    rw [unitEndCoefficient_res φ (homOfLE (le_top : U.unop ≤ ⊤))] at h1
    erw [h1, mul_smul]
    exact @smul_comm Γ(Y, U.unop) Γ(Y, U.unop) Γ(G, U.unop) _ _ _ _ _ g
  change (sheafify Y).map (𝟙 G.val ⊗ₘ φ.val) ≫
      ((sheafify Y).map (ρ_ G.val).hom ≫ (sheafifyForgetIso Y).hom.app G) =
    ((sheafify Y).map (ρ_ G.val).hom ≫ (sheafifyForgetIso Y).hom.app G) ≫
      (unitEndCoefficient φ ⊤ • 𝟙 G)
  erw [← Category.assoc, ← Functor.map_comp, id_tensorHom, hpre, Functor.map_comp,
    Category.assoc, Category.assoc]
  exact congrArg ((sheafify Y).map (ρ_ G.val).hom ≫ ·)
    ((sheafifyForgetIso Y).hom.naturality _)

end UnitEnd

end Langlands.AlgebraicGeometry.Modules.SerreVanishing
