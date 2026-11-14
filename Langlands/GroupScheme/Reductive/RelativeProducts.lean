import Langlands.GroupScheme.Reductive.DirectProductProof
import Langlands.GroupScheme.SmoothProducts

/-! # Products of reductive group schemes over an arbitrary base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- A binary product of reductive group schemes is reductive over the same base. -/
theorem IsReductive.tensor (hG : IsReductive G) (hH : IsReductive H) :
    IsReductive (G ⊗ H) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom H.X.hom := hH.isAffineHom
  refine ⟨smooth_tensor G.X H.X hG.smooth hH.smooth, ?_, fun s => ?_⟩
  · change IsAffineHom (pullback.fst G.X.hom H.X.hom ≫ G.X.hom)
    let : IsAffineHom (pullback.fst G.X.hom H.X.hom) :=
      MorphismProperty.pullback_fst _ _ hH.isAffineHom
    infer_instance
  · exact IsPseudoReductive.of_iso (baseChangeTensorIso (geometricPoint S s) G H)
      (DirectProduct.isPseudoReductive_tensor (hG.geometricFiber s) (hH.geometricFiber s))

/-- Binary products preserve reductivity over every base scheme, in every universe. -/
def RelativeReductiveProductStatement : Prop :=
  ∀ (S : Scheme.{u}) (G H : GroupScheme S),
    IsReductive G → IsReductive H → IsReductive (G ⊗ H)

theorem relativeReductiveProduct : RelativeReductiveProductStatement.{u} :=
  fun _ _ _ hG hH => hG.tensor hH

end Langlands.GroupScheme
