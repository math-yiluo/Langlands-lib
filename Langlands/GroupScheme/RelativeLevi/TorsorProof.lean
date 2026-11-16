import Langlands.GroupScheme.RelativeLevi.TorsorModelConstruction
import Langlands.GroupScheme.RelativeLevi.ModuliEtaleSheaf

/-! # The torsor of actual relative Levi subgroup images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open RelativeLevi

/-- Assemble the relative Levi torsor from sheaf descent for its actual
image-valued presheaf. The two premises isolate the sheaf descent used in the construction. -/
theorem relativeLeviTorsor_of_sheaf
    (hZ : ∀ (B : Scheme.{u}) (H Q R : GroupScheme B) (j : Q ⟶ H) (s : R ⟶ Q)
      (hH : IsReductive H) (hj : IsRelativeParabolicSubgroup j)
      (_hs : IsRelativeUnipotentRadical s),
      Presieve.IsSheaf (Scheme.zariskiTopology.over B) (moduliFunctorOfParabolic hj hH))
    (hE : ∀ (B : Scheme.{u}) (H Q R : GroupScheme B) (j : Q ⟶ H) (s : R ⟶ Q)
      (hH : IsReductive H) (hj : IsRelativeParabolicSubgroup j)
      (_hs : IsRelativeUnipotentRadical s)
      {V W : Over B} (p : V ⟶ W) [Etale p.left] [Surjective p.left],
      Presieve.IsSheafFor (moduliFunctorOfParabolic hj hH) (.singleton p)) :
    RelativeLeviTorsorStatement.{u} := by
  intro S G P U i r hG hi hr
  let M := moduliModelOfAffineModels hG hi
    ((isSheaf_iff_isSheaf_of_type _ _).mpr (hZ S G P U i r hG hi hr))
    (fun {B} b _ => affineModuliModel
      (hG.baseChange b) (hi.baseChange hG b) (hr.baseChange_parabolic hi hG b)
      (hZ B ((baseChange b).obj G) ((baseChange b).obj P) ((baseChange b).obj U)
        ((baseChange b).map i) ((baseChange b).map r)
        (hG.baseChange b) (hi.baseChange hG b) (hr.baseChange_parabolic hi hG b))
      (hE B ((baseChange b).obj G) ((baseChange b).obj P) ((baseChange b).obj U)
        ((baseChange b).map i) ((baseChange b).map r)
        (hG.baseChange b) (hi.baseChange hG b) (hr.baseChange_parabolic hi hG b)))
  exact exists_torsor_of_smoothAffineModel i r hG hi hr M

/-- The actual relative Levi moduli is an fpqc torsor under the supplied
unipotent radical, with its conjugation-equivariant representing correspondence. -/
theorem relativeLeviTorsor : RelativeLeviTorsorStatement.{u} := by
  apply relativeLeviTorsor_of_sheaf
  · intro S G P U i r hG hi hr
    exact (isSheaf_iff_isSheaf_of_type _ _).mp
      (moduliFunctor_isSheaf_zariski i r hG hi
        (fun b => hr.baseChange_parabolic hi hG b)
        (restrictionStable_of_parabolic hi hG))
  · intro S G P U i r hG hi hr V W p _ _
    exact moduliFunctor_isSheafFor_etale i r hG hi
      (fun b => hr.baseChange_parabolic hi hG b)
      (restrictionStable_of_parabolic hi hG) p

end Langlands.GroupScheme
