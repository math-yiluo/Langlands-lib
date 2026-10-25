import Langlands.GroupScheme.HomConjugacy
import Langlands.GroupScheme.CocharacterTransport

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
universe u
variable {S S' : Scheme.{u}} {G H J : GroupScheme S}

/-- Inner conjugacy is preserved by precomposition with a group-scheme morphism. -/
theorem HomConjugate.precomp {χ ψ : H ⟶ G} (h : HomConjugate χ ψ) (f : J ⟶ H) :
    HomConjugate (f ≫ χ) (f ≫ ψ) := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, by rw [Category.assoc, hg]⟩

/-- A group-scheme morphism sends a base point's constant family to the image family. -/
theorem constantPoint_comp (f : G ⟶ H) (g : Over.mk (𝟙 S) ⟶ G.X) (T : Over S) :
    G.constantPoint g T ≫ f.hom.hom = H.constantPoint (g ≫ f.hom.hom) T :=
  Category.assoc _ _ _

/-- Inner conjugacy is preserved by postcomposition with a group-scheme morphism. -/
theorem HomConjugate.postcomp {χ ψ : J ⟶ G} (h : HomConjugate χ ψ) (f : G ⟶ H) :
    HomConjugate (χ ≫ f) (ψ ≫ f) := by
  obtain ⟨g, hg⟩ := (homConjugate_iff_points χ ψ).mp h
  apply (homConjugate_iff_points _ _).mpr
  refine ⟨g ≫ f.hom.hom, fun T x => ?_⟩
  have hm := congrArg (fun y : T ⟶ G.X => (yonedaGrp.map f).app (op T) y) (hg T x)
  change ((yonedaGrp.map f).app (op T)).hom _ =
    ((yonedaGrp.map f).app (op T)).hom _ at hm
  rw [map_mul, map_mul, map_inv] at hm
  change (G.constantPoint g T ≫ f.hom.hom) * ((x ≫ χ.hom.hom) ≫ f.hom.hom) *
    (G.constantPoint g T ≫ f.hom.hom)⁻¹ = (x ≫ ψ.hom.hom) ≫ f.hom.hom at hm
  simpa only [Grp.comp_hom_hom, Category.assoc, constantPoint_comp] using hm

/-- Pull back an actual base point along a morphism of base schemes. -/
def baseChangeBasePoint (b : S' ⟶ S) (G : GroupScheme S)
    (g : Over.mk (𝟙 S) ⟶ G.X) :
    Over.mk (𝟙 S') ⟶ ((Over.pullback b).mapGrp.obj G).X :=
  (baseChangeBasePointsEquiv b G).symm (G.constantPoint g (Over.mk b))

/-- The pulled-back base point projects to the original section composed with the base map. -/
theorem baseChangeBasePoint_fst (b : S' ⟶ S) (G : GroupScheme S)
    (g : Over.mk (𝟙 S) ⟶ G.X) :
    (baseChangeBasePoint b G g).left ≫ pullback.fst G.X.hom b = b ≫ g.left := by
  calc
    _ = (baseChangeBasePointsEquiv b G (baseChangeBasePoint b G g)).left :=
      (baseChangeBasePointsEquiv_left b G _).symm
    _ = (G.constantPoint g (Over.mk b)).left :=
      congrArg (fun x : Over.mk b ⟶ G.X => x.left)
        ((baseChangeBasePointsEquiv b G).apply_symm_apply _)
    _ = b ≫ g.left := rfl

/-- Pullback of the constant point family is the constant family of the pulled-back point. -/
theorem baseChangePointsEquiv_constantPoint (b : S' ⟶ S) (G : GroupScheme S)
    (g : Over.mk (𝟙 S) ⟶ G.X) (T : Over S') :
    baseChangePointsEquiv b G T
      (constantPoint ((Over.pullback b).mapGrp.obj G) (baseChangeBasePoint b G g) T) =
        G.constantPoint g ((Over.map b).obj T) := by
  apply Over.OverMorphism.ext
  change (T.hom ≫ (baseChangeBasePoint b G g).left) ≫ pullback.fst G.X.hom b =
    (T.hom ≫ b) ≫ g.left
  rw [Category.assoc, baseChangeBasePoint_fst, Category.assoc]

/-- Actual base change preserves inner conjugacy, with the pulled-back base point. -/
theorem HomConjugate.baseChange {χ ψ : H ⟶ G} (h : HomConjugate χ ψ) (b : S' ⟶ S) :
    HomConjugate ((Over.pullback b).mapGrp.map χ) ((Over.pullback b).mapGrp.map ψ) := by
  obtain ⟨g, hg⟩ := (homConjugate_iff_points χ ψ).mp h
  apply (homConjugate_iff_points _ _).mpr
  refine ⟨baseChangeBasePoint b G g, fun T x => ?_⟩
  apply (baseChangePointsEquiv b G T).injective
  rw [map_mul, map_mul, map_inv, baseChangePointsEquiv_constantPoint,
    baseChangePointsEquiv_comp, baseChangePointsEquiv_comp]
  exact hg ((Over.map b).obj T) (baseChangePointsEquiv b H T x)

/-- Canonical descent transport of actual cocharacters preserves inner conjugacy. -/
theorem HomConjugate.transportCocharacter {B : Scheme.{u}}
    (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b) (G : GroupScheme B)
    {χ ψ : (Gm S).toGrp ⟶ (Over.pullback b).mapGrp.obj G}
    (h : HomConjugate χ ψ) :
    HomConjugate (transportCocharacter b a ha G χ) (transportCocharacter b a ha G ψ) :=
  ((h.baseChange a).postcomp (descentBaseChangeIso b a ha G).hom).precomp
    (Gm.baseChangeIso a).inv

end Langlands.GroupScheme
