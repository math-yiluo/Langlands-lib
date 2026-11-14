import Langlands.GroupScheme.HomScheme.PointedEtaleLift
import Langlands.GroupScheme.HomScheme.FibreComparison
import Langlands.GroupScheme.Reductive.PinningScalarCoherence

/-! # Pointed etale lifting of actual cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme

variable {S U K : Scheme.{u}} {G : GroupScheme S}

/-- Normalize a relative homomorphism with multiplicative source into an
actual cocharacter over its test base. -/
def cocharacterOfRelativeHom (p : U ⟶ S)
    (i : RelativeHom (Gm S).toGrp G (Over.mk p)) :
    (Gm U).toGrp ⟶ (baseChange p).obj G :=
  (Gm.baseChangeIso p).inv ≫ i

/-- Exact relative Hom evaluation becomes exact recovery of the normalized
cocharacter through the canonical iterated-pullback comparison. -/
theorem cocharacterOfRelativeHom_recovers
    (p : U ⟶ S) (c : K ⟶ S) (b : K ⟶ U) (hb : b ≫ p = c)
    (i : RelativeHom (Gm S).toGrp G (Over.mk p))
    (χ₀ : (Gm K).toGrp ⟶ (baseChange c).obj G)
    (hi : evaluate (show Over.mk c ⟶ Over.mk p from Over.homMk b hb) i =
      (Gm.baseChangeIso c).hom ≫ χ₀) :
    Dynamic.baseChangeCocharacter b (cocharacterOfRelativeHom p i) ≫
      (Descent.pullbackComparison p b c hb G).hom = χ₀ := by
  have h := evaluate_comparison
    (show Over.mk c ⟶ Over.mk p from Over.homMk b hb) i
  rw [hi] at h
  have hsrc := Descent.gmBaseChange_tower p b c hb
  apply (cancel_epi ((baseChange b).map (Gm.baseChangeIso p).hom ≫
    (Gm.baseChangeIso b).hom)).mp
  dsimp only [Dynamic.baseChangeCocharacter, cocharacterOfRelativeHom]
  rw [Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [← Category.assoc, hsrc]
  simpa only [Over.Hom.left, Over.mk_hom, Over.homMk_left, Category.assoc] using h

/-- An actual cocharacter lift over a pointed etale neighbourhood, retaining
the exact equality with the specified residue-fibre cocharacter. -/
structure PointedEtaleCocharacterLiftData
    (S : Scheme.{u}) (G : GroupScheme S) (s : S)
    (χ₀ : (Gm (Spec (S.residueField s))).toGrp ⟶
      (baseChange (S.fromSpecResidueField s)).obj G) where
  neighbourhood : Scheme.{u}
  projection : neighbourhood ⟶ S
  etale : Etale projection
  residuePoint : Spec (S.residueField s) ⟶ neighbourhood
  residue_over : residuePoint ≫ projection = S.fromSpecResidueField s
  cocharacter : (Gm neighbourhood).toGrp ⟶ (baseChange projection).obj G
  recovers : Dynamic.baseChangeCocharacter residuePoint cocharacter ≫
    (Descent.pullbackComparison projection residuePoint
      (S.fromSpecResidueField s) residue_over G).hom = χ₀

/-- Lift any prescribed residue cocharacter of a smooth affine group over a
pointed etale neighbourhood. -/
def pointedEtaleCocharacterLift
    (S : Scheme.{u}) (G : GroupScheme S)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (s : S)
    (χ₀ : (Gm (Spec (S.residueField s))).toGrp ⟶
      (baseChange (S.fromSpecResidueField s)).obj G) :
    PointedEtaleCocharacterLiftData S G s χ₀ :=
  let D := pointedEtaleHomLift S (Gm S).toGrp G (isSplitTorus_gm (S := S)) s
    ((Gm.baseChangeIso (S.fromSpecResidueField s)).hom ≫ χ₀)
  { neighbourhood := D.neighbourhood
    projection := D.projection
    etale := D.etale
    residuePoint := D.residuePoint
    residue_over := D.residue_over
    cocharacter := cocharacterOfRelativeHom D.projection D.homomorphism
    recovers := cocharacterOfRelativeHom_recovers D.projection
      (S.fromSpecResidueField s) D.residuePoint D.residue_over
      D.homomorphism χ₀ D.recovers }

end Langlands.GroupScheme.HomScheme
