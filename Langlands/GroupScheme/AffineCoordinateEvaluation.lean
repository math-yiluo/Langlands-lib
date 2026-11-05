import Langlands.GroupScheme.Unipotent.BaseChange
import Langlands.GroupScheme.AffineHomImageHopfAdapter
import Langlands.GroupScheme.AffineLinearEmbedding.Coordinate

/-! # Evaluation of affine Hopf coordinates on arbitrary test schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace Corepresented

variable {R : CommRingCat.{u}} (C : Grp (CommAlgCat R)ᵒᵖ)

/-- Cogroup recovery leaves the underlying algebra map unchanged. -/
theorem cogroupRecoveryIso_hom_hom_hom :
    (cogroupRecoveryIso C).hom.hom.hom = 𝟙 C.X := rfl

/-- The inverse recovery map also leaves the underlying algebra unchanged. -/
theorem cogroupRecoveryIso_inv_hom_hom :
    (cogroupRecoveryIso C).inv.hom.hom = 𝟙 C.X := rfl

end Corepresented

namespace AffineCoordinates

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffine G.X.left]

set_option backward.isDefEq.respectTransparency false in
/-- The corepresented and chosen affine coordinates use the same underlying scheme map. -/
theorem groupSchemeIso_hom_hom_hom :
    (groupSchemeIso G).hom.hom.hom = (coordinateCogroupIso G).hom.hom.hom := by
  change (algSpec R).map (Corepresented.cogroupRecoveryIso (coordinateCogroup G)).hom.hom.hom
    ≫ _ = _
  rw [Corepresented.cogroupRecoveryIso_hom_hom_hom, CategoryTheory.Functor.map_id]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
/-- The inverse corepresented coordinate map is the chosen affine coordinate map. -/
theorem groupSchemeIso_inv_hom_hom :
    (groupSchemeIso G).inv.hom.hom = (coordinateCogroupIso G).inv.hom.hom := by
  change _ ≫ (algSpec R).map (Corepresented.cogroupRecoveryIso (coordinateCogroup G)).inv.hom.hom
    = _
  rw [Corepresented.cogroupRecoveryIso_inv_hom_hom, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
/-- Hopf spectrum and the chosen affine coordinates use the same underlying map. -/
theorem hopfSpecIso_hom_hom_hom :
    (hopfSpecIso G).hom.hom.hom = (coordinateCogroupIso G).hom.hom.hom := by
  change (algSpec R).map (𝟙 _) ≫ _ = _
  rw [CategoryTheory.Functor.map_id]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
/-- The inverse Hopf-spectrum coordinate map is the chosen affine coordinate map. -/
theorem hopfSpecIso_inv_hom_hom :
    (hopfSpecIso G).inv.hom.hom = (coordinateCogroupIso G).inv.hom.hom := by
  change _ ≫ (algSpec R).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- The coordinate coalgebra comultiplication equals that used by the regular representation. -/
theorem corepresentation_comul :
    @Coalgebra.comul R (algebra G) _ _ _
        (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra.toCoalgebraStruct =
      @Coalgebra.comul R (hopfAlgebra G) _ _ _ inferInstance := by
  change (AffineLinearEmbedding.comul (corepresentation G)).toLinearMap =
    μ[(coordinateCogroup G).X].unop.hom.toLinearMap
  exact congrArg AlgHom.toLinearMap
    (Unipotent.comul_cogroupCorepresentation (coordinateCogroup G))

/-- The coordinate coalgebra counit equals that used by the regular representation. -/
theorem corepresentation_counit :
    @Coalgebra.counit R (algebra G) _ _ _
        (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra.toCoalgebraStruct =
      @Coalgebra.counit R (hopfAlgebra G) _ _ _ inferInstance := by
  change (AffineLinearEmbedding.counit (corepresentation G)).toLinearMap =
    η[(coordinateCogroup G).X].unop.hom.toLinearMap
  exact congrArg AlgHom.toLinearMap
    (Unipotent.counit_cogroupCorepresentation (coordinateCogroup G))

private theorem coalgebra_eq_of_maps {K B : Type*} [CommSemiring K]
    [AddCommMonoid B] [Module K B] (c d : Coalgebra K B)
    (hf : c.comul = d.comul) (he : c.counit = d.counit) : c = d := by
  cases c with
  | @mk cs hc hl hr =>
    cases d with
    | @mk ds hd hdl hdr =>
      have h : cs = ds := by
        cases cs
        cases ds
        congr 1
      cases h
      rfl

/-- The full coalgebra structures agree, including the regular-action conventions. -/
theorem corepresentation_coalgebra_eq :
    (AffineLinearEmbedding.bialgebra (corepresentation G)).toCoalgebra =
      (inferInstance : Coalgebra R (hopfAlgebra G)) :=
  coalgebra_eq_of_maps _ _ (corepresentation_comul G) (corepresentation_counit G)

/-- Evaluation of an affine coordinate on a point over any test scheme. -/
def pointAlgebraHom (T : Over (Spec R)) (g : T ⟶ G.X) :
    algebra G →ₐ[R] ((algΓ R).obj T).unop :=
  ((corepresentation G).homEquiv.symm
    (Corepresented.pointsEquiv (functor G) (corepresentation G) T
      (g ≫ (groupSchemeIso G).inv.hom.hom))).hom

/-- Evaluation is the algebra map supplied by the relative spectrum adjunction. -/
theorem pointAlgebraHom_eq (T : Over (Spec R)) (g : T ⟶ G.X) :
    pointAlgebraHom G T g =
      (((algΓAlgSpecAdjunction R).homEquiv T (op (algebra G))).symm
        (g ≫ (groupSchemeIso G).inv.hom.hom)).unop.hom := by
  simp only [pointAlgebraHom, Corepresented.pointsEquiv_apply, Equiv.symm_apply_apply]
  rfl

/-- Multiplication of actual test points is evaluated by coordinate comultiplication. -/
theorem pointAlgebraHom_mul (T : Over (Spec R)) (g h : T ⟶ G.X) :
    pointAlgebraHom G T (g * h) =
      (Algebra.TensorProduct.productMap (pointAlgebraHom G T g)
        (pointAlgebraHom G T h)).comp (AffineLinearEmbedding.comul (corepresentation G)) := by
  simp only [pointAlgebraHom, MonObj.mul_comp, map_mul,
    AffineLinearEmbedding.homEquiv_symm_mul]

/-- The identity point is evaluated by the coordinate counit. -/
theorem pointAlgebraHom_one (T : Over (Spec R)) :
    pointAlgebraHom G T 1 =
      (Algebra.ofId R ((algΓ R).obj T).unop).comp
        (AffineLinearEmbedding.counit (corepresentation G)) := by
  simp only [pointAlgebraHom, MonObj.one_comp, map_one,
    AffineLinearEmbedding.homEquiv_symm_one]

/-- Pulling back the test scheme pulls back each evaluated coordinate. -/
theorem pointAlgebraHom_naturality {T T' : Over (Spec R)}
    (a : T' ⟶ T) (g : T ⟶ G.X) :
    pointAlgebraHom G T' (a ≫ g) =
      ((algΓ R).map a).unop.hom.comp (pointAlgebraHom G T g) := by
  simp only [pointAlgebraHom, Category.assoc, Corepresented.pointsEquiv_naturality,
    AffineLinearEmbedding.homEquiv_symm_map]

end AffineCoordinates

namespace AffineHomImageHopfAdapter

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

set_option backward.isDefEq.respectTransparency false in
/-- The actual pullback also uses the corepresented affine coordinate isomorphisms. -/
theorem algSpec_map_pullback (f : G ⟶ H) :
    (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (pullback f).hom.toAlgHom).op =
      (AffineCoordinates.groupSchemeIso G).hom.hom.hom ≫ f.hom.hom ≫
        (AffineCoordinates.groupSchemeIso H).inv.hom.hom := by
  have h := congrArg (fun z => z.hom.hom) (hopfSpec.fullyFaithful.map_preimage
    ((AffineCoordinates.hopfSpecIso G).hom ≫ f ≫ (AffineCoordinates.hopfSpecIso H).inv))
  change (algSpec (CommRingCat.of k)).map
      (CommAlgCat.ofHom (pullback f).hom.toAlgHom).op =
    (AffineCoordinates.hopfSpecIso G).hom.hom.hom ≫ f.hom.hom ≫
      (AffineCoordinates.hopfSpecIso H).inv.hom.hom at h
  rw [AffineCoordinates.hopfSpecIso_hom_hom_hom,
    AffineCoordinates.hopfSpecIso_inv_hom_hom,
    ← AffineCoordinates.groupSchemeIso_hom_hom_hom,
    ← AffineCoordinates.groupSchemeIso_inv_hom_hom] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of coordinates commutes with every actual affine group homomorphism. -/
theorem pointAlgebraHom_pullback (f : G ⟶ H)
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) :
    AffineCoordinates.pointAlgebraHom H T (g ≫ f.hom.hom) =
      (AffineCoordinates.pointAlgebraHom G T g).comp (pullback f).hom.toAlgHom := by
  rw [AffineCoordinates.pointAlgebraHom_eq, AffineCoordinates.pointAlgebraHom_eq]
  have hfac : (g ≫ f.hom.hom) ≫ (AffineCoordinates.groupSchemeIso H).inv.hom.hom =
      (g ≫ (AffineCoordinates.groupSchemeIso G).inv.hom.hom) ≫
        (algSpec (CommRingCat.of k)).map
          (CommAlgCat.ofHom (pullback f).hom.toAlgHom).op := by
    rw [algSpec_map_pullback]
    simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id_assoc]
  rw [hfac, (algΓAlgSpecAdjunction (CommRingCat.of k)).homEquiv_naturality_right_symm]
  rfl

end AffineHomImageHopfAdapter

end Langlands.GroupScheme
