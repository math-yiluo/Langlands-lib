import Langlands.GroupScheme.Torus.AffineDiagonalizableTranslation
import Langlands.GroupScheme.Torus.CentralExtensionHopfSpec

/-! # Coordinates of diagonalizable translation graphs -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.CharacterAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]

/-- Tensor inclusions evaluated in the group algebra. -/
def productAlgebraHom (B : CommAlgCat.{u} R) :
    Corepresented.tensorObj (Diagonalizable.algebra R M) B ⟶ algebra (M := M) B :=
  Corepresented.tensorLift (Diagonalizable.lift R M (universal B)) (constant B)

/-- The universal coefficient and character maps into the tensor product. -/
def productAlgebraInv (B : CommAlgCat.{u} R) :
    algebra (M := M) B ⟶ Corepresented.tensorObj (Diagonalizable.algebra R M) B :=
  evaluate (Corepresented.inr (Diagonalizable.algebra R M) B)
    (mapCharacter (Corepresented.inl (Diagonalizable.algebra R M) B)
      (Diagonalizable.monomialUnits R M))

@[simp] theorem productAlgebraInv_single (B : CommAlgCat.{u} R) (m : M) (b : B) :
    (productAlgebraInv B).hom (AddMonoidAlgebra.single m b) =
      AddMonoidAlgebra.single m 1 ⊗ₜ[R] b := by
  rw [productAlgebraInv, evaluate_single]
  change ((1 : AddMonoidAlgebra R M) ⊗ₜ[R] b) *
    (AddMonoidAlgebra.single m 1 ⊗ₜ[R] (1 : B)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

/-- The group algebra is the coordinate algebra of the product with `D(M)`. -/
def productAlgebraIso (B : CommAlgCat.{u} R) :
    Corepresented.tensorObj (Diagonalizable.algebra R M) B ≅ algebra (M := M) B where
  hom := productAlgebraHom B
  inv := productAlgebraInv B
  hom_inv_id := by
    apply CommAlgCat.hom_ext
    apply Algebra.TensorProduct.ext
    · apply AddMonoidAlgebra.algHom_ext
      · intro m
        change (productAlgebraInv B).hom
          ((productAlgebraHom B).hom (AddMonoidAlgebra.single m 1 ⊗ₜ[R] 1)) =
            AddMonoidAlgebra.single m 1 ⊗ₜ[R] 1
        rw [productAlgebraHom, Corepresented.tensorLift_tmul, map_one, mul_one,
          Diagonalizable.lift_single, one_smul]
        exact productAlgebraInv_single B m 1
      · exact Subsingleton.elim _ _
    · apply AlgHom.ext
      intro b
      change (productAlgebraInv B).hom
        ((productAlgebraHom B).hom ((1 : AddMonoidAlgebra R M) ⊗ₜ[R] b)) = 1 ⊗ₜ[R] b
      rw [productAlgebraHom, Corepresented.tensorLift_tmul, map_one, one_mul,
        constant_apply, productAlgebraInv_single]
      rfl
  inv_hom_id := by
    apply CommAlgCat.hom_ext
    apply AddMonoidAlgebra.algHom_ext
    · intro m
      change (productAlgebraHom B).hom
        ((productAlgebraInv B).hom (AddMonoidAlgebra.single m 1)) = _
      rw [productAlgebraInv_single, productAlgebraHom, Corepresented.tensorLift_tmul,
        map_one, mul_one, Diagonalizable.lift_single, one_smul]
      rfl
    · apply AlgHom.ext
      intro b
      change (productAlgebraHom B).hom
        ((productAlgebraInv B).hom (AddMonoidAlgebra.single 0 b)) = _
      rw [productAlgebraInv_single]
      change (productAlgebraHom B).hom ((1 : AddMonoidAlgebra R M) ⊗ₜ[R] b) = _
      rw [productAlgebraHom, Corepresented.tensorLift_tmul, map_one, one_mul]
      rfl

/-- Spectrum comparison with the product of the diagonalizable group and `Spec B`. -/
def algebraProductIso (B : CommAlgCat.{u} R) :
    (algSpec R).obj (op (algebra (M := M) B)) ≅
      (Diagonalizable.groupScheme R M).X ⊗ (algSpec R).obj (op B) :=
  (algSpec R).mapIso (productAlgebraIso (M := M) B).op ≪≫
    prodComparisonIso (algSpec R) (op (Diagonalizable.algebra R M)) (op B)

@[simp] theorem algebraProductIso_hom_fst (B : CommAlgCat.{u} R) :
    (algebraProductIso (M := M) B).hom ≫ fst _ _ = characterPoint (universal B) := by
  change (algSpec R).map (productAlgebraHom B).op ≫
    prodComparison (algSpec R) _ _ ≫ fst _ _ = _
  rw [prodComparison_fst, ← Functor.map_comp]
  have h : (productAlgebraHom (M := M) B).op ≫
      fst (op (Diagonalizable.algebra R M)) (op B) =
        (Diagonalizable.lift R M (universal B)).op := by
    apply Quiver.Hom.unop_inj
    exact Corepresented.inl_tensorLift _ _
  rw [h]
  apply (Corepresented.affinePointsEquiv (Diagonalizable.functor R M)
    (Diagonalizable.grpCorepresentation R M) _).injective
  rw [Corepresented.affinePointsEquiv_map]
  simp only [characterPoint, MulEquiv.apply_symm_apply]
  apply MonoidHom.ext
  intro m
  apply Units.ext
  change (Diagonalizable.lift R M (universal B)).hom
    (AddMonoidAlgebra.single m.toAdd 1) = _
  rw [Diagonalizable.lift_single, one_smul]
  rfl

@[simp] theorem algebraProductIso_hom_snd (B : CommAlgCat.{u} R) :
    (algebraProductIso (M := M) B).hom ≫ snd _ _ =
      (algSpec R).map (constant (M := M) B).op := by
  change (algSpec R).map (productAlgebraHom B).op ≫
    prodComparison (algSpec R) _ _ ≫ snd _ _ = _
  rw [prodComparison_snd, ← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  exact Corepresented.inr_tensorLift _ _

variable {G : GroupScheme (Spec R)} [IsAffine G.X.left]

/-- The actual product of the diagonalizable group with the affine group. -/
def translationProductIso (G : GroupScheme (Spec R)) [IsAffine G.X.left] :
    (algSpec R).obj (op (algebra (M := M) (AffineCoordinates.algebra G))) ≅
      (Diagonalizable.groupScheme R M).X ⊗ G.X :=
  algebraProductIso (AffineCoordinates.algebra G) ≪≫
    tensorIso (Iso.refl _) (AffineCoordinates.coordinateSchemeIso G)

@[simp] theorem translationProductIso_hom_fst :
    (translationProductIso (M := M) G).hom ≫ fst _ _ =
      characterPoint (universal (AffineCoordinates.algebra G)) := by
  simp only [translationProductIso, Iso.trans_hom, Category.assoc, tensorIso_hom,
    tensorHom_fst, Iso.refl_hom, Category.comp_id]
  exact algebraProductIso_hom_fst (AffineCoordinates.algebra G)

@[simp] theorem translationProductIso_hom_snd :
    (translationProductIso (M := M) G).hom ≫ snd _ _ =
      AffineCoordinates.pointEquiv G _ (constant (AffineCoordinates.algebra G)) := by
  simp only [translationProductIso, Iso.trans_hom, Category.assoc, tensorIso_hom,
    tensorHom_snd]
  rw [← Category.assoc, algebraProductIso_hom_snd]
  rfl

/-- Coordinates for the square of the actual affine group. -/
def affineSquareIso (G : GroupScheme (Spec R)) [IsAffine G.X.left] :
    (algSpec R).obj (op (Corepresented.tensorObj
      (AffineCoordinates.algebra G) (AffineCoordinates.algebra G))) ≅ G.X ⊗ G.X :=
  prodComparisonIso (algSpec R) (op (AffineCoordinates.algebra G))
    (op (AffineCoordinates.algebra G)) ≪≫
      tensorIso (AffineCoordinates.coordinateSchemeIso G) (AffineCoordinates.coordinateSchemeIso G)

/-- The first coordinate of a spectrum map into the square. -/
theorem map_affineSquareIso_fst {C : CommAlgCat.{u} R}
    (f : Corepresented.tensorObj (AffineCoordinates.algebra G) (AffineCoordinates.algebra G) ⟶ C) :
    (algSpec R).map f.op ≫ (affineSquareIso G).hom ≫ fst _ _ =
      AffineCoordinates.pointEquiv G C
        (Corepresented.inl (AffineCoordinates.algebra G) (AffineCoordinates.algebra G) ≫ f) := by
  simp only [affineSquareIso, Iso.trans_hom, Category.assoc, tensorIso_hom, tensorHom_fst,
    prodComparisonIso_hom, prodComparison_fst_assoc]
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

/-- The second coordinate of a spectrum map into the square. -/
theorem map_affineSquareIso_snd {C : CommAlgCat.{u} R}
    (f : Corepresented.tensorObj (AffineCoordinates.algebra G) (AffineCoordinates.algebra G) ⟶ C) :
    (algSpec R).map f.op ≫ (affineSquareIso G).hom ≫ snd _ _ =
      AffineCoordinates.pointEquiv G C
        (Corepresented.inr (AffineCoordinates.algebra G) (AffineCoordinates.algebra G) ≫ f) := by
  simp only [affineSquareIso, Iso.trans_hom, Category.assoc, tensorIso_hom, tensorHom_snd,
    prodComparisonIso_hom, prodComparison_snd_assoc]
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

/-- The graph map of an action in the category of algebras over the original base. -/
def graphMap {B : CommAlgCat.{u} R} (a : Action (M := M) B) :
    Corepresented.tensorObj B B ⟶ algebra (M := M) B :=
  Corepresented.tensorLift (constant B) (coaction a)

/-- The geometric graph coordinates are the strong-grading graph coordinates. -/
theorem graphMap_hom_eq {B : CommAlgCat.{u} R} (a : Action (M := M) B) :
    (graphMap a).hom =
      (Langlands.CommutativeAlgebra.StronglyGraded.graph (coaction a).hom).restrictScalars R := by
  apply Algebra.TensorProduct.ext'
  intro b c
  rfl

/-- The spectrum of the coordinate graph is the actual subgroup-translation graph. -/
theorem map_graphMap_ofTranslation
    (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G) :
    (algSpec R).map (graphMap (ofTranslation i)).op ≫ (affineSquareIso G).hom =
      (translationProductIso (M := M) G).hom ≫ Translation.graph i := by
  apply hom_ext
  · rw [Category.assoc, map_affineSquareIso_fst]
    simp only [graphMap, Corepresented.inl_tensorLift, Translation.graph, comp_lift, lift_fst,
      translationProductIso_hom_snd]
  · rw [Category.assoc, map_affineSquareIso_snd]
    rw [graphMap, Corepresented.inr_tensorLift]
    change AffineCoordinates.pointEquiv G _
      ((ofTranslation i).act (universal _) (constant _)) = _
    rw [pointEquiv_ofTranslation_act]
    simp only [Translation.graph, comp_lift, lift_snd, MonObj.comp_mul,
      ← Category.assoc, translationProductIso_hom_fst, translationProductIso_hom_snd]

/-- Closed subgroup translation has surjective graph coordinates. -/
theorem graph_surjective_of_isClosedSubgroup
    (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G) (hi : IsClosedSubgroup i) :
    Function.Surjective
      (Langlands.CommutativeAlgebra.StronglyGraded.graph (coaction (ofTranslation i)).hom) := by
  have he : (algSpec R).map (graphMap (ofTranslation i)).op =
      (translationProductIso (M := M) G).hom ≫ Translation.graph i ≫
        (affineSquareIso G).inv := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun f => f ≫ (affineSquareIso G).inv) (map_graphMap_ofTranslation i)
  let : IsClosedImmersion (Translation.graph i).left := Translation.isClosedImmersion_graph i hi
  have hclosed : IsClosedImmersion ((algSpec R).map (graphMap (ofTranslation i)).op).left := by
    rw [he, Over.comp_left, Over.comp_left]
    infer_instance
  change IsClosedImmersion
    (Spec.map (CommRingCat.ofHom (graphMap (ofTranslation i)).hom.toRingHom)) at hclosed
  let := hclosed
  have hs := CentralExtensionHopfSpec.surjective_of_isClosedImmersion
    (CommRingCat.ofHom (graphMap (ofTranslation i)).hom.toRingHom)
  change Function.Surjective (graphMap (ofTranslation i)).hom at hs
  rw [graphMap_hom_eq] at hs
  exact hs

/-- A closed diagonalizable subgroup gives a strong translation grading. -/
theorem isStrong_ofTranslation
    (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G) (hi : IsClosedSubgroup i) :
    Langlands.CommutativeAlgebra.StronglyGraded.IsStrong
      (c := (coaction (ofTranslation i)).hom.toRingHom) :=
  Langlands.CommutativeAlgebra.StronglyGraded.strong_of_graph_surjective
    (coaction (ofTranslation i)).hom (isGrading_coaction _) (graph_surjective_of_isClosedSubgroup i hi)

end Langlands.GroupScheme.CharacterAction
