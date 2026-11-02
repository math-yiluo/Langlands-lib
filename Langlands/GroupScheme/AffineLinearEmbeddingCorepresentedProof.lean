import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.CorepresentedLinearEmbedding
import Langlands.GroupScheme.AffinePoints

/-! # Proof of the closed linear embedding theorem for affine algebraic groups over a field -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineCorepresentation

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) {B : CommAlgCat.{u} R}
  (ψ : (algSpec R).obj (op B) ≅ G.X)

/-- The affine points of `G` are corepresented by `B`, through the isomorphism `ψ`. -/
abbrev corep : (affinePointFunctor G ⋙ forget GrpCat).CorepresentableBy B :=
  AffineLinearEmbedding.corepresentableBy G ψ

/-- The corepresented group scheme carried by `Spec B`. -/
abbrev model : GroupScheme (Spec R) :=
  AffineLinearEmbedding.model G ψ

/-- The comparison isomorphism between the underlying objects. -/
def iso : (model G ψ).X ≅ G.X := ψ

theorem iso_hom : (iso G ψ).hom = ψ.hom := rfl

/-- The affine point comparison of the model is composition with `ψ`. -/
theorem affinePointsEquiv_eq (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ (model G ψ).X) :
    (Corepresented.affinePointsEquiv _ (corep G ψ) S x : (algSpec R).obj (op S) ⟶ G.X) =
      x ≫ (iso G ψ).hom := by
  rw [Corepresented.affinePointsEquiv_apply]
  have hx : (algSpec R).map
      (algSpec.fullyFaithful.preimage (x : (algSpec R).obj (op S) ⟶ (algSpec R).obj (op B))) =
      x := algSpec.fullyFaithful.map_preimage _
  change (algSpec R).map (algSpec.fullyFaithful.preimage x) ≫ ψ.hom = x ≫ ψ.hom
  exact congrArg (· ≫ ψ.hom) hx

theorem mul_comp_affine (W : (CommAlgCat.{u} R)ᵒᵖ)
    (p q : (algSpec R).obj W ⟶ (model G ψ).X) :
    (p * q) ≫ (iso G ψ).hom = (p ≫ (iso G ψ).hom) * (q ≫ (iso G ψ).hom) := by
  have h := map_mul (Corepresented.affinePointsEquiv _ (corep G ψ) W.unop) p q
  rw [affinePointsEquiv_eq, affinePointsEquiv_eq, affinePointsEquiv_eq] at h
  exact h

theorem one_comp_affine (W : (CommAlgCat.{u} R)ᵒᵖ) :
    (1 : (algSpec R).obj W ⟶ (model G ψ).X) ≫ (iso G ψ).hom = 1 := by
  have h := map_one (Corepresented.affinePointsEquiv _ (corep G ψ) W.unop)
  rw [affinePointsEquiv_eq] at h
  exact h

theorem mul_comp_of_iso {Z : Over (Spec R)} (W : (CommAlgCat.{u} R)ᵒᵖ)
    (i : Z ≅ (algSpec R).obj W) (p q : Z ⟶ (model G ψ).X) :
    (p * q) ≫ (iso G ψ).hom = (p ≫ (iso G ψ).hom) * (q ≫ (iso G ψ).hom) := by
  calc (p * q) ≫ (iso G ψ).hom = i.hom ≫ (i.inv ≫ (p * q)) ≫ (iso G ψ).hom := by
        rw [← Category.assoc, Iso.hom_inv_id_assoc]
    _ = i.hom ≫ ((i.inv ≫ p) * (i.inv ≫ q)) ≫ (iso G ψ).hom := by rw [MonObj.comp_mul]
    _ = i.hom ≫ (((i.inv ≫ p) ≫ (iso G ψ).hom) * ((i.inv ≫ q) ≫ (iso G ψ).hom)) := by
        rw [mul_comp_affine]
    _ = (i.hom ≫ (i.inv ≫ p) ≫ (iso G ψ).hom) * (i.hom ≫ (i.inv ≫ q) ≫ (iso G ψ).hom) := by
        rw [MonObj.comp_mul]
    _ = (p ≫ (iso G ψ).hom) * (q ≫ (iso G ψ).hom) := by
        rw [← Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, Iso.hom_inv_id_assoc]

theorem one_comp_of_iso {Z : Over (Spec R)} (W : (CommAlgCat.{u} R)ᵒᵖ)
    (i : Z ≅ (algSpec R).obj W) :
    (1 : Z ⟶ (model G ψ).X) ≫ (iso G ψ).hom = 1 := by
  calc (1 : Z ⟶ (model G ψ).X) ≫ (iso G ψ).hom =
        i.hom ≫ (i.inv ≫ (1 : Z ⟶ (model G ψ).X)) ≫ (iso G ψ).hom := by
        rw [← Category.assoc, Iso.hom_inv_id_assoc]
    _ = i.hom ≫ (1 : (algSpec R).obj W ⟶ (model G ψ).X) ≫ (iso G ψ).hom := by
        rw [MonObj.comp_one]
    _ = 1 := by rw [one_comp_affine, MonObj.comp_one]

/-- The comparison isomorphism is a homomorphism of group objects. -/
instance isMonHom_iso : IsMonHom (iso G ψ).hom where
  one_hom := by
    rw [MonObj.one_eq_one, MonObj.one_eq_one]
    exact one_comp_of_iso G ψ _ (Functor.Monoidal.εIso (algSpec R))
  mul_hom := by
    let i : (model G ψ).X ⊗ (model G ψ).X ≅ (algSpec R).obj (op B ⊗ op B) :=
      Functor.Monoidal.μIso (algSpec R) (op B) (op B)
    rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul, mul_comp_of_iso G ψ _ i, MonObj.comp_mul,
      tensorHom_fst, tensorHom_snd]

/-- The inverse comparison as an actual homomorphism of group schemes. -/
def toModel : G ⟶ model G ψ := Grp.homMk (iso G ψ).inv

theorem toModel_hom_left : (toModel G ψ).hom.hom.left = ψ.inv.left := rfl

/-- A spectrum isomorphic over the base to a locally finite type scheme has a finite type
coordinate algebra. -/
theorem finiteType_of_iso {R : CommRingCat.{u}} {X : Over (Spec R)} [LocallyOfFiniteType X.hom]
    (W : (CommAlgCat.{u} R)ᵒᵖ) (ψ : (algSpec R).obj W ≅ X) : Algebra.FiniteType R W.unop := by
  have : IsIso ψ.hom.left := inferInstanceAs (IsIso ((Over.forget _).map ψ.hom))
  have h1 : LocallyOfFiniteType ((algSpec R).obj W).hom := by
    rw [← Over.w ψ.hom]
    infer_instance
  change @LocallyOfFiniteType (Spec (CommRingCat.of W.unop)) (Spec (CommRingCat.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R W.unop))) at h1
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h1
  exact RingHom.finiteType_algebraMap.mp h1

end AffineCorepresentation

/-- Every affine group scheme of finite type over a field has a finite-dimensional
representation that is a closed immersion. -/
theorem affineLinearEmbeddingStatement_viaCorepresented : AffineLinearEmbeddingStatement.{u} := by
  intro k _ G _ _
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨W, ⟨ψ⟩⟩ := (essImage_algSpec (G := G.X)).mpr inferInstance
  have : Algebra.FiniteType (CommRingCat.of k) W.unop :=
    AffineCorepresentation.finiteType_of_iso W ψ
  obtain ⟨N, ρ, hρ⟩ :=
    Corepresented.exists_isClosedSubgroup k (AffineCorepresentation.corep G (B := W.unop) ψ)
  refine ⟨N, AffineCorepresentation.toModel G (B := W.unop) ψ ≫ ρ, ?_⟩
  unfold IsClosedSubgroup at hρ ⊢
  have : IsIso ψ.inv.left := inferInstanceAs (IsIso ((Over.forget _).map ψ.inv))
  have hψ : IsClosedImmersion ψ.inv.left := inferInstance
  exact @IsClosedImmersion.comp _ _ _ ψ.inv.left ρ.hom.hom.left hψ hρ

end Langlands.GroupScheme
