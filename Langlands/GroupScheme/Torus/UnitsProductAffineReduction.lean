import Langlands.GroupScheme.Torus.UnitsProductDecompositionStatement
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage

/-! # Affine product-units splitting from tensor-product units -/

noncomputable section
universe u v w

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open P2MW.S_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage.P2mKDeg0 (appLE_top_top)

namespace Langlands.GroupScheme.UnitsProduct

/-- The fixed-algebra input used to split units on an affine product. -/
def TensorUnitsSplit (k : Type u) [CommRing k]
    (A : Type v) [CommRing A] [Algebra k A]
    (B : Type w) [CommRing B] [Algebra k B] : Prop :=
  ∀ z : (A ⊗[k] B)ˣ, ∃ (a : Aˣ) (b : Bˣ),
    (z : A ⊗[k] B) = (a : A) ⊗ₜ[k] (b : B)

/-- Global sections of an affine product are the actual tensor product,
with pure tensors given by multiplication of the two pullbacks. -/
theorem exists_affine_product_sections_equiv (k : Type u) [CommRing k]
    (X Y : Over (Spec (CommRingCat.of k))) [IsAffine X.left] [IsAffine Y.left] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom X.hom ⊤
    letI := Scheme.TwoAffineOpenCover.algebraOfHom Y.hom ⊤
    ∃ e : Γ(X.left, ⊤) ⊗[k] Γ(Y.left, ⊤) ≃+* Γ((X ⊗ Y).left, ⊤),
      ∀ (a : Γ(X.left, ⊤)) (b : Γ(Y.left, ⊤)), e (a ⊗ₜ[k] b) =
        (fst X Y).left.appTop a * (snd X Y).left.appTop b := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom X.hom ⊤
  let := Scheme.TwoAffineOpenCover.algebraOfHom Y.hom ⊤
  let := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst X.hom Y.hom ≫ X.hom)
    (pullback.fst X.hom Y.hom ⁻¹ᵁ ⊤ ⊓ pullback.snd X.hom Y.hom ⁻¹ᵁ ⊤)
  obtain ⟨-, e, he⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage.solution
      X.hom Y.hom ⊤ (isAffineOpen_top X.left) ⊤ (isAffineOpen_top Y.left)
  have htop : pullback.fst X.hom Y.hom ⁻¹ᵁ ⊤ ⊓
      pullback.snd X.hom Y.hom ⁻¹ᵁ ⊤ = ⊤ := by simp
  let ρ : Γ(pullback X.hom Y.hom, pullback.fst X.hom Y.hom ⁻¹ᵁ ⊤ ⊓
      pullback.snd X.hom Y.hom ⁻¹ᵁ ⊤) ≅ Γ((X ⊗ Y).left, ⊤) :=
    (pullback X.hom Y.hom).presheaf.mapIso (eqToIso htop).symm.op
  refine ⟨e.toRingEquiv.trans ρ.commRingCatIsoToRingEquiv, ?_⟩
  intro a b
  change (pullback X.hom Y.hom).presheaf.map (eqToHom htop.symm).op (e (a ⊗ₜ[k] b)) = _
  rw [he, map_mul]
  congr 1 <;> rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, appLE_top_top] <;> rfl

/-- Tensor-unit splitting on the coordinate rings gives splitting of actual
morphisms from the affine product to the multiplicative group. -/
theorem affine_splitting_of_tensor_units (k : Type u) [CommRing k]
    (X Y : Over (Spec (CommRingCat.of k))) [IsAffine X.left] [IsAffine Y.left] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom X.hom ⊤
    letI := Scheme.TwoAffineOpenCover.algebraOfHom Y.hom ⊤
    TensorUnitsSplit k Γ(X.left, ⊤) Γ(Y.left, ⊤) →
      ∀ f : X ⊗ Y ⟶ (Gm (Spec (CommRingCat.of k))).X,
        ∃ (a : X ⟶ (Gm (Spec (CommRingCat.of k))).X)
          (b : Y ⟶ (Gm (Spec (CommRingCat.of k))).X),
          f = (fst X Y ≫ a) * (snd X Y ≫ b) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom X.hom ⊤
  let := Scheme.TwoAffineOpenCover.algebraOfHom Y.hom ⊤
  intro hsplit f
  obtain ⟨e, he⟩ := exists_affine_product_sections_equiv k X Y
  let s := Gm.pointsEquiv (Spec (CommRingCat.of k)) (X ⊗ Y) f
  let z := Units.map e.symm.toMonoidHom s
  obtain ⟨a, b, hab⟩ := hsplit z
  refine ⟨(Gm.pointsEquiv _ X).symm a, (Gm.pointsEquiv _ Y).symm b, ?_⟩
  apply (Gm.pointsEquiv _ (X ⊗ Y)).injective
  apply Units.ext
  simp only [map_mul, Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply,
    Units.val_mul, Units.coe_map]
  calc
    (s : Γ((X ⊗ Y).left, ⊤)) = e (z : Γ(X.left, ⊤) ⊗[k] Γ(Y.left, ⊤)) :=
      (e.apply_symm_apply _).symm
    _ = e ((a : Γ(X.left, ⊤)) ⊗ₜ[k] (b : Γ(Y.left, ⊤))) := congrArg e hab
    _ = _ := he _ _

/-- Local finite type on an affine scheme gives finite type for the coordinate
algebra used in the tensor-sections equivalence. -/
theorem finiteType_sections_algebra (k : Type u) [CommRing k]
    (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom X.hom ⊤
    Algebra.FiniteType k Γ(X.left, ⊤) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom X.hom ⊤
  apply RingHom.finiteType_algebraMap.mp
  have h := (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) X.hom inferInstance).comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appLE ⊤ ⊤ le_top).hom.FiniteType
  have happ : X.hom.appLE ⊤ ⊤ le_top = X.hom.appTop := appLE_top_top _ _
  rw [happ]
  exact h

/-- A tensor-unit theorem for finitely generated domains supplies the affine
case used by the geometric product-units reduction. -/
theorem affine_splitting_of_domain_tensor_units
    (hsplit : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (A : Type u) [CommRing A] [Algebra k A] [IsDomain A] [Algebra.FiniteType k A]
      (B : Type u) [CommRing B] [Algebra k B] [IsDomain B] [Algebra.FiniteType k B],
      TensorUnitsSplit k A B)
    (k : Type u) [Field k] [IsAlgClosed k]
    (X Y : Over (Spec (CommRingCat.of k))) [IsAffine X.left] [IsAffine Y.left]
    [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⊗ Y ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    ∃ (a : X ⟶ (Gm (Spec (CommRingCat.of k))).X)
      (b : Y ⟶ (Gm (Spec (CommRingCat.of k))).X),
      f = (fst X Y ≫ a) * (snd X Y ≫ b) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom X.hom ⊤
  let := Scheme.TwoAffineOpenCover.algebraOfHom Y.hom ⊤
  have := finiteType_sections_algebra k X
  have := finiteType_sections_algebra k Y
  exact affine_splitting_of_tensor_units k X Y (hsplit k Γ(X.left, ⊤) Γ(Y.left, ⊤)) f

end Langlands.GroupScheme.UnitsProduct
