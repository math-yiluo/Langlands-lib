import Langlands.AbelianScheme.GroupSchemeSubalgebraDescentProof
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.NoetherianDescent

/-! # Models of smooth affine group schemes over rings of finite type over `ℤ` -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme

/-- A smooth affine group scheme over `Spec A` is the base change of a smooth affine group
scheme over `Spec R` along a ring map `R → A`, for a ring `R` of finite type over `ℤ`. -/
theorem exists_finiteType_model (A : Type u) [CommRing A]
    (G : GroupScheme (Spec (CommRingCat.of A))) [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra.FiniteType ℤ R) (φ : R →+* A)
      (G₀ : GroupScheme (Spec (CommRingCat.of R))),
      Smooth G₀.X.hom ∧ IsAffineHom G₀.X.hom ∧
        Nonempty (G ≅ (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom φ))).obj G₀) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  -- The coordinate ring `B` of `G` as an `A`-algebra.
  let ψ : CommRingCat.of A ⟶ Γ(G.X.left, ⊤) := (Scheme.ΓSpecIso _).inv ≫ G.X.hom.appTop
  have hψ : G.X.left.isoSpec.hom ≫ Spec.map ψ = G.X.hom := by
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_hom_naturality_assoc,
      Iso.hom_inv_id, Category.comp_id]
  let : Algebra A Γ(G.X.left, ⊤) := ψ.hom.toAlgebra
  have hψs : ψ.hom.Smooth := by
    have h : Spec.map ψ = G.X.left.isoSpec.inv ≫ G.X.hom := by rw [← hψ, Iso.inv_hom_id_assoc]
    rw [← HasRingHomProperty.Spec_iff (P := @Smooth), h]
    infer_instance
  have : Algebra.Smooth A Γ(G.X.left, ⊤) := hψs
  obtain ⟨A₀, B₀, _, _, hA₀, hB₀, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ A Γ(G.X.left, ⊤)
  -- The affine model `Spec B₀ → Spec A₀` and the pullback square exhibiting `G` as its
  -- base change.
  let f₀ : Spec (CommRingCat.of B₀) ⟶ Spec (CommRingCat.of A₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))
  have hf₀ : Smooth f₀ := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth), CommRingCat.hom_ofHom,
      RingHom.smooth_algebraMap]
    exact hB₀
  let eR : CommRingCat.of (A ⊗[A₀] B₀) ≅ Γ(G.X.left, ⊤) := e.symm.toRingEquiv.toCommRingCatIso
  let eX : G.X.left ≅ Spec (CommRingCat.of (A ⊗[A₀] B₀)) :=
    G.X.left.isoSpec ≪≫ Scheme.Spec.mapIso eR.op
  have hinl : CommRingCat.ofHom (S := A ⊗[A₀] B₀) Algebra.TensorProduct.includeLeftRingHom ≫
      eR.hom = ψ := by
    ext a
    exact e.symm.commutes a
  have hpb : IsPullback (eX.hom ≫ Spec.map (CommRingCat.ofHom
      (S := A ⊗[A₀] B₀) Algebra.TensorProduct.includeRight.toRingHom)) G.X.hom f₀
      (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) := by
    refine (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct A₀ A B₀)).flip.of_iso' eX (Iso.refl _)
        (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp [f₀]) (by simp)
    change (G.X.left.isoSpec.hom ≫ Spec.map eR.hom) ≫ _ = _
    rw [Iso.refl_hom, Category.comp_id, ← hψ, Category.assoc, ← Spec.map_comp, hinl]
  obtain ⟨T, hT, -, G₀, a₀, hpb₀, -, ⟨eG⟩⟩ := subalgebraDescent f₀ G _ hpb ∅
  have : Algebra.FiniteType ℤ A₀ := Subalgebra.fg_iff_finiteType _ |>.mp hA₀
  have : Algebra.FiniteType A₀ T := Subalgebra.fg_iff_finiteType _ |>.mp hT
  refine ⟨T, inferInstance, Algebra.FiniteType.trans (S := A₀) inferInstance inferInstance,
    algebraMap T A, G₀, MorphismProperty.of_isPullback hpb₀ hf₀,
    MorphismProperty.of_isPullback (P := @IsAffineHom) hpb₀ inferInstance, ⟨eG⟩⟩

end Langlands.GroupScheme
