import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage

/-! # Coefficients along a linearly independent family on a product -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.ProductCoefficients

variable {k : Type u} [Field k]

/-- A linearly independent family over a field has a dual functional for each member. -/
theorem exists_dual {M : Type*} [AddCommGroup M] [Module k M] {ι : Type*} [DecidableEq ι]
    {e : ι → M} (he : LinearIndependent k e) (j : ι) :
    ∃ f : M →ₗ[k] k, ∀ l, f (e l) = if l = j then 1 else 0 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span he).coord j)
  refine ⟨g, fun l => ?_⟩
  have h1 : g (e l) = (Module.Basis.span he).coord j ⟨e l, Submodule.subset_span ⟨l, rfl⟩⟩ := by
    rw [← hg]
    rfl
  have h2 : (⟨e l, Submodule.subset_span ⟨l, rfl⟩⟩ : Submodule.span k (Set.range e)) =
      Module.Basis.span he l := (Module.Basis.span_apply he l).symm
  rw [h1, h2, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

/-- Tensor coefficients along a linearly independent family over a field vanish
when the tensor vanishes. -/
theorem coeff_eq_zero_of_sum_tmul_eq_zero {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] {ι : Type*} [Fintype ι]
    {e : ι → M} (he : LinearIndependent k e) {n : ι → N}
    (h : ∑ l, e l ⊗ₜ[k] n l = 0) (j : ι) : n j = 0 := by
  classical
  obtain ⟨f, hf⟩ := exists_dual he j
  have e1 := congrArg (fun t => TensorProduct.lid k N (f.rTensor N t)) h
  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hf, map_zero,
    ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at e1
  exact e1

/-- On the product of an affine scheme over a field with an arbitrary scheme,
coefficients along a linearly independent family of global functions on the affine
factor are determined by the resulting global function. -/
theorem coefficients_injective (X T : Over (Spec (CommRingCat.of k))) [IsAffineHom X.hom]
    {ι : Type*} [Fintype ι] (e : ι → Γ(X.left, ⊤))
    (he : letI := Scheme.TwoAffineOpenCover.algebraOfHom X.hom ⊤; LinearIndependent k e)
    {y y' : ι → Γ(T.left, ⊤)}
    (h : ∑ l, (fst X T).left.appTop (e l) * (snd X T).left.appTop (y l) =
      ∑ l, (fst X T).left.appTop (e l) * (snd X T).left.appTop (y' l)) :
    y = y' := by
  classical
  have hX : IsAffine X.left := isAffine_of_isAffineHom X.hom
  -- It suffices to show that the differences vanish.
  set d : ι → Γ(T.left, ⊤) := fun l => y l - y' l with hd
  have h0 : ∑ l, (fst X T).left.appTop (e l) * (snd X T).left.appTop (d l) = 0 := by
    simp only [hd, map_sub, mul_sub, Finset.sum_sub_distrib, h, sub_self]
  -- Restriction to every affine open of `T` kills each difference.
  have hV : ∀ (V : T.left.Opens), IsAffineOpen V → ∀ j,
      T.left.presheaf.map (homOfLE le_top : V ⟶ ⊤).op (d j) = 0 := by
    intro V hVaff j
    let := Scheme.TwoAffineOpenCover.algebraOfHom X.hom ⊤
    let := Scheme.TwoAffineOpenCover.algebraOfHom T.hom V
    let := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst X.hom T.hom ≫ X.hom)
      (pullback.fst X.hom T.hom ⁻¹ᵁ ⊤ ⊓ pullback.snd X.hom T.hom ⁻¹ᵁ V)
    obtain ⟨-, φ, hφ⟩ :=
      P2MW.S_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage.solution
        X.hom T.hom ⊤ (isAffineOpen_top X.left) V hVaff
    have hres := congrArg
      ((pullback X.hom T.hom).presheaf.map (homOfLE le_top :
        pullback.fst X.hom T.hom ⁻¹ᵁ ⊤ ⊓ pullback.snd X.hom T.hom ⁻¹ᵁ V ⟶ ⊤).op) h0
    rw [map_zero, map_sum] at hres
    have hsum : ∑ l, e l ⊗ₜ[k] T.left.presheaf.map (homOfLE le_top : V ⟶ ⊤).op (d l) = 0 := by
      apply φ.injective
      refine (map_sum φ _ _).trans (Eq.trans ?_ (map_zero φ).symm)
      rw [← hres]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hφ, map_mul]
      congr 1
      rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
      rfl
    exact coeff_eq_zero_of_sum_tmul_eq_zero he hsum j
  -- Sections of a scheme vanishing on every affine open vanish.
  funext j
  rw [← sub_eq_zero]
  change d j = 0
  apply TopCat.Presheaf.section_ext T.left.sheaf ⊤
  intro x hx
  obtain ⟨V, hVaff, hxV, -⟩ := exists_isAffineOpen_mem_and_subset hx
  have := hV V hVaff j
  refine (?_ : T.left.presheaf.germ ⊤ x hx (d j) = 0).trans (map_zero _).symm
  calc T.left.presheaf.germ ⊤ x hx (d j) =
      T.left.presheaf.germ V x hxV (T.left.presheaf.map (homOfLE le_top : V ⟶ ⊤).op (d j)) :=
        (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
    _ = 0 := by rw [this, map_zero]

end Langlands.AlgebraicGeometry.ProductCoefficients
