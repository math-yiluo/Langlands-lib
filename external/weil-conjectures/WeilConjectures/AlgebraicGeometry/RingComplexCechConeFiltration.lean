/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingComplexCechData
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.AlgebraicGeometry.RingComplexGodementConstruction
import WeilConjectures.AlgebraicGeometry.RingComplexSemilinearExtension
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage

/-! # Finite localization filtration of the augmentation cone -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private noncomputable def pointIso {A : CommRingCat.{u}} (M N : RingSiteModules A)
    (e : M.val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A] N.val.obj (op ⟨PUnit.unit⟩)) : M ≅ N where
  hom := ringComplexPointLift M N e.toLinearMap
  inv := ringComplexPointLift N M e.symm.toLinearMap
  hom_inv_id := by
    apply ringComplex_point_hom_ext
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    apply ringComplex_point_hom_ext
    ext x
    exact e.apply_symm_apply x

private theorem point_isZero {A : CommRingCat.{u}} (M : RingSiteModules A)
    (h : Subsingleton (M.val.obj (op ⟨PUnit.unit⟩))) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply ringComplex_point_hom_ext
  ext x
  exact h.elim _ _

private theorem point_isIso {A : CommRingCat.{u}} {M N : RingSiteModules A}
    (f : M ⟶ N) (h : Function.Bijective (f.val.app (op ⟨PUnit.unit⟩))) : IsIso f := by
  let e := LinearEquiv.ofBijective (f.val.app (op ⟨PUnit.unit⟩)).hom h
  have hf : f = (pointIso M N e).hom := by
    apply ringComplex_point_hom_ext
    rfl
  rw [hf]
  infer_instance

private theorem localization_term_mem
    (A : CommRingCat.{u}) [HasDerivedCategory.{w} (RingSiteModules A)]
    (I : Ideal A) (r q : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = I)
    (M : RingSiteModules A)
    (e : M.val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A]
      ((t : Fin (q + 1) ↪o Fin r) → Localization.Away (∏ i, f (t i))))
    (P : ObjectProperty (DerivedCategory (RingSiteModules A)))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ (s : A), s ∈ I → ∀ N : RingSiteModules A,
      Function.Bijective (fun x : N.val.obj (op ⟨PUnit.unit⟩) ↦ s • x) →
        P (DerivedCategory.Q.obj
          ((HomologicalComplex.single (RingSiteModules A) (.up ℤ) 0).obj N))) :
    P ((DerivedCategory.singleFunctor (RingSiteModules A) 0).obj M) := by
  classical
  let J := Fin (q + 1) ↪o Fin r
  let g (t : J) : A := ∏ i, f (t i)
  let N (t : J) := ModuleCat.of A (Localization.Away (g t))
  let F := ringComplexConstant A ⋙
    HomologicalComplex.single (RingSiteModules A) (.up ℤ) 0 ⋙ DerivedCategory.Q
  have hfactor (t : J) : P (F.obj (N t)) := by
    apply hP (g t)
    · apply I.mem_of_dvd (Finset.dvd_prod_of_mem (fun i ↦ f (t i))
        (Finset.mem_univ (0 : Fin (q + 1))))
      rw [← hf]
      exact Ideal.subset_span ⟨t 0, rfl⟩
    · change Function.Bijective
        (fun x : Localization.Away (g t) ↦ g t • x)
      simpa only [Algebra.smul_def] using
        (IsUnit.isUnit_iff_mulLeft_bijective.mp
          (IsLocalization.Away.algebraMap_isUnit (g t) (S := Localization.Away (g t))))
  have hprod : P (F.obj (ModuleCat.of A (∀ t : J, N t))) := by
    apply P.prop_of_iso ((PreservesProduct.iso F N).symm ≪≫
      F.mapIso (ModuleCat.piIsoPi N))
    exact P.prop_pi _ hfactor
  exact P.prop_of_iso
    ((DerivedCategory.singleFunctor (RingSiteModules A) 0).mapIso
      (pointIso M ((ringComplexConstant A).obj (ModuleCat.of A (∀ t : J, N t))) e).symm)
    hprod

/-- The cone of a model augmentation belongs to every triangulated subcategory containing
modules on which some element of I acts invertibly. This assertion concerns the target
model alone and imposes no condition on any source of morphisms.
Source: Stacks Project, dualizing.tex, Tag 0A6R, lemma-local-cohomology-adjoint,
the finite localization filtration of its displayed extended Cech complex.
(auxiliary; not a blueprint node)

Proof: choose a finite generating list f of I and use the augmented model isomorphism
in hK. For its ordered model C, the degree-zero augmentation is an isomorphism and
all negative terms vanish. Cancelling the resulting identity pair in its cone gives
the ordinary finite unaugmented localization complex, shifted as prescribed by the
cone convention. Its terms are finite products of A[1/g], with g a product of a
nonempty increasing subset of f. Each g lies in I, and multiplication by g is bijective
on that localization, so each factor in degree zero belongs to P by hP. Finite products
are finite biproducts and belong to P; the zero terms do as well. Filter the bounded
complex by its degrees. The successive triangles have shifts of these terms as their
third vertices, so induction using closure under shifts and distinguished triangles
puts its derived object in P. The augmentation-compatible derived isomorphism gives
an isomorphism of the augmentation triangles (hence their cones), transporting this
membership to the actual cone of εK. For an empty generating list the augmentation is
already an isomorphism and its cone is zero. Zero and nilpotent products simply give
zero localization factors; repeated generators require no change.
-/
theorem ringComplex_cech_cone_filtration
    (A : CommRingCat.{u}) [HasDerivedCategory.{w} (RingSiteModules A)]
    (I : {I : Ideal A // I.FG})
    (K : CochainComplex (RingSiteModules A) ℤ) (εK : K ⟶ ringComplexSingle A)
    (hK : RingComplexHasCechModel A I.val K εK)
    (P : ObjectProperty (DerivedCategory (RingSiteModules A)))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ (s : A), s ∈ I.val → ∀ M : RingSiteModules A,
      Function.Bijective (fun x : M.val.obj (op ⟨PUnit.unit⟩) ↦ s • x) →
        P (DerivedCategory.Q.obj
          ((HomologicalComplex.single (RingSiteModules A) (.up ℤ) 0).obj M))) :
    P (DerivedCategory.Q.obj (CochainComplex.mappingCone εK)) := by
  classical
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp I.property
  have hf' : Ideal.span (Set.range f) = I.val := hf
  obtain ⟨C, a, e₀, e, l, hneg, hd₀, hd, ha, α, hα⟩ := hK r f hf'
  have ha0 : IsIso (a.f 0) := by
    have hcomp : IsIso (a.f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ringComplexUnit A)).hom) := by
      apply point_isIso
      change Function.Bijective (fun x ↦ ringComplexAugmentationValue a x)
      simpa only [ringComplexAugmentationValue, ha] using e₀.bijective
    exact IsIso.of_isIso_comp_right (a.f 0)
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ringComplexUnit A)).hom
  have : Epi a := HomologicalComplex.epi_of_epi_f a (fun n ↦ by
    by_cases hn : n = 0
    · subst hn
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
        (ringComplexUnit A) n hn).epi _)
  let S := ShortComplex.mk (kernel.ι a) a (kernel.condition a)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel a }
  have heval (n : ℤ) := hS.map (HomologicalComplex.eval (RingSiteModules A) (.up ℤ) n)
  have htail_iso (n : ℤ) (hn : n ≠ 0) : IsIso ((kernel.ι a).f n) := by
    exact (heval n).isIso_f_iff.mpr
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ringComplexUnit A) n hn)
  have hzero : IsZero ((kernel a).X 0) := (heval 0).isIso_g_iff.mp ha0
  have hupper (n : ℤ) (hn : (r : ℤ) < n) : IsZero (C.X n) := by
    obtain ⟨q, hq⟩ : ∃ q : ℕ, n = (q : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
    subst n
    have hJ : IsEmpty (Fin (q + 1) ↪o Fin r) := ⟨fun t ↦ by
      have ht := Fintype.card_le_of_injective t t.injective
      simp only [Fintype.card_fin] at ht
      omega⟩
    apply point_isZero
    exact e q |>.injective.subsingleton
  have htail : P (DerivedCategory.Q.obj (kernel a)) := by
    apply bounded_complex_mem_triangulated P (kernel a) 1 r
    · intro n hn
      by_cases hn0 : n = 0
      · subst hn0
        exact hzero
      · have := htail_iso n hn0
        exact (if h : n < 0 then hneg n h else hupper n (by omega)).of_iso
          (asIso ((kernel.ι a).f n))
    · intro n hn hnr
      have hn0 : n ≠ 0 := by omega
      have := htail_iso n hn0
      obtain ⟨q, hq⟩ : ∃ q : ℕ, n = (q : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
      subst n
      apply P.prop_of_iso
        ((DerivedCategory.singleFunctor (RingSiteModules A) 0).mapIso
          (asIso ((kernel.ι a).f ((q : ℤ) + 1)))).symm
      exact localization_term_mem A I.val r q f hf' _ (e q) P hP
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle a)
  let TK := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle εK)
  have hT := DerivedCategory.mappingCone_triangle_distinguished a
  have hTK := DerivedCategory.mappingCone_triangle_distinguished εK
  let β := Pretriangulated.isoTriangleOfIso₁₂
    (DerivedCategory.triangleOfSES hS).rotate T
    ((Pretriangulated.rotate_distinguished_triangle _).mp
      (DerivedCategory.triangleOfSES_distinguished hS)) hT
    (Iso.refl _) (Iso.refl _) (by
      change DerivedCategory.Q.map a ≫ 𝟙 _ = 𝟙 _ ≫ DerivedCategory.Q.map a
      simp)
  have hmodel : P (DerivedCategory.Q.obj (CochainComplex.mappingCone a)) := by
    exact P.prop_of_iso (Pretriangulated.Triangle.π₃.mapIso β)
      (P.le_shift (1 : ℤ) _ htail)
  let γ := Pretriangulated.isoTriangleOfIso₁₂ T TK hT hTK α (Iso.refl _)
    (by
      change DerivedCategory.Q.map a ≫ 𝟙 _ = α.hom ≫ DerivedCategory.Q.map εK
      simpa only [Category.comp_id] using hα.symm)
  exact P.prop_of_iso (Pretriangulated.Triangle.π₃.mapIso γ) hmodel

end AlgebraicGeometry
