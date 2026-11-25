/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated

import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomTransposeExact

/-! # The thick locus of the étale scalar Hom comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w w₁ w₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Pretriangulated.Opposite Opposite
namespace AlgebraicGeometry.Etale
variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

namespace HomComparison
variable {C : Type w₁} {D : Type w₂} [Category.{v} C] [Category.{w} D]
  (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C) (adj : T ⊣₂ H)
  (S : D ⥤ D ⥤ D) (J : Dᵒᵖ ⥤ D ⥤ D) (adj' : S ⊣₂ J)
  (F : C ⥤ D)
  (μ : ∀ K L : C, (S.obj (F.obj K)).obj (F.obj L) ≅ F.obj ((T.obj K).obj L))

private def component (K M : C) : F.obj ((H.obj (op K)).obj M) ⟶
    (J.obj (op (F.obj K))).obj (F.obj M) :=
  adj'.homEquiv ((μ K ((H.obj (op K)).obj M)).hom ≫
    F.map ((adj.adj K).counit.app M))

variable
  (hμ₁ : ∀ {K K' : C} (f : K ⟶ K') (L : C),
    (S.map (F.map f)).app (F.obj L) ≫ (μ K' L).hom =
      (μ K L).hom ≫ F.map ((T.map f).app L))
  (hμ₂ : ∀ (K : C) {L L' : C} (g : L ⟶ L'),
    (S.obj (F.obj K)).map (F.map g) ≫ (μ K L').hom =
      (μ K L).hom ≫ F.map ((T.obj K).map g))

include hμ₁ hμ₂ in
private theorem natural₁ (M : C) {K L : C} (f : L ⟶ K) :
    F.map ((H.map f.op).app M) ≫ component T H adj S J adj' F μ L M =
      component T H adj S J adj' F μ K M ≫ (J.map (F.map f).op).app (F.obj M) := by
  apply adj'.homEquiv.symm.injective
  rw [adj'.homEquiv_symm_naturality_two, adj'.homEquiv_symm_naturality_one]
  simp only [component, Equiv.symm_apply_apply]
  rw [← Category.assoc, hμ₂, Category.assoc]
  conv_rhs => rw [← Category.assoc, hμ₁, Category.assoc]
  simp only [← F.map_comp]
  congr 1
  exact F.congr_map (NatTrans.congr_app (adj.whiskerLeft_map_counit f) M).symm

include hμ₂ in
private theorem natural₂ {M N : C} (g : M ⟶ N) (K : C) :
    F.map ((H.obj (op K)).map g) ≫ component T H adj S J adj' F μ K N =
      component T H adj S J adj' F μ K M ≫ (J.obj (op (F.obj K))).map (F.map g) := by
  apply adj'.homEquiv.symm.injective
  rw [adj'.homEquiv_symm_naturality_two, adj'.homEquiv_symm_naturality_three]
  simp only [component, Equiv.symm_apply_apply]
  rw [← Category.assoc, hμ₂]
  simp only [Category.assoc, ← F.map_comp]
  congr 1
  exact F.congr_map ((adj.adj K).counit.naturality g)

private def transformation (M : C) : H.flip.obj M ⋙ F ⟶ F.op ⋙ J.flip.obj (F.obj M) where
  app K := component T H adj S J adj' F μ K.unop M
  naturality {_K _L} f := natural₁ T H adj S J adj' F μ hμ₁ hμ₂ M f.unop

private theorem transformation_natural {M N : C} (g : M ⟶ N) (K : C) :
    F.map ((H.obj (op K)).map g) ≫
        (transformation T H adj S J adj' F μ hμ₁ hμ₂ N).app (op K) =
      (transformation T H adj S J adj' F μ hμ₁ hμ₂ M).app (op K) ≫
        (J.obj (op (F.obj K))).map (F.map g) :=
  natural₂ T H adj S J adj' F μ hμ₂ g K

include hμ₁ hμ₂ in
private theorem exists_transformation :
    ∃ v : ∀ M : C, H.flip.obj M ⋙ F ⟶ F.op ⋙ J.flip.obj (F.obj M),
      (∀ M K : C,
        (μ K ((H.obj (op K)).obj M)).hom ≫ F.map ((adj.adj K).counit.app M) =
          ((adj'.adj (F.obj K)).homEquiv _ _).symm ((v M).app (op K))) ∧
      (∀ {M N : C} (g : M ⟶ N) (K : C),
        F.map ((H.obj (op K)).map g) ≫ (v N).app (op K) =
          (v M).app (op K) ≫ (J.obj (op (F.obj K))).map (F.map g)) := by
  refine ⟨transformation T H adj S J adj' F μ hμ₁ hμ₂, ?_, ?_⟩
  · intro M K
    exact (adj'.homEquiv.symm_apply_apply _).symm
  · intro M N g K
    exact transformation_natural T H adj S J adj' F μ hμ₁ hμ₂ g K

end HomComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem tensorComparison_natural (X : Scheme.{u}) (φ : A →+* B) :
    IsEtaleHomTensorCanonical X φ (etaleHomTensorComparison X φ) :=
  by
    unfold etaleHomTensorComparison
    exact (etaleHomTensorComparison_existsUnique X φ).choose_spec.1

private theorem exactTransformation_isoLocus
    {C : Type w₁} {D : Type w₂} [Category.{v} C] [Category.{w} D]
    [HasShift C ℤ] [HasShift D ℤ] [HasZeroObject C] [HasZeroObject D]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated] (v : F ⟶ G) [NatTrans.CommShift v ℤ] :
    (∀ K : C, IsZero K → IsIso (v.app K)) ∧
    (∀ {K L : C} (_e : K ≅ L), IsIso (v.app K) ↔ IsIso (v.app L)) ∧
    (∀ (K : C) (n : ℤ), IsIso (v.app K) → IsIso (v.app (K⟦n⟧))) ∧
    (∀ T : Triangle C, T ∈ distTriang C →
      IsIso (v.app T.obj₁) → IsIso (v.app T.obj₂) → IsIso (v.app T.obj₃)) ∧
    (∀ {K L : C} (i : K ⟶ L) (r : L ⟶ K),
      i ≫ r = 𝟙 K → IsIso (v.app L) → IsIso (v.app K)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K hK
    exact (Functor.map_isZero F hK).isIso
      (Functor.map_isZero G hK) (v.app K)
  · intro K L e
    exact v.isIso_app_iff_of_iso e
  · intro K n hK
    let := hK
    rw [NatTrans.app_shift v n K]
    infer_instance
  · intro T hT h₁ h₂
    let t : F.mapTriangle.obj T ⟶
        G.mapTriangle.obj T :=
      { hom₁ := v.app T.obj₁
        hom₂ := v.app T.obj₂
        hom₃ := v.app T.obj₃
        comm₁ := v.naturality T.mor₁
        comm₂ := v.naturality T.mor₂
        comm₃ := by
          change (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
            (v.app T.obj₁)⟦1⟧' =
              v.app T.obj₃ ≫ G.map T.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁
          rw [Category.assoc, NatTrans.shift_app_comm,
            ← Category.assoc, v.naturality, Category.assoc] }
    exact isIso₃_of_isIso₁₂ t
      (F.map_distinguished T hT)
      (G.map_distinguished T hT) h₁ h₂
  · intro K L i r hir hL
    let := hL
    refine ⟨⟨G.map i ≫ inv (v.app L) ≫
      F.map r, ?_, ?_⟩⟩
    · rw [← v.naturality_assoc, IsIso.hom_inv_id_assoc,
        ← Functor.map_comp, hir, F.map_id]
    · rw [Category.assoc, Category.assoc, v.naturality,
        IsIso.inv_hom_id_assoc, ← Functor.map_comp, hir, G.map_id]

private theorem thickLocus_of_reversedExact (X : Scheme.{u}) (φ : A →+* B)
    (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M)
    (hv : IsEtaleHomReversedExact X φ M v) : IsEtaleHomThickIsoLocus X φ M v := by
  let := etaleHomScalarCommShift X φ
  obtain ⟨sA, sB, sF, sG, _, _, _, _, hF, hG, hs⟩ := hv
  let := sF
  let := sG
  let := hF
  let := hG
  let := hs
  exact exactTransformation_isoLocus v

/--
For every coefficient map and every fixed coefficient object, scalar extension of the
derived internal Hom admits the evaluation-defined comparison with the internal Hom of
the scalar extensions.  The comparison is natural in both variables, its two
contravariant functors are exact with their canonical shifts (hence carry every
distinguished triangle to the reversed triangle, including the connecting sign), and
its isomorphism locus is thick: zero, isomorphisms, all integer shifts, cones, and
retracts.  No flatness assumption on `φ` is made.

Source: blueprint lemma-change-coefficients-internal-hom--1, proof paragraph 2 (localization
reduction), and Stacks 06YY, 07A4, 08J9, 08JC; expanded proof steps 1--9 of this node.

Proof:
1. The canonical comparison on flat-term K-flat models is coefficient multiplication;
   use its uniqueness theorem above. The scalar shift is its counit-compatible one.
2. Transpose scalar extension of the evaluation counit along the B tensor-Hom
   adjunction. K-injective target models compute the given internal Hom.
3. Naturality of evaluation, scalar balancing and the adjunction gives naturality in
   K and M on all derived morphisms, by injectivity of transposition.
4. On Hom complexes the source-shift map is f ↦ (-1)^a f in degree a (node's H ⊗ K
   order, shift one). In the library's K ⊗ H order, for shift n it is
   f ↦ (-1)^(n*j + n*(n+1)/2) f in degree j, and the tensor cancellation has the sign
   (-1)^(p*n) on K^p. Their evaluation equation is precisely
   EtaleHomShiftNormalization. K-flat/K-injective models descend this equation.
5. Transpose the shift square. Both sides reduce to the evaluation equation in step 4
   and the degree-preserving scalar balancing formula in step 1. Iterate for all integers.
6. The cone calculation gives the reversed distinguished triangles. Naturality gives
   their first two squares; the shift square gives their third, retaining its reversal sign.
7. Exact functors preserve zero; naturality preserves invertibility under isomorphisms;
   the normalized shift square preserves invertibility under every integer shift.
8. Two-out-of-three for the resulting morphism of triangles gives closure under cones.
9. For i : K → L and r : L → K with ri = 1, the inverse at K is
   Phi(i) v_L inverse Psi(r). Naturality verifies both inverse identities, giving retract
   closure. No flatness, boundedness, or idempotent-completeness hypothesis is used.
(blueprint: lem-coef-etale-hom-thick-locus)
-/
theorem etaleHomComparison_thickLocus (X : Scheme.{u}) (φ : A →+* B) :
    ∃ (v : ∀ M : DerivedCategoryModule A X,
      EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M),
      (∀ M : DerivedCategoryModule A X,
        IsEtaleHomTranspose X φ M (v M) ∧
          IsEtaleHomReversedExact X φ M (v M) ∧
          IsEtaleHomThickIsoLocus X φ M (v M)) ∧
        IsEtaleHomNaturalInM X φ v := by
  obtain ⟨v, ht, hn⟩ := HomComparison.exists_transformation
    (derivedTensor (ModuleCat.{u + 1} A) X) (derivedHom (ModuleCat.{u + 1} A) X)
    (derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} A) X)
    (derivedTensor (ModuleCat.{u + 1} B) X) (derivedHom (ModuleCat.{u + 1} B) X)
    (derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} B) X)
    (scalarExtension φ X) (etaleHomTensorComparison X φ)
    (tensorComparison_natural X φ).1 (tensorComparison_natural X φ).2.1
  refine ⟨v, ?_, hn⟩
  intro M
  have htranspose : IsEtaleHomTranspose X φ M (v M) := ht M
  have he := etaleHomComparison_reversedExact X φ M (v M) htranspose
  exact ⟨htranspose, he, thickLocus_of_reversedExact X φ M _ he⟩

end AlgebraicGeometry.Etale
