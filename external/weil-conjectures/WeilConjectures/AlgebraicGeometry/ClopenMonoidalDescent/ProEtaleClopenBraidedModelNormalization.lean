/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenMonoidalNormalization
import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenBraidedLocalization
import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenBraidedCochainNormalization
import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenBraidedModelSquares
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

/-! # Braided lift of clopen restriction with its model square

Source: Stacks Project, Tags 06YS, 0G7D, 06YU and 0FPT.
(blueprint: lem-pur-clopen-braided-model-normalization).
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.Functor.mapCochainComplexMonoidal
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open WeilConjectures

attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory
  RingedDerivedNative.monoidal
  RingedDerivedNative.symmetric HasDerivedCategory.standard SheafOfModules.pushforward

namespace CategoryTheory

open Category Functor.LaxMonoidal Functor.OplaxMonoidal

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem inverse_tensor_square
    {A B D E : Type*} [Category* A] [Category* B] [Category* D] [Category* E]
    [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory D] [MonoidalCategory E]
    (Q : A ⥤ D) (L : B ⥤ E) (F : A ⥤ B) (G : D ⥤ E)
    [Q.LaxMonoidal] [L.LaxMonoidal] [F.Monoidal] [G.Monoidal]
    (e : Q ⋙ G ≅ F ⋙ L) [NatTrans.IsMonoidal e.hom]
    (X Y : A) [IsIso (μ Q X Y)] [IsIso (μ L (F.obj X) (F.obj Y))] :
    G.map (inv (μ Q X Y)) ≫ δ G (Q.obj X) (Q.obj Y) ≫
        (e.hom.app X ⊗ₘ e.hom.app Y) =
      e.hom.app (X ⊗ Y) ≫ L.map (δ F X Y) ≫ inv (μ L (F.obj X) (F.obj Y)) := by
  have hh := NatTrans.IsMonoidal.tensor (τ := e.hom) X Y
  simp only [comp_μ, Functor.comp_obj, Category.assoc] at hh
  apply (cancel_epi (G.map (μ Q X Y))).1
  simp only [← G.map_comp_assoc, IsIso.hom_inv_id, G.map_id, id_comp]
  apply (cancel_epi (μ G (Q.obj X) (Q.obj Y))).1
  simp only [Functor.Monoidal.μ_δ_assoc]
  apply (cancel_mono (μ L (F.obj X) (F.obj Y))).1
  simp only [assoc, IsIso.inv_hom_id, comp_id]
  rw [reassoc_of% hh]
  simp only [← L.map_comp, Functor.Monoidal.μ_δ, L.map_id, comp_id]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem inverse_unit_square
    {A B D E : Type*} [Category* A] [Category* B] [Category* D] [Category* E]
    [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory D] [MonoidalCategory E]
    (Q : A ⥤ D) (L : B ⥤ E) (F : A ⥤ B) (G : D ⥤ E)
    [Q.LaxMonoidal] [L.LaxMonoidal] [F.Monoidal] [G.Monoidal]
    (e : Q ⋙ G ≅ F ⋙ L) [NatTrans.IsMonoidal e.hom]
    [IsIso (ε L)] :
    η G = G.map (ε Q) ≫ e.hom.app (𝟙_ A) ≫ L.map (η F) ≫ inv (ε L) := by
  have hh := NatTrans.IsMonoidal.unit (τ := e.hom)
  simp only [comp_ε, Category.assoc] at hh
  apply (cancel_epi (ε G)).1
  rw [Functor.Monoidal.ε_η, reassoc_of% hh]
  rw [← L.map_comp_assoc, Functor.Monoidal.ε_η, L.map_id, id_comp, IsIso.hom_inv_id]

end CategoryTheory

namespace AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent

attribute [local instance 20000] instMonoidalCategoryHomologicalComplexIntUp_weilConjectures
  RingedDerivedNative.moduleClosed SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive

/-- The summand-normalized total comparison descends to a braided structure on the
specified exact derived restriction, satisfying the K-flat computation square and
canonical degree-zero unit equation.

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 0G7D, 06YU and 0FPT.
(blueprint: lem-pur-clopen-braided-model-normalization).

Proof: Coproduct preservation and exactness give preservation of the countable sums
forming total complexes. The ordinary braided functor therefore induces a braided
functor on signed cochain complexes. Its inverse tensorator agrees with b: precompose
with each total summand, use the displayed summand equation, and apply the direct-sum
universal property. Flat-term K-flat resolutions give the left derivability structure
for the categorical K-flat subcategory. The independent-coefficient K-flat predicate
implies categorical K-flatness, and the converse follows by tensoring the
quasi-isomorphism from zero to an acyclic complex. Thus hk preserves these models.
The native localization is lax braided, with invertible unit and tensorators when one
input is K-flat. Apply normalizedBraidedLocalization to the canonical factorization
factors, obtaining a braided structure whose factorization is monoidal. In its tensor
equation cancel the native tensorators on a K-flat pair. Their inverses are exactly the
native computation isomorphisms, giving ModelNormalization for braidedComparison.
In the unit equation cancel the two native unit maps. The induced cochain unit is the
single-complex restriction of the ordinary ring unit; the resulting composite is
unitComparison. This proves the claimed unit equation. The argument uses neither a
nonzero coefficient ring nor a nonempty scheme. -/
theorem clopen_braided_model_normalization
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (clopenTensorRestriction.{t, u} j R).Braided)
    (b : coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
        clopenTensorComplexRestriction.{t, u} j R ≅
      ((clopenTensorComplexRestriction.{t, u} j R).prod
        (clopenTensorComplexRestriction.{t, u} j R)) ⋙
          coefficientTotalTensor.{u, t + 1, t} (topology Y)
            ((clopenTensorRings.{t, u} j).obj R))
    (hsum : ∀ (P Q : CochainComplex (clopenTensorModules.{t, u} R) ℤ)
      (p q n : ℤ) (hpq : p + q = n),
      (clopenTensorRestriction.{t, u} j R).map
          (clopenTotalTensorSummand.{t, u} R P Q p q n hpq) ≫
          (b.hom.app (P, Q)).f n =
        (clopenTensorComparison.{t, u} j R h (P.X p) (Q.X q)).hom ≫
          clopenTotalTensorSummand.{t, u} ((clopenTensorRings.{t, u} j).obj R)
            ((clopenTensorComplexRestriction.{t, u} j R).obj P)
            ((clopenTensorComplexRestriction.{t, u} j R).obj Q) p q n hpq)
    (hk : ∀ P : CochainComplex (clopenTensorModules.{t, u} R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P →
      CochainComplex.IsKFlatIndependentCoefficients (J := topology Y)
        (R := (clopenTensorRings.{t, u} j).obj R)
        ((clopenTensorComplexRestriction.{t, u} j R).obj P))
    (hcolim : ∀ (K : Type (max u (t + 1))),
      PreservesColimitsOfShape (Discrete K) (clopenTensorRestriction.{t, u} j R)) :
    ∃ d : (derivedRestriction.{t, u} j R).Braided,
      ModelNormalization.{t, u} j R b (braidedComparison.{t, u} j R d) ∧
      braidedUnit.{t, u} j R d = unitComparison.{t, u} j R h  := by
  obtain ⟨c, hcδ, hcη⟩ :=
    clopen_braided_cochain_normalization.{t, u} j R h b hsum hcolim
  obtain ⟨d, hd⟩ := clopen_braided_localization.{t, u} j R c hk
  exact ⟨d, clopen_braided_model_squares.{t, u} j R h b c hcδ hcη d hd⟩

end AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent
