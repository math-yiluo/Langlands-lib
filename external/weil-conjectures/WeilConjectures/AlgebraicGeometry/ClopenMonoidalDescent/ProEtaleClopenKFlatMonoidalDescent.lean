/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenMonoidalNormalization
import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenBraidedModelNormalization
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Normalized clopen monoidal descent

The finite-family equivalence and uniqueness on flat-term K-flat models are proved here.
The remaining normalized braided lift is isolated in its own theorem.
Source: Stacks Project, Tags 06YS, 0G7D, 06YU and 0FPT
(blueprint: lem-pur-clopen-kflat-monoidal-descent).
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures

attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory SheafOfModules.pushforward

namespace AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent

private abbrev TotalComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :=
  coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
    clopenTensorComplexRestriction.{t, u} j R ≅
    ((clopenTensorComplexRestriction.{t, u} j R).prod
      (clopenTensorComplexRestriction.{t, u} j R)) ⋙
        coefficientTotalTensor.{u, t + 1, t} (topology Y) ((clopenTensorRings.{t, u} j).obj R)

private theorem comparison_unique {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (hk : ∀ P : CochainComplex (clopenTensorModules.{t, u} R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P →
      CochainComplex.IsKFlatIndependentCoefficients (J := topology Y)
        (R := (clopenTensorRings.{t, u} j).obj R)
        ((clopenTensorComplexRestriction.{t, u} j R).obj P))
    (b : coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
        clopenTensorComplexRestriction.{t, u} j R ≅
      ((clopenTensorComplexRestriction.{t, u} j R).prod
        (clopenTensorComplexRestriction.{t, u} j R)) ⋙
          coefficientTotalTensor.{u, t + 1, t} (topology Y)
            ((clopenTensorRings.{t, u} j).obj R))
    (c c' : Comparison.{t, u} j R)
    (h : ModelNormalization.{t, u} j R b c)
    (h' : ModelNormalization.{t, u} j R b c') : c' = c := by
  have hrep (P Q : CochainComplex (clopenTensorModules.{t, u} R) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) Q)
      (hfP : ∀ n, SheafOfModules.IsFlatOnSite (J := topology X) (R := R) (P.X n))
      (hfQ : ∀ n, SheafOfModules.IsFlatOnSite (J := topology X) (R := R) (Q.X n)) :
      c'.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        c.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := by
    apply (cancel_epi ((derivedRestriction.{t, u} j R).map
      (RingedDerivedNative.tensorIso.{t + 1, t, u, max (u + 1) (t + 2)}
        (topology X) R P Q (Or.inl hP)).hom)).1
    apply (cancel_mono (tensorHom ((factors.{t, u} j R).hom.app P)
      ((factors.{t, u} j R).hom.app Q))).1
    simpa only [Category.assoc] using
      (h' P Q hP hQ hfP hfQ (hk P hP)).trans
        (h P Q hP hQ hfP hfQ (hk P hP)).symm
  obtain ⟨P, hp, _, _, hext⟩ :=
    SheafOfModules.site_derived_tensor_descent_independentCoefficients
      (topology X) R
  apply Iso.ext
  apply hext _ _ _ _ |>.1
  apply NatTrans.ext
  funext ⟨K, L⟩
  let i := (DerivedCategory.quotientCompQhIso (clopenTensorModules.{t, u} R)).app K.obj.as
  let k := (DerivedCategory.quotientCompQhIso (clopenTensorModules.{t, u} R)).app L.obj.as
  let ik := i.prod k
  have he := hrep K.obj.as L.obj.as ((hp K.obj).mp K.property).1
    ((hp L.obj).mp L.property).1 ((hp K.obj).mp K.property).2
    ((hp L.obj).mp L.property).2
  apply (cancel_epi ((tensor _ ⋙ derivedRestriction.{t, u} j R).map ik.inv)).1
  exact ((c'.hom.naturality ik.inv).trans (by rw [he])).trans
    (c.hom.naturality ik.inv).symm

private theorem equiv_of_inverse {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) (G : B ⥤ A) (η : 𝟭 A ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 B) :
    F.IsEquivalence := (CategoryTheory.Equivalence.mk F G η ε).isEquivalence_functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem equivalence_of_reindex {J K : Type*} {A : Type*} [Category* A]
    (B : J → Type*) [∀ i, Category* (B i)] (F : ∀ i, A ⥤ B i) (e : K ≃ J)
    (h : (Functor.pi' (fun k ↦ F (e k))).IsEquivalence) :
    (Functor.pi' F).IsEquivalence := by
  let reindex := Pi.equivalenceOfEquiv B e
  have : ((Functor.pi' F) ⋙ reindex.inverse).IsEquivalence := h
  exact Functor.isEquivalence_of_comp_right (Functor.pi' F) reindex.inverse

private theorem restriction_equivalence
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hc : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    (Functor.pi' (fun i ↦ derivedRestriction.{t, u} (j i) R)).IsEquivalence := by
  let R' := (sheafCompose _
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R
  have hcomm : ∀ U (x y : R'.obj.obj U), x * y = y * x := fun U x y ↦
    @mul_comm (R.obj.obj U) _ x y
  classical
  let : Fintype I := Fintype.ofFinite I
  let eI := (Fintype.equivFin I).symm
  have hd' : Pairwise (fun a b ↦
      Disjoint (Set.range (j (eI a))) (Set.range (j (eI b)))) :=
    fun _ _ h ↦ hd (eI.injective.ne h)
  have hc' : ∀ x : X, ∃ a, x ∈ Set.range (j (eI a)) := by
    intro x
    obtain ⟨i, hi⟩ := hc x
    refine ⟨eI.symm i, ?_⟩
    rw [eI.apply_symm_apply]
    exact hi
  obtain ⟨_, _, _, _, _, _, _, _, _, G, η, ε, _⟩ :=
    ClopenLocalization.clopen_unbounded_derived_localization.{t, max u (t + 1), u, 0}
      X _ (fun a ↦ Y (eI a)) (fun a ↦ j (eI a)) hd' hc' R' hcomm
  have he := equiv_of_inverse _ G η ε
  exact equivalence_of_reindex
    (fun i ↦ DerivedCategory
      (clopenTensorModules.{t, u} ((clopenTensorRings.{t, u} (j i)).obj R)))
    (fun i ↦ derivedRestriction.{t, u} (j i) R) eI he

attribute [local semireducible] SheafOfModules.pushforward

private theorem generator_eq_summand {X : Scheme.{t}}
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (P Q : CochainComplex (clopenTensorModules.{t, u} R) ℤ)
    (p q n : ℤ) (hpq : p + q = n) (U : X.ProEtᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    coefficientTensorGenerator.{u, t + 1, t} (topology X) R P Q p q n hpq U x y =
      (clopenTotalTensorSummand.{t, u} R P Q p q n hpq).val.app U
        (clopenTensorPure.{t, u} R (P.X p) (Q.X q) U x y) := by
  rfl

attribute [local irreducible] coefficientTotalTensor clopenTotalTensorSummand
  clopenTensorPure

private theorem restriction_map_apply {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    {M N : clopenTensorModules.{t, u} R} (f : M ⟶ N) (U : Y.ProEt)
    (x : M.val.obj (op ((MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale j)).obj U))) :
    (((clopenTensorRestriction.{t, u} j R).map f).val.app (op U)) x =
      (f.val.app (op ((MorphismProperty.Over.map ⊤
        (inferInstance : WeaklyEtale j)).obj U))) x := by
  rfl

private theorem totalNormalization_of_summands
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (clopenTensorRestriction.{t, u} j R).Braided)
    (b : TotalComparison.{t, u} j R)
    (hpure : ∀ (F H : clopenTensorModules.{t, u} R) (U : Y.ProEt)
      (x : F.val.obj (op ((MorphismProperty.Over.map ⊤
        (inferInstance : WeaklyEtale j)).obj U)))
      (y : H.val.obj (op ((MorphismProperty.Over.map ⊤
        (inferInstance : WeaklyEtale j)).obj U))),
      (clopenTensorComparison.{t, u} j R h F H).hom.val.app (op U)
          (clopenTensorPure.{t, u} R F H _ x y) =
        clopenTensorPure.{t, u} ((clopenTensorRings.{t, u} j).obj R)
          ((clopenTensorRestriction.{t, u} j R).obj F)
          ((clopenTensorRestriction.{t, u} j R).obj H) (op U) x y)
    (hsum : ∀ (P Q : CochainComplex (clopenTensorModules.{t, u} R) ℤ)
      (p q n : ℤ) (hpq : p + q = n),
      (clopenTensorRestriction.{t, u} j R).map
          (clopenTotalTensorSummand.{t, u} R P Q p q n hpq) ≫
          (b.hom.app (P, Q)).f n =
        (clopenTensorComparison.{t, u} j R h (P.X p) (Q.X q)).hom ≫
          clopenTotalTensorSummand.{t, u} ((clopenTensorRings.{t, u} j).obj R)
            ((clopenTensorComplexRestriction.{t, u} j R).obj P)
            ((clopenTensorComplexRestriction.{t, u} j R).obj Q) p q n hpq)
    : TotalNormalization.{t, u} j R h b := by
  refine ⟨hpure, ?_⟩
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  intro P Q p q n hpq U x y
  have hs := hsum P Q p q n hpq
  have he := congrArg (fun f ↦ f.val.app (op U)
    (clopenTensorPure.{t, u} R (P.X p) (Q.X q) _ x y)) hs
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, restriction_map_apply] at he
  rw [hpure] at he
  simp only [generator_eq_summand]
  dsimp only [clopenTensorComplexRestriction, Functor.mapHomologicalComplex] at he ⊢
  exact he

attribute [local irreducible] TotalNormalization ModelNormalization
  braidedComparison braidedUnit unitComparison RingedDerivedNative.monoidal
  RingedDerivedNative.symmetric

/-- Clopen restriction has a unique K-flat-normalized derived tensor comparison. Its
inverse is natural for every derived morphism; its tensorator and degree-zero unit make
restriction a symmetric monoidal equivalence for the prescribed native tensor structures.

Source: Stacks sites-cohomology.tex, Tags 06YS, 0G7D, 06YU and 0FPT; normalized
finite-clopen application (blueprint: lem-pur-clopen-kflat-monoidal-descent).

Proof:
1. Reindex the existing finite clopen derived localization equivalence from Fin to I.
2. Tensor detection supplies ordinary braided restriction, a normalized comparison on
   every total summand, preservation of K-flat complexes, and coproduct preservation.
3. Evaluating the summand equation on a local pure tensor proves TotalNormalization.
4. The component braided model-normalization theorem gives the coherent derived lift,
   its computation square, and its canonical unit equation.
5. Cancel the computation and factorization isomorphisms on flat-term K-flat pairs.
   Resolving localization is fully faithful on natural transformations; apply its
   injectivity after transport along quotientCompQhIso to prove uniqueness everywhere.
6. Assemble the component data. No nonempty index or nonzero coefficient is assumed.
-/
theorem clopen_kflat_monoidal_descent
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    (Functor.pi' (fun i ↦ derivedRestriction.{t, u} (j i) R)).IsEquivalence ∧
    ∃ d : ∀ i, (derivedRestriction.{t, u} (j i) R).Braided,
      ∀ i, ∃ (h : (clopenTensorRestriction.{t, u} (j i) R).Braided)
        (b : coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
            clopenTensorComplexRestriction.{t, u} (j i) R ≅
          ((clopenTensorComplexRestriction.{t, u} (j i) R).prod
            (clopenTensorComplexRestriction.{t, u} (j i) R)) ⋙
              coefficientTotalTensor.{u, t + 1, t} (topology (Y i))
                ((clopenTensorRings.{t, u} (j i)).obj R))
        (c : Comparison.{t, u} (j i) R),
        TotalNormalization.{t, u} (j i) R h b ∧
        ModelNormalization.{t, u} (j i) R b c ∧
        (∀ c' : Comparison.{t, u} (j i) R,
          ModelNormalization.{t, u} (j i) R b c' → c' = c) ∧
        braidedComparison.{t, u} (j i) R (d i) = c ∧
        braidedUnit.{t, u} (j i) R (d i) = unitComparison.{t, u} (j i) R h := by
  classical
  refine ⟨restriction_equivalence X I Y j hdisjoint hcover R, ?_⟩
  obtain ⟨_, hk, ht, hcolim, _⟩ :=
    clopen_total_tensor_kflat_detection.{t, u, w} X I Y j hdisjoint hcover R
  refine (Classical.skolem (p := fun i (d : (derivedRestriction.{t, u} (j i) R).Braided) ↦
    ∃ (h : (clopenTensorRestriction.{t, u} (j i) R).Braided)
      (b : TotalComparison.{t, u} (j i) R) (c : Comparison.{t, u} (j i) R),
      TotalNormalization.{t, u} (j i) R h b ∧ ModelNormalization.{t, u} (j i) R b c ∧
      (∀ c' : Comparison.{t, u} (j i) R, ModelNormalization.{t, u} (j i) R b c' → c' = c) ∧
      braidedComparison.{t, u} (j i) R d = c ∧
      braidedUnit.{t, u} (j i) R d = unitComparison.{t, u} (j i) R h)).mp ?_
  intro i
  obtain ⟨h, b, hpure, hsum, _⟩ := ht i
  obtain ⟨d, hm, hu⟩ := clopen_braided_model_normalization.{t, u} (j i) R h b
    hsum (fun P hp ↦ (hk P).1 hp i) (hcolim i)
  refine ⟨d, h, b, braidedComparison.{t, u} (j i) R d, ?_⟩
  exact ⟨totalNormalization_of_summands.{t, u} (j i) R h b hpure hsum,
    hm, fun c' hc' ↦ comparison_unique.{t, u} (j i) R
      (fun P hp ↦ (hk P).1 hp i) b _ c' hm hc', rfl, hu⟩

end AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent
