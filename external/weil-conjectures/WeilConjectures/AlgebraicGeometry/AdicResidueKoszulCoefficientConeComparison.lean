/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import WeilConjectures.AlgebraicGeometry.AdicResidueQuotientTensorTower
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
import WeilConjectures.AlgebraicGeometry.AdicResidueExactCoefficientRealization
import WeilConjectures.CategoryTheory.AdditiveConeFamilyComparison
import WeilConjectures.CategoryTheory.ExteriorKoszulScalarRealization
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Single

/-! # Finite coefficient comparison for normalized Koszul augmentations

Source: Stacks Project, proetale.tex, lemma-naive-completion (099M), and
more-algebra.tex, lemma-sequence-Koszul-complexes.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

/-- Keep the coefficient category abstract during the degree-zero calculation. -/
private theorem augmentationComparisonOfZero
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (E : C ⥤ D) [E.Additive]
    {K L : CochainComplex C ℤ} {T Q : CochainComplex D ℤ}
    (f : K ⟶ L) (ε : T ⟶ Q)
    (eK : (E.mapHomologicalComplex (.up ℤ)).obj K ≅ T)
    (eQ : (E.mapHomologicalComplex (.up ℤ)).obj L ≅ Q)
    {V Z : C} {M : D} (vK : V ≅ K.X 0) (vL : L.X 0 ≅ Z) (π : V ⟶ Z)
    (c : M ≅ E.obj V) (w : E.obj Z ⟶ Q.X 0) (ρ : M ⟶ T.X 0) (p : M ⟶ Q.X 0)
    (hf : vK.hom ≫ f.f 0 ≫ vL.hom = π)
    (heQ : eQ.hom.f 0 = E.map vL.hom ≫ w)
    (hu : c.hom ≫ E.map vK.hom ≫ eK.hom.f 0 = ρ)
    (hp : c.hom ≫ E.map π ≫ w = p) (hε : ρ ≫ ε.f 0 = p)
    (hex : ∀ g h : (E.mapHomologicalComplex (.up ℤ)).obj K ⟶ Q,
      g.f 0 = h.f 0 → g = h) :
    (E.mapHomologicalComplex (.up ℤ)).map f ≫ eQ.hom = eK.hom ≫ ε := by
  apply hex
  apply (cancel_epi (c.hom ≫ E.map vK.hom)).1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    heQ, Category.assoc]
  rw [← E.map_comp_assoc, ← E.map_comp_assoc, Category.assoc, hf]
  have hun := congrArg (fun z ↦ z ≫ ε.f 0) hu
  simp only [Category.assoc] at hun
  rw [hun, hε, hp]

/-- Compute the single-complex comparison before specializing the coefficient category. -/
private theorem mapExtendSingleIso_hom_f_zero
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (E : C ⥤ D) [E.Additive] (M : C) {N : D} (e : E.obj M ≅ N) :
    (((E.mapHomologicalComplex (.up ℤ)).mapIso
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat M 0 0 rfl) ≪≫
      (HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).app M ≪≫
      (HomologicalComplex.single D (.up ℤ) 0).mapIso e).hom.f 0) =
      E.map (((ChainComplex.single₀ C).obj M).extendXIso
        ComplexShape.embeddingDownNat (i := 0) rfl).hom ≫
        e.hom ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv := by
  simp only [Iso.trans_hom, Iso.app_hom, HomologicalComplex.comp_f,
    Functor.mapIso_hom, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.extendSingleIso_hom_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self, Category.assoc,
    Iso.inv_hom_id_assoc, ← E.map_comp_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id, ChainComplex.single₀ObjXSelf,
    Iso.refl_hom]

/-- Normalized units determine an augmentation into a single complex. -/
private theorem augmentationComparisonToSingle
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (E : C ⥤ D) [E.Additive]
    {K L : CochainComplex C ℤ} {T : CochainComplex D ℤ} {N W : D}
    (f : K ⟶ L) (ε : T ⟶ (HomologicalComplex.single D (.up ℤ) 0).obj N)
    (eK : (E.mapHomologicalComplex (.up ℤ)).obj K ≅ T)
    (eQ : (E.mapHomologicalComplex (.up ℤ)).obj L ≅
      (HomologicalComplex.single D (.up ℤ) 0).obj N)
    {V Z : C} (vK : V ≅ K.X 0) (vL : L.X 0 ≅ Z) (π : V ⟶ Z)
    (c : W ≅ E.obj V) (q : E.obj Z ≅ N)
    (u : (HomologicalComplex.single D (.up ℤ) 0).obj W ⟶ T)
    (p : (HomologicalComplex.single D (.up ℤ) 0).obj W ⟶
      (HomologicalComplex.single D (.up ℤ) 0).obj N)
    (hf : vK.hom ≫ f.f 0 ≫ vL.hom = π)
    (heQ : eQ.hom.f 0 =
      E.map vL.hom ≫ q.hom ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv)
    (hu : c.hom ≫ E.map vK.hom ≫ eK.hom.f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 W).inv ≫ u.f 0)
    (hp : c.hom ≫ E.map π ≫ q.hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 W).inv ≫ p.f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).hom)
    (hε : u ≫ ε = p) :
    (E.mapHomologicalComplex (.up ℤ)).map f ≫ eQ.hom = eK.hom ≫ ε := by
  have hp' := congrArg
    (fun z ↦ z ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv) hp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hp'
  have hn := congrArg (fun z ↦
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 W).inv ≫ z.f 0) hε
  simp only [HomologicalComplex.comp_f] at hn
  exact augmentationComparisonOfZero E f ε eK eQ vK vL π c
    (q.hom ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv)
    _ _ hf heQ hu hp' (by simpa only [Category.assoc] using hn)
    (fun _ _ h ↦ HomologicalComplex.to_single_hom_ext h)

/-- Compare extended augmentations using only their normalized degree-zero maps. -/
private theorem normalizedExtendedAugmentationComparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (E : C ⥤ D) [E.Additive] {K : ChainComplex C ℕ} {V Z : C}
    (v : V ≅ K.X 0) (f : K ⟶ (ChainComplex.single₀ C).obj Z) (π : V ⟶ Z)
    {T : CochainComplex D ℤ} {N W : D}
    (ε : T ⟶ (HomologicalComplex.single D (.up ℤ) 0).obj N)
    (eK : (E.mapHomologicalComplex (.up ℤ)).obj
      (K.extend ComplexShape.embeddingDownNat) ≅ T)
    (c : W ≅ E.obj V) (q : E.obj Z ≅ N)
    (u : (HomologicalComplex.single D (.up ℤ) 0).obj W ⟶ T)
    (p : (HomologicalComplex.single D (.up ℤ) 0).obj W ⟶
      (HomologicalComplex.single D (.up ℤ) 0).obj N)
    (hf : v.hom ≫ f.f 0 = π)
    (hu : c.hom ≫ E.map
        (v.hom ≫ (K.extendXIso ComplexShape.embeddingDownNat (i := 0) rfl).inv) ≫
      eK.hom.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 W).inv ≫ u.f 0)
    (hp : c.hom ≫ E.map π ≫ q.hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 W).inv ≫ p.f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).hom)
    (hε : u ≫ ε = p) :
    (E.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap f ComplexShape.embeddingDownNat) ≫
      (((E.mapHomologicalComplex (.up ℤ)).mapIso
          (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat Z 0 0 rfl) ≪≫
        (HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).app Z ≪≫
        (HomologicalComplex.single D (.up ℤ) 0).mapIso q).hom) = eK.hom ≫ ε := by
  apply augmentationComparisonToSingle E _ ε eK _
    (v ≪≫ (K.extendXIso ComplexShape.embeddingDownNat (i := 0) rfl).symm)
    (((ChainComplex.single₀ C).obj Z).extendXIso
      ComplexShape.embeddingDownNat (i := 0) rfl) π c q u p
  · simp only [Iso.trans_hom, Iso.symm_hom,
      HomologicalComplex.extendMap_f f ComplexShape.embeddingDownNat (i := 0) (i' := 0) rfl,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    exact hf
  · exact mapExtendSingleIso_hom_f_zero E Z q
  · exact hu
  · exact hp
  · exact hε

/-- Extension preserves an augmentation which is epimorphic in degree zero. -/
private theorem epi_extendMap_single_of_epi_zero
    {C : Type*} [Category C] [Abelian C] {K : ChainComplex C ℕ} {M : C}
    (f : K ⟶ (ChainComplex.single₀ C).obj M) [Epi (f.f 0)] :
    Epi (HomologicalComplex.extendMap f ComplexShape.embeddingDownNat) := by
  have hepi (k : ℕ) : Epi (f.f k) := by
    cases k with
    | zero => infer_instance
    | succ k =>
      exact (HomologicalComplex.isZero_single_obj_X (.down ℕ) 0 M (k + 1)
        (by omega)).epi _
  apply HomologicalComplex.epi_of_epi_f
  intro i
  by_cases hi : ∃ k, ComplexShape.embeddingDownNat.f k = i
  · obtain ⟨k, hk⟩ := hi
    rw [HomologicalComplex.extendMap_f _ _ hk]
    infer_instance
  · exact (HomologicalComplex.isZero_extend_X _ _ i (by simpa using hi)).epi _

/-- Assemble normalized finite cone comparisons in abstract coefficient categories. -/
private theorem normalizedExtendedConeFamilyComparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (E : C ⥤ D) [E.Additive] [PreservesFiniteColimits E]
    (K : ℕ → ChainComplex C ℕ) (B : ℕ → C)
    (f : ∀ n, K n ⟶ (ChainComplex.single₀ C).obj (B n))
    (t : ∀ n m : ℕ, n ≤ m → (K m ⟶ K n))
    (qA : ∀ n m : ℕ, n ≤ m →
      ((ChainComplex.single₀ C).obj (B m) ⟶ (ChainComplex.single₀ C).obj (B n)))
    (hc : ∀ n m h,
      HomologicalComplex.extendMap (t n m h) ComplexShape.embeddingDownNat ≫
        HomologicalComplex.extendMap (f n) ComplexShape.embeddingDownNat =
      HomologicalComplex.extendMap (f m) ComplexShape.embeddingDownNat ≫
        HomologicalComplex.extendMap (qA n m h) ComplexShape.embeddingDownNat)
    (N : ℕ → D) (ν : ∀ n, N (n + 1) ⟶ N n)
    {T : ℕᵒᵖ ⥤ CochainComplex D ℤ}
    (ε : T ⟶ Functor.ofOpSequence
      (X := fun n ↦ (HomologicalComplex.single D (.up ℤ) 0).obj (N n))
      (fun n ↦ (HomologicalComplex.single D (.up ℤ) 0).map (ν n)))
    (eK : ∀ n, (E.mapHomologicalComplex (.up ℤ)).obj
      ((K n).extend ComplexShape.embeddingDownNat) ≅ T.obj (op n))
    (ht : ∀ n m h, (E.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap (t n m h) ComplexShape.embeddingDownNat) ≫
      (eK n).hom = (eK m).hom ≫ T.map (homOfLE h).op)
    {V : C} {W : D} (v : ∀ n, V ≅ (K n).X 0) (π : ∀ n, V ⟶ B n)
    (hπ : ∀ n, Epi (π n)) (hf : ∀ n, (v n).hom ≫ (f n).f 0 = π n)
    (c : W ≅ E.obj V) (q : ∀ n, E.obj (B n) ≅ N n)
    (u : ∀ n, (HomologicalComplex.single D (.up ℤ) 0).obj W ⟶ T.obj (op n))
    (p : ∀ n, (HomologicalComplex.single D (.up ℤ) 0).obj W ⟶
      (HomologicalComplex.single D (.up ℤ) 0).obj (N n))
    (hu : ∀ n, c.hom ≫ E.map ((v n).hom ≫
        ((K n).extendXIso ComplexShape.embeddingDownNat (i := 0) rfl).inv) ≫
      (eK n).hom.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 W).inv ≫ (u n).f 0)
    (hp : ∀ n, c.hom ≫ E.map (π n) ≫ (q n).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 W).inv ≫ (p n).f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (N n)).hom)
    (hε : ∀ n, u n ≫ ε.app (op n) = p n) :
    ∃ e : ∀ n, (E.mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.homotopyCofiber
          (HomologicalComplex.extendMap (f n) ComplexShape.embeddingDownNat)) ≅
      (CochainComplex.mappingCone
        ((HomologicalComplex.functorEquivalence D (.up ℤ) ℕᵒᵖ).inverse.map ε)).asFunctor.obj
          (op n),
      ∀ n m h, (E.mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom
            (HomologicalComplex.extendMap (f m) ComplexShape.embeddingDownNat)
            (HomologicalComplex.extendMap (f n) ComplexShape.embeddingDownNat)
            (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
            (Arrow.homMk
              (HomologicalComplex.extendMap (t n m h) ComplexShape.embeddingDownNat)
              (HomologicalComplex.extendMap (qA n m h) ComplexShape.embeddingDownNat)
              (hc n m h))) ≫ (e n).hom =
        (e m).hom ≫ (CochainComplex.mappingCone
          ((HomologicalComplex.functorEquivalence D (.up ℤ) ℕᵒᵖ).inverse.map ε)).asFunctor.map
            (homOfLE h).op := by
  let H := E.mapHomologicalComplex (.up ℤ)
  let eQ (n : ℕ) :=
    H.mapIso (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
      (B n) 0 0 rfl) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).app (B n) ≪≫
    (HomologicalComplex.single D (.up ℤ) 0).mapIso (q n)
  have haug (n : ℕ) :
      H.map (HomologicalComplex.extendMap (f n) ComplexShape.embeddingDownNat) ≫
        (eQ n).hom = (eK n).hom ≫ ε.app (op n) :=
    normalizedExtendedAugmentationComparison E (v n) (f n) (π n)
      (ε.app (op n)) (eK n) c (q n) (u n) (p n) (hf n) (hu n) (hp n) (hε n)
  have hfepi (n : ℕ) :
      Epi (H.map (HomologicalComplex.extendMap (f n) ComplexShape.embeddingDownNat)) := by
    have := hπ n
    have : Epi ((f n).f 0) := epi_of_epi_fac (hf n)
    have := epi_extendMap_single_of_epi_zero (f n)
    infer_instance
  exact additiveConeFamilyComparison E
    (fun n ↦ (K n).extend ComplexShape.embeddingDownNat)
    (fun n ↦ ((ChainComplex.single₀ C).obj (B n)).extend ComplexShape.embeddingDownNat)
    (fun n ↦ HomologicalComplex.extendMap (f n) ComplexShape.embeddingDownNat)
    (fun n m h ↦ HomologicalComplex.extendMap (t n m h) ComplexShape.embeddingDownNat)
    (fun n m h ↦ HomologicalComplex.extendMap (qA n m h) ComplexShape.embeddingDownNat)
    hc ε eK eQ haug ht hfepi

attribute [local irreducible] homComplexFunctor ringedKoszulDualTower
  completed ringedKoszulDualUnit adicResidueQuotientCoefficientUnit
  adicResidueQuotientModule

/-- Specialize the finite comparison to the ideal generated by the Koszul sequence. -/
private theorem adicResidueConeComparison_span
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (r : ℕ) (a : Fin r → A)
    (εA : ∀ n : ℕ, ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (n + 1)) ⟶
      (ChainComplex.single₀ (ModuleCat.{max v (u + 1)} A)).obj
        (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (n + 1))))
    (tA : ∀ n m : ℕ, n ≤ m →
      (ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (m + 1)) ⟶
        ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (n + 1))))
    (qA : ∀ n m : ℕ, n ≤ m →
      ((ChainComplex.single₀ (ModuleCat.{max v (u + 1)} A)).obj
          (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (m + 1))) ⟶
        (ChainComplex.single₀ (ModuleCat.{max v (u + 1)} A)).obj
          (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (n + 1)))))
    (hεA : ∀ n, (εA n).f 0 = ModuleCat.ofHom
      (((Ideal.span (Set.range a)) ^ (n + 1)).mkQ.comp
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap))
    (htA : ∀ n m h k, (tA n m h).f k = ModuleCat.ofHom
      (exteriorPower.map k
        (Finsupp.linearCombination A (fun i ↦ Finsupp.single i (a i ^ (m - n))))))
    (hc : ∀ n m h,
      HomologicalComplex.extendMap (tA n m h) ComplexShape.embeddingDownNat ≫
        HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat =
      HomologicalComplex.extendMap (εA m) ComplexShape.embeddingDownNat ≫
        HomologicalComplex.extendMap (qA n m h) ComplexShape.embeddingDownNat) :
    let R := (completed (coefficientProEtaleModelTopology.{u, v} X) A
      (Ideal.span (Set.range a))).over U
    let b := fun i ↦ ringedKoszulSliceSection
      (completed (coefficientProEtaleModelTopology.{u, v} X) A (Ideal.span (Set.range a)))
      (algebraSection (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A
        (Ideal.span (Set.range a))) (a i)) U
    ∀ (ε : ringedKoszulDualTower R r b ⟶
        adicResidueQuotientCoefficientTower X (Ideal.span (Set.range a)) U)
      (_hε : ∀ n : ℕ, ringedKoszulDualUnit R r b n ≫ ε.app (op n) =
        (show ringedSiteRingComplex R ⟶
          (adicResidueQuotientCoefficientTower X (Ideal.span (Set.range a)) U).obj (op n) from
          adicResidueQuotientCoefficientUnit X (Ideal.span (Set.range a)) U n)),
    ∃ (E : ModuleCat.{max v (u + 1)} A ⥤ Mod R) (_hadd : E.Additive)
      (_hlim : PreservesFiniteLimits E) (_hcolim : PreservesFiniteColimits E)
      (e : ∀ n : ℕ,
        (E.mapHomologicalComplex (.up ℤ)).obj
          (HomologicalComplex.homotopyCofiber
            (HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat)) ≅
          (CochainComplex.mappingCone
            ((HomologicalComplex.functorEquivalence
              (Mod R) (.up ℤ) ℕᵒᵖ).inverse.map ε)).asFunctor.obj
              (op n)),
      ∀ (n m : ℕ) (h : n ≤ m),
        (E.mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom
            (HomologicalComplex.extendMap (εA m) ComplexShape.embeddingDownNat)
            (HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat)
            (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
            (Arrow.homMk
              (HomologicalComplex.extendMap (tA n m h) ComplexShape.embeddingDownNat)
              (HomologicalComplex.extendMap (qA n m h) ComplexShape.embeddingDownNat)
              (hc n m h))) ≫ (e n).hom =
        (e m).hom ≫
          (CochainComplex.mappingCone
            ((HomologicalComplex.functorEquivalence
              (Mod R) (.up ℤ) ℕᵒᵖ).inverse.map ε)).asFunctor.map
              (homOfLE h).op  := by
  intro O b ε hε
  obtain ⟨E, hadd, hlim, hcolim, c, q, hs, hq⟩ :=
    adicResidue_exact_coefficient_realization X (Ideal.span (Set.range a)) U
  let s := fun x : A ↦ ringedKoszulSliceSection
    (completed (coefficientProEtaleModelTopology.{u, v} X) A (Ideal.span (Set.range a)))
    (algebraSection (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A
      (Ideal.span (Set.range a))) x) U
  obtain ⟨eK, ht, hu⟩ := exteriorKoszul_scalar_realization O E c s hs r a tA htA
  refine ⟨E, hadd, hlim, hcolim, ?_⟩
  apply normalizedExtendedConeFamilyComparison E
    (fun n ↦ ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (n + 1)))
    (fun n ↦ ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (n + 1)))
    εA tA qA hc
    (adicResidueQuotientModule X (Ideal.span (Set.range a)) U)
    (adicResidueQuotientModuleStep X (Ideal.span (Set.range a)) U)
    ε eK ht (fun _ ↦ (exteriorPower.zeroEquiv A (Fin r →₀ A)).toModuleIso.symm)
    (fun n ↦ ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (n + 1)).mkQ)
    ?_ ?_ c q (ringedKoszulDualUnit O r b)
    (adicResidueQuotientCoefficientUnit X (Ideal.span (Set.range a)) U) hu hq hε
  · intro n
    exact (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
  · intro n
    rw [hεA n]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (((Ideal.span (Set.range a)) ^ (n + 1)).mkQ)
      ((exteriorPower.zeroEquiv A (Fin r →₀ A)).apply_symm_apply x)


/-- Exact realization identifies the finite algebraic augmentation cones and their
strict transitions with those of any normalized coefficient augmentation.
This is a finite comparison: it asserts no eventual vanishing, uses no complex P,
and makes no assertion about derived inverse limits.

Source: Stacks Project, proetale.tex, proof of lemma-naive-completion (099M);
more-algebra.tex, lemma-sequence-Koszul-complexes; algebraization.tex,
lemma-derived-completion-koszul (0A0E).
(auxiliary; not a blueprint node).

Proof: take E to be exact commutative constant-module realization, followed by
extension to the completed coefficient sheaf and restriction to the slice U.
The first functor is exact by module sheafification; the second is exact by
flat_and_quotients, and slice restriction is exact. The same quotient theorem
identifies E(A/J^(n+1)) with the actual quotient module on the slice. These
identifications are induced by the projections, hence commute with qA.
Identify the exterior complex with the ordered tensor of negative two-term
complexes by splitting wedges according to their first basis vector. A wedge
on an increasing subset maps to its tensor basis vector. This respects the
contraction differential and sends the exterior diagonal tA to the product of
its diagonal coefficients on that subset. Constant realization, extension and
slice restriction preserve these finite tensor coordinates. The finite free
evaluation pairing identifies this negative tensor with the internal dual of
the positive Koszul tensor; the empty-subset basis vector is the dual unit.
A map to a degree-zero complex has only its degree-zero component, and this
unit is invertible in degree zero. Thus the normalization of epsilon makes
the resulting augmentation precisely E(epsilonA). The supplied component
identities uniquely specify epsilonA, tA and qA (for qA use surjectivity of
the quotient map). Consequently all the strict squares agree. The additive
mapping-cone comparison gives e and its naturality for every n <= m.
For r=0 the exterior-degree-zero identification is the entire comparison;
for the zero ring or J=A the same formulas and quotient universal property
apply. No infinite tensor or product occurs. -/
theorem adicResidue_koszul_coefficient_cone_comparison
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = J)
    (εA : ∀ n : ℕ, ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (n + 1)) ⟶
      (ChainComplex.single₀ (ModuleCat.{max v (u + 1)} A)).obj
        (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (n + 1))))
    (tA : ∀ n m : ℕ, n ≤ m →
      (ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (m + 1)) ⟶
        ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (n + 1))))
    (qA : ∀ n m : ℕ, n ≤ m →
      ((ChainComplex.single₀ (ModuleCat.{max v (u + 1)} A)).obj
          (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (m + 1))) ⟶
        (ChainComplex.single₀ (ModuleCat.{max v (u + 1)} A)).obj
          (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (n + 1)))))
    (hεA : ∀ n, (εA n).f 0 = ModuleCat.ofHom
      (((Ideal.span (Set.range a)) ^ (n + 1)).mkQ.comp
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap))
    (htA : ∀ n m h k, (tA n m h).f k = ModuleCat.ofHom
      (exteriorPower.map k
        (Finsupp.linearCombination A (fun i ↦ Finsupp.single i (a i ^ (m - n))))))
    (hqA : ∀ n m h,
      ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (m + 1)).mkQ ≫ (qA n m h).f 0 =
        ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (n + 1)).mkQ)
    (hc : ∀ n m h,
      HomologicalComplex.extendMap (tA n m h) ComplexShape.embeddingDownNat ≫
        HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat =
      HomologicalComplex.extendMap (εA m) ComplexShape.embeddingDownNat ≫
        HomologicalComplex.extendMap (qA n m h) ComplexShape.embeddingDownNat) :
    let R := (completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U
    let b := fun i ↦ ringedKoszulSliceSection
      (completed (coefficientProEtaleModelTopology.{u, v} X) A J)
      (algebraSection (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J)
        (a i)) U
    ∀ (ε : ringedKoszulDualTower R r b ⟶ adicResidueQuotientCoefficientTower X J U)
      (_hε : ∀ n : ℕ, ringedKoszulDualUnit R r b n ≫ ε.app (op n) =
        adicResidueQuotientCoefficientUnit X J U n),
    ∃ (E : ModuleCat.{max v (u + 1)} A ⥤ Mod R) (_hadd : E.Additive)
      (_hlim : PreservesFiniteLimits E) (_hcolim : PreservesFiniteColimits E)
      (e : ∀ n : ℕ,
        (E.mapHomologicalComplex (.up ℤ)).obj
          (HomologicalComplex.homotopyCofiber
            (HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat)) ≅
          (CochainComplex.mappingCone
            ((HomologicalComplex.functorEquivalence
              (Mod R) (.up ℤ) ℕᵒᵖ).inverse.map ε)).asFunctor.obj
              (op n)),
      ∀ (n m : ℕ) (h : n ≤ m),
        (E.mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom
            (HomologicalComplex.extendMap (εA m) ComplexShape.embeddingDownNat)
            (HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat)
            (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
            (Arrow.homMk
              (HomologicalComplex.extendMap (tA n m h) ComplexShape.embeddingDownNat)
              (HomologicalComplex.extendMap (qA n m h) ComplexShape.embeddingDownNat)
              (hc n m h))) ≫ (e n).hom =
        (e m).hom ≫
          (CochainComplex.mappingCone
            ((HomologicalComplex.functorEquivalence
              (Mod R) (.up ℤ) ℕᵒᵖ).inverse.map ε)).asFunctor.map
              (homOfLE h).op  := by
  have _ := hqA
  cases ha
  apply adicResidueConeComparison_span.{u, v} X U r a εA tA qA hεA htA hc

end AlgebraicGeometry.Scheme
