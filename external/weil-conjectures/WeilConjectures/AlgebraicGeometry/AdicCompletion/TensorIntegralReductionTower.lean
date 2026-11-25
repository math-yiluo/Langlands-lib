/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import all WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Algebra.Homology.BifunctorSingleNaturality

/-! # Tensor associativity for the internal integral reduction tower

Source: blueprint latest, det-lem-int-tensor-product.proof.md, first paragraph.
(blueprint: lem-sfb-tensor-integral-reduction-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale.AdicCompletion

attribute [local irreducible] upperStarFromPoint

private def tensorRightComplex {C : Type*} [Category C] [MonoidalCategory C]
    [Preadditive C] [MonoidalPreadditive C] (P : CochainComplex C ℤ) :
    C ⥤ CochainComplex C ℤ where
  obj B := ((tensorRight B).mapHomologicalComplex (.up ℤ)).obj P
  map f := (NatTrans.mapHomologicalComplex ((tensoringRight C).map f) (.up ℤ)).app P
  map_id B := by ext; simp
  map_comp f g := by ext; simp

private def tensorSingleIso {C : Type v} [Category.{w} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory C]
    (P : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    DerivedCategory.singleFunctor C 0 ⋙ tensorLeft (DerivedCategory.Q.obj P) ≅
      tensorRightComplex P ⋙ DerivedCategory.Q := by
  have hPk : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
      ((HomotopyCategory.quotient C (.up ℤ)).obj P) :=
    (HomotopyCategory.kFlat_quotient_obj_iff _).2 hP
  have hμ (Z : CochainComplex C ℤ) :
      IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Z) := by
    have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj Z)) :=
      DerivedMonoidal.isIso_counit_app_app_of_kFlat_left DerivedCategory.Qh
        (HomotopyCategory.quasiIso C (.up ℤ)) _ _ hPk
    change IsIso ((_ ⊗ₘ _) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
    infer_instance
  let t : DerivedCategory.Q ⋙ tensorLeft (DerivedCategory.Q.obj P) ≅
      tensorLeft P ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun Z ↦ asIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Z))
      (fun f ↦ Functor.LaxMonoidal.μ_natural_right DerivedCategory.Q P f)
  let a : HomologicalComplex.single C (.up ℤ) 0 ⋙ tensorLeft P ≅
      tensorRightComplex P :=
    NatIso.ofComponents
      (fun B ↦ CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) B P)
      (fun f ↦ CochainComplex.mapBifunctorSingle₂Iso_hom_naturality₂
        (curriedTensor C) f P)
  exact Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ C 0) _ ≪≫
    Functor.isoWhiskerLeft (HomologicalComplex.single C (.up ℤ) 0) t ≪≫
    Functor.isoWhiskerRight a DerivedCategory.Q

private def coefficientTower
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (S : Scheme.{u}) :
    ℕᵒᵖ ⥤ Modules l E S :=
  Functor.ofOpSequence (X := finiteModule l E S)
    (fun n ↦ (DerivedNakayama.pullback l E S).map (quotientStep l E n))

private theorem reductionTensorTowerIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (S : Scheme.{u})
    (K : DerivedCategory (Modules l E S)) :
    Nonempty (coefficientTower l E S ⋙ DerivedCategory.singleFunctor (Modules l E S) 0 ⋙
      tensorLeft K ≅ derivedTower l E S K) := by
  classical
  obtain ⟨P, f, hf, _, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage K)
  have : QuasiIso f := hf
  let eP := asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨e, hstep, _⟩ := strictScalarRealization l E S K P hP eP
  let t : DerivedCategory.singleFunctor (Modules l E S) 0 ⋙ tensorLeft K ≅
      tensorRightComplex P ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (Modules l E S) 0)
      ((curriedTensor _).mapIso eP.symm) ≪≫ tensorSingleIso P hP
  let e' (n : ℕ) := t.app (finiteModule l E S n) ≪≫ e n
  let nt : coefficientTower l E S ⋙ DerivedCategory.singleFunctor (Modules l E S) 0 ⋙
      tensorLeft K ⟶ derivedTower l E S K :=
    NatTrans.ofOpSequence (fun n ↦ (e' n).hom) (by
      intro n
      have hn := t.hom.naturality
        ((DerivedNakayama.pullback l E S).map (quotientStep l E n))
      simp only [Functor.comp_map] at hn
      simp only [Functor.comp_map, coefficientTower, derivedTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      dsimp only [Functor.comp_obj, Functor.ofOpSequence_obj]
      dsimp only [e', Iso.trans_hom]
      erw [← Category.assoc, hn, Category.assoc]
      simpa only [Category.assoc, tensorRightComplex, levelStep, finiteModule,
        Iso.app_hom] using
        congrArg ((t.app (finiteModule l E S (n + 1))).hom ≫ ·) (hstep n))
  exact ⟨NatIso.ofComponents (fun n ↦ e' n.unop) (fun f ↦ by exact nt.naturality f)⟩

/-- Tensoring the canonical reduction tower agrees with reducing the tensor product.
No completeness, dualizability or inverse-limit hypothesis occurs in this statement.

Source: blueprint latest, det-lem-int-tensor-product.proof.md, first paragraph,
"It also commutes with reduction ... by associativity of the derived tensor product."
(blueprint: lem-sfb-tensor-integral-reduction-tower).

Proof: for each derived object K choose a K-flat representative P. The localization
lax tensorator, invertible with K-flat left argument, and the single-complex tensor
comparison give a natural isomorphism K tensor B[0] ≅ Q(P tensor B). The coherent
scalar realization then identifies the coefficient tower tensored with K with the
actual integral reduction tower of K. Naturality in B and the scalar realization's
transition equation prove the consecutive transition squares; NatTrans.ofOpSequence
packages them as a natural isomorphism. Apply this construction to N and M tensor N.
Between these two descriptions, the inverse derived associator identifies
M tensor (N tensor B[0]) with (M tensor N) tensor B[0], naturally in B. Whisker the
first comparison by tensorLeft M and compose these three isomorphisms. No completeness
or dualizability is used; the construction also applies to zero objects and the empty
scheme. -/
theorem tensorIntegralReductionTower
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) (M N : DerivedCategory (Modules l E S)) :
    Nonempty (derivedTower l E S N ⋙ tensorLeft M ≅ derivedTower l E S (M ⊗ N)) := by
  classical
  obtain ⟨eN⟩ := reductionTensorTowerIso l E S N
  obtain ⟨eMN⟩ := reductionTensorTowerIso l E S (M ⊗ N)
  let a : (coefficientTower l E S ⋙ DerivedCategory.singleFunctor (Modules l E S) 0 ⋙
      tensorLeft N) ⋙ tensorLeft M ≅
      coefficientTower l E S ⋙ DerivedCategory.singleFunctor (Modules l E S) 0 ⋙
        tensorLeft (M ⊗ N) :=
    NatIso.ofComponents (fun B ↦ (α_ M N
      ((DerivedCategory.singleFunctor (Modules l E S) 0).obj
        ((coefficientTower l E S).obj B))).symm)
  exact ⟨Functor.isoWhiskerRight eN.symm (tensorLeft M) ≪≫ a ≪≫ eMN⟩

end AlgebraicGeometry.ProEtale.AdicCompletion
