/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableTransfer

/-!
# Transport of acyclicity of K-injectives along equivalences

Let `P : C' ⥤ C` and `F : C ⥤ D` be additive functors. The property "for every K-injective
complex `I` and every quasi-isomorphism `P(I) ⟶ J` to a K-injective complex `J`, the map
`F(P I) ⟶ F(J)` is a quasi-isomorphism" is invariant under replacing the three categories by
equivalent ones, compatibly with `P` and `F` up to natural isomorphism.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C' C D C'₁ C₁ D₁ : Type*} [Category* C'] [Category* C] [Category* D]
  [Category* C'₁] [Category* C₁] [Category* D₁]
  [Abelian C'] [Abelian C] [Abelian D] [Abelian C'₁] [Abelian C₁] [Abelian D₁]

/-- The acyclicity condition on `F` for images of K-injective complexes under `P`. -/
def KInjectiveImageAcyclic (P : C' ⥤ C) (F : C ⥤ D) [P.Additive] [F.Additive] : Prop :=
  ∀ (I : CochainComplex C' ℤ) [I.IsKInjective] (J : CochainComplex C ℤ) [J.IsKInjective]
    (j : (P.mapHomologicalComplex _).obj I ⟶ J) [QuasiIso j],
    QuasiIso ((F.mapHomologicalComplex _).map j)

/-- An additive equivalence preserves K-injective complexes. -/
theorem isKInjective_map_of_equivalence (e : C ≌ C₁) [e.functor.Additive]
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective ((e.functor.mapHomologicalComplex (.up ℤ)).obj I) := by
  have : e.symm.functor.Additive := e.inverse_additive
  exact CochainComplex.isKInjective_map_of_adjunction e.functor e.symm.toAdjunction I

/-- The componentwise isomorphism of complexes `G(F K) ≅ G'(F' K)` induced by a natural
isomorphism `F ⋙ G ≅ F' ⋙ G'`. -/
def mapHomologicalComplexCompIso' {A B B' E : Type*} [Category* A] [Category* B]
    [Category* B'] [Category* E] [Preadditive A] [Preadditive B] [Preadditive B']
    [Preadditive E] {F : A ⥤ B} {G : B ⥤ E} {F' : A ⥤ B'} {G' : B' ⥤ E}
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    (α : F ⋙ G ≅ F' ⋙ G') (K : CochainComplex A ℤ) :
    (G.mapHomologicalComplex _).obj ((F.mapHomologicalComplex _).obj K) ≅
      (G'.mapHomologicalComplex _).obj ((F'.mapHomologicalComplex _).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ α.app (K.X n))
    (fun i j _ ↦ (α.hom.naturality (K.d i j)).symm)

/-- The acyclicity condition is transported along equivalences commuting with the functors
up to natural isomorphism. -/
theorem KInjectiveImageAcyclic.of_equivalence
    (e' : C' ≌ C'₁) (e : C ≌ C₁) (eD : D ≌ D₁)
    [e'.functor.Additive] [e.functor.Additive] [eD.functor.Additive]
    {P : C' ⥤ C} {F : C ⥤ D} {P₁ : C'₁ ⥤ C₁} {F₁ : C₁ ⥤ D₁}
    [P.Additive] [F.Additive] [P₁.Additive] [F₁.Additive]
    (α : P ⋙ e.functor ≅ e'.functor ⋙ P₁) (β : F ⋙ eD.functor ≅ e.functor ⋙ F₁)
    (h : KInjectiveImageAcyclic P₁ F₁) : KInjectiveImageAcyclic P F := by
  intro I _ J _ j _
  have : e.functor.PreservesHomology := inferInstance
  have : eD.functor.PreservesHomology := inferInstance
  have := isKInjective_map_of_equivalence e' I
  have := isKInjective_map_of_equivalence e J
  let j₁ := (mapHomologicalComplexCompIso' α I).inv ≫ (e.functor.mapHomologicalComplex _).map j
  have : QuasiIso j₁ := by
    have : QuasiIso (mapHomologicalComplexCompIso' α I).inv := quasiIso_of_isIso _
    exact quasiIso_comp _ _
  have hj₁ := h _ _ j₁
  have hF : QuasiIso ((eD.functor.mapHomologicalComplex _).map
      ((F.mapHomologicalComplex _).map j)) := by
    refine (quasiIso_iff_of_arrow_mk_iso _ ((F₁.mapHomologicalComplex _).map j₁) ?_).2 hj₁
    refine Arrow.isoMk (mapHomologicalComplexCompIso' β _ ≪≫
      (F₁.mapHomologicalComplex _).mapIso (mapHomologicalComplexCompIso' α I))
      (mapHomologicalComplexCompIso' β J) ?_
    ext n
    have hn := β.hom.naturality (j.f n)
    dsimp at hn
    simp only [j₁, mapHomologicalComplexCompIso', Arrow.mk_hom, Iso.trans_hom, Functor.mapIso_hom,
      Functor.mapHomologicalComplex_map_f, HomologicalComplex.comp_f, Functor.map_comp,
      Category.assoc]
    erw [← F₁.map_comp_assoc, Iso.hom_inv_id_app, F₁.map_id, Category.id_comp]
    exact hn.symm
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ eD.functor).1 hF

end CategoryTheory.Functor
