/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Morphisms out of a projective object placed in one degree

Let `P` be a projective object of an abelian category `C`. For every `n : ℤ` and every object
`X` of the derived category `D(C)`, taking `n`-th homology identifies morphisms
`P[-n] ⟶ X` in `D(C)` with morphisms `P ⟶ Hⁿ(X)` in `C`
(`DerivedCategory.homSingleEquivOfProjective`).

The complex `P[-n]` is K-projective, so a morphism `P[-n] ⟶ X` comes from a morphism of
complexes, that is from a morphism `P ⟶ Xⁿ` landing in the cycles. Projectivity of `P` lets
such a morphism be lifted from homology to cycles (surjectivity) and makes it null-homotopic
when it vanishes in homology, as it then factors through the boundaries (injectivity).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The map `Hom(P[-n], X) ⟶ Hom(P, Hⁿ(X))` given by taking `n`-th homology. -/
noncomputable def homSingleToHomology (P : C) (n : ℤ) (X : DerivedCategory C)
    (φ : (singleFunctor C n).obj P ⟶ X) : P ⟶ (homologyFunctor C n).obj X :=
  ((singleFunctorCompHomologyFunctorIso C n).app P).inv ≫ (homologyFunctor C n).map φ

/-- `homSingleToHomology` is natural in the target: for `φ : P[-n] ⟶ X` and `ψ : X ⟶ Y`, the
morphism `P ⟶ Hⁿ(Y)` attached to `φ ≫ ψ` is the one attached to `φ` followed by `Hⁿ(ψ)`. -/
lemma homSingleToHomology_comp (P : C) (n : ℤ) {X Y : DerivedCategory C}
    (φ : (singleFunctor C n).obj P ⟶ X) (ψ : X ⟶ Y) :
    homSingleToHomology P n Y (φ ≫ ψ) =
      homSingleToHomology P n X φ ≫ (homologyFunctor C n).map ψ := by
  simp [homSingleToHomology]

/-- The isomorphism `Hⁿ(Q(P[-n])) ≅ P` of `singleFunctorCompHomologyFunctorIso`, computed on the
complex `P[-n]`: it is the comparison `Hⁿ(Q(P[-n])) ≅ Hⁿ(P[-n])` of `homologyFunctorFactors`
followed by `HomologicalComplex.singleObjHomologySelfIso`. -/
lemma singleFunctorCompHomologyFunctorIso_hom_app (P : C) (n : ℤ) :
    (singleFunctorCompHomologyFunctorIso C n).hom.app P =
      (homologyFunctorFactors C n).hom.app ((HomologicalComplex.single C _ n).obj P) ≫
        (HomologicalComplex.singleObjHomologySelfIso _ n P).hom := by
  simp only [Functor.comp_obj, Functor.id_obj, singleFunctorCompHomologyFunctorIso,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.mapIso_hom, SingleFunctors.evaluation_map,
    singleFunctorsPostcompQIso_hom_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, NatTrans.id_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, HomologicalComplex.homologyFunctorSingleIso_hom_app, Q_obj_single_obj]
  erw [(homologyFunctor C n).map_id, Category.id_comp, Category.id_comp]

/-- Let `a : P ⟶ Lⁿ` be a morphism landing in the cycles of `L`, and `P[-n] ⟶ L` the morphism of
complexes it defines. The following square commutes, where the left map is
`homSingleToHomology` of `Q(P[-n] ⟶ L)` and the bottom map is `homologyFunctorFactors`:
```
P ─────────── a ──────────→ Zⁿ(L)
│                             │
↓                             ↓
Hⁿ(Q L) ────────────────→ Hⁿ(L)
```
-/
lemma homSingleToHomology_Q_map_mkHomFromSingle (P : C) (n : ℤ) (L : CochainComplex C ℤ)
    (a : P ⟶ L.X n) (ha : ∀ j, (ComplexShape.up ℤ).Rel n j → a ≫ L.d n j = 0) :
    homSingleToHomology P n (Q.obj L) (Q.map (HomologicalComplex.mkHomFromSingle a ha)) ≫
        (homologyFunctorFactors C n).hom.app L =
      L.liftCycles a (n + 1) (by simp) (ha _ rfl) ≫ L.homologyπ n := by
  have key : ((singleFunctorCompHomologyFunctorIso C n).app P).inv ≫
      (homologyFunctorFactors C n).hom.app ((HomologicalComplex.single C _ n).obj P) =
        (HomologicalComplex.singleObjHomologySelfIso _ n P).inv := by
    rw [Iso.inv_comp_eq, Iso.app_hom, singleFunctorCompHomologyFunctorIso_hom_app, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [homSingleToHomology, Category.assoc, homologyFunctorFactors_hom_naturality]
  erw [reassoc_of% key]
  rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ, Category.assoc,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  congr 1
  rw [← cancel_mono (L.iCycles n), Category.assoc, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc,
    HomologicalComplex.mkHomFromSingle_f, Iso.inv_hom_id_assoc, HomologicalComplex.liftCycles_i]

variable (P : C) [Projective P] (n : ℤ)

instance isKProjective_single_obj_of_projective :
    CochainComplex.IsKProjective ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj P) := by
  have (i : ℤ) : Projective (((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj P).X i) := by
    by_cases hi : i = n
    · exact Projective.of_iso (HomologicalComplex.singleObjXIsoOfEq _ n P i hi).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X _ n P i hi).projective
  have :
      CochainComplex.IsStrictlyLE ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj P) n :=
    inferInstanceAs (CochainComplex.IsStrictlyLE ((CochainComplex.singleFunctor C n).obj P) n)
  exact CochainComplex.isKProjective_of_projective _ n

lemma bijective_homSingleToHomology_Q_obj (L : CochainComplex C ℤ) :
    Function.Bijective (homSingleToHomology P n (Q.obj L)) := by
  constructor
  · intro φ₁ φ₂ h
    rw [← sub_eq_zero]
    have hz : homSingleToHomology P n _ (φ₁ - φ₂) = 0 := by
      simp only [homSingleToHomology, Functor.map_sub, Preadditive.comp_sub] at h ⊢
      rw [h, sub_self]
    obtain ⟨f, hf⟩ := CochainComplex.IsKProjective.exists_Q_map_eq
      ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj P) L (φ₁ - φ₂)
    rw [← hf] at hz ⊢
    let a := (HomologicalComplex.singleObjXSelf _ n P).inv ≫ f.f n
    have ha (j : ℤ) (_ : (ComplexShape.up ℤ).Rel n j) : a ≫ L.d n j = 0 := by
      simp [a]
    have hfa : f = HomologicalComplex.mkHomFromSingle a ha := by
      ext
      simp [a]
    rw [hfa] at hz ⊢
    have hπ : L.liftCycles a (n + 1) (by simp) (ha _ rfl) ≫ L.homologyπ n = 0 := by
      rw [← homSingleToHomology_Q_map_mkHomFromSingle, hz, zero_comp]
    let S := ShortComplex.mk (L.toCycles (n - 1) n) (L.homologyπ n) (by simp)
    have hS : S.Exact := S.exact_of_g_is_cokernel (L.homologyIsCokernel (n - 1) n (by simp))
    let h := hS.liftFromProjective (L.liftCycles a (n + 1) (by simp) (ha _ rfl)) hπ
    have hh : h ≫ L.d (n - 1) n = a := by
      rw [← L.toCycles_i (n - 1) n, ← Category.assoc,
        hS.liftFromProjective_comp (L.liftCycles a (n + 1) (by simp) (ha _ rfl)) hπ,
        HomologicalComplex.liftCycles_i]
    let h' : ∀ i j, (ComplexShape.up ℤ).Rel j i →
        (((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj P).X i ⟶ L.X j) :=
      fun i j hij ↦ if hi : i = n then
        (HomologicalComplex.singleObjXIsoOfEq _ n P i hi).hom ≫ h ≫
          (L.XIsoOfEq (show n - 1 = j by simp at hij; omega)).hom
      else 0
    have hnull : HomologicalComplex.mkHomFromSingle a ha = Homotopy.nullHomotopicMap' h' := by
      ext
      rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)
        (show (ComplexShape.up ℤ).Rel n (n + 1) by simp)]
      simp only [← hh, HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.singleObjXSelf,
        HomologicalComplex.single_obj_d, add_eq_left, one_ne_zero, ↓reduceDIte, comp_zero,
        HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.assoc, zero_add,
        Iso.cancel_iso_hom_left, h']
      erw [Category.id_comp]
    rw [hnull, Q_map_eq_of_homotopy _ (Homotopy.nullHomotopy' h'), Functor.map_zero]
  · intro g
    let t := Projective.factorThru (g ≫ (homologyFunctorFactors C n).hom.app L) (L.homologyπ n)
    have ht (j : ℤ) (_ : (ComplexShape.up ℤ).Rel n j) : (t ≫ L.iCycles n) ≫ L.d n j = 0 := by
      simp
    refine ⟨Q.map (HomologicalComplex.mkHomFromSingle (t ≫ L.iCycles n) ht), ?_⟩
    rw [← cancel_mono ((homologyFunctorFactors C n).hom.app L),
      homSingleToHomology_Q_map_mkHomFromSingle]
    have : L.liftCycles (t ≫ L.iCycles n) (n + 1) (by simp) (ht _ rfl) = t := by
      rw [← cancel_mono (L.iCycles n), HomologicalComplex.liftCycles_i]
    rw [this, Projective.factorThru_comp]

/-- For a projective object `P` of an abelian category `C`, taking `n`-th homology is a bijection
between morphisms `P[-n] ⟶ X` in the derived category and morphisms `P ⟶ Hⁿ(X)` in `C`. -/
noncomputable def homSingleEquivOfProjective (X : DerivedCategory C) :
    ((singleFunctor C n).obj P ⟶ X) ≃ (P ⟶ (homologyFunctor C n).obj X) :=
  Equiv.ofBijective (homSingleToHomology P n X) (by
    let e := Q.objObjPreimageIso X
    have : homSingleToHomology P n X =
        ⇑((Iso.refl _).homCongr ((homologyFunctor C n).mapIso e)) ∘
          homSingleToHomology P n (Q.obj (Q.objPreimage X)) ∘ ⇑((Iso.refl _).homCongr e.symm) := by
      funext φ
      simp [Iso.homCongr_apply, ← homSingleToHomology_comp]
    rw [this]
    exact ((Iso.refl _).homCongr ((homologyFunctor C n).mapIso e)).bijective.comp
      ((bijective_homSingleToHomology_Q_obj P n _).comp
        ((Iso.refl _).homCongr e.symm).bijective))

@[simp]
lemma homSingleEquivOfProjective_apply (X : DerivedCategory C)
    (φ : (singleFunctor C n).obj P ⟶ X) :
    homSingleEquivOfProjective P n X φ = homSingleToHomology P n X φ :=
  rfl

end DerivedCategory
