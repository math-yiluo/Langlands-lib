/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingle

/-!
# Morphisms from `P[0]` for a projective object `P`

Let `P` be a projective object of an abelian category `C`. For `X` in the derived category,
taking `H⁰` induces a bijection `(P[0] ⟶ X) ≃ (P ⟶ H⁰(X))`
(`DerivedCategory.singleFunctorZeroHomEquiv`). Indeed, `P[0]` is K-projective, so that a
morphism `P[0] ⟶ Q(K)` is the image of a morphism of complexes `f : P[0] ⟶ K`, i.e. of a
morphism `P ⟶ Z⁰(K)`. The induced map `P ⟶ H⁰(K)` is its composition with `Z⁰(K) ⟶ H⁰(K)`.
Surjectivity follows from the projectivity of `P`, and if the composition vanishes, the morphism
`P ⟶ Z⁰(K)` factors through `K⁻¹`, which gives a null-homotopy of `f`.

## Main definitions

- `DerivedCategory.singleFunctorZeroHomEquiv`: the bijection `(P[0] ⟶ X) ≃ (P ⟶ H⁰(X))`.
-/

@[expose] public section

open CategoryTheory Limits Category CochainComplex HomComplex

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- A morphism `Q.obj K ⟶ Q.obj L` in the derived category from a K-projective complex `K` is
the image of a morphism of complexes. -/
lemma exists_Q_map_eq_of_isKProjective (K L : CochainComplex C ℤ) [K.IsKProjective]
    (φ : Q.obj K ⟶ Q.obj L) : ∃ (f : K ⟶ L), Q.map f = φ := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient C (.up ℤ)).obj L)).2
      ((quotientCompQhIso C).hom.app K ≫ φ ≫ (quotientCompQhIso C).inv.app L)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g
  refine ⟨f, ?_⟩
  have := (quotientCompQhIso C).hom.naturality f
  dsimp at this hg
  rw [← cancel_epi ((quotientCompQhIso C).hom.app K), ← this, hg]
  simp

variable (C) in
lemma singleFunctorCompHomologyFunctorIso_inv_app_zero (A : C) :
    (singleFunctorCompHomologyFunctorIso C 0).inv.app A =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 A).inv ≫
        (homologyFunctorFactors C 0).inv.app ((HomologicalComplex.single C (.up ℤ) 0).obj A) := by
  have : (singleFunctorCompHomologyFunctorIso C 0).hom.app A =
      (homologyFunctorFactors C 0).hom.app ((HomologicalComplex.single C (.up ℤ) 0).obj A) ≫
        (HomologicalComplex.homologyFunctorSingleIso C (.up ℤ) 0).hom.app A := by
    simp only [singleFunctorCompHomologyFunctorIso, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.mapIso_hom,
      SingleFunctors.evaluation_map, singleFunctorsPostcompQIso_hom_hom, NatTrans.id_app,
      Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
    erw [CategoryTheory.Functor.map_id, id_comp, id_comp]
  rw [← cancel_mono ((singleFunctorCompHomologyFunctorIso C 0).hom.app A), Iso.inv_hom_id_app,
    this]
  simp

omit [HasDerivedCategory C] in
/-- The morphism `P ⟶ H⁰(K)` induced by a morphism of complexes `f : P[0] ⟶ K` is the
composition of the morphism `P ⟶ Z⁰(K)` given by `f` and of `Z⁰(K) ⟶ H⁰(K)`. -/
lemma singleObjHomologySelfIso_inv_homologyMap (P : C) {K : CochainComplex C ℤ}
    (f : (HomologicalComplex.single C (.up ℤ) 0).obj P ⟶ K) :
    (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 P).inv ≫
      HomologicalComplex.homologyMap f 0 =
      K.liftCycles ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0) 1 (by simp)
        (by rw [assoc, f.comm, HomologicalComplex.single_obj_d, zero_comp, comp_zero]) ≫
        K.homologyπ 0 := by
  have h : (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 P).inv ≫
      HomologicalComplex.cyclesMap f 0 =
      K.liftCycles ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0) 1 (by simp)
        (by rw [assoc, f.comm, HomologicalComplex.single_obj_d, zero_comp, comp_zero]) := by
    rw [← cancel_mono (K.iCycles 0)]
    simp
  rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ_assoc,
    HomologicalComplex.homologyπ_naturality, reassoc_of% h]

/-- The morphism `P ⟶ H⁰(Q(K))` induced by a morphism of complexes `f : P[0] ⟶ K`. -/
lemma singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map_Q_map (P : C)
    {K : CochainComplex C ℤ} (f : (HomologicalComplex.single C (.up ℤ) 0).obj P ⟶ K) :
    (singleFunctorCompHomologyFunctorIso C 0).inv.app P ≫ (homologyFunctor C 0).map (Q.map f) =
      K.liftCycles ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0) 1 (by simp)
        (by rw [assoc, f.comm, HomologicalComplex.single_obj_d, zero_comp, comp_zero]) ≫
        K.homologyπ 0 ≫ (homologyFunctorFactors C 0).inv.app K := by
  have h : (homologyFunctor C 0).map (Q.map f) =
      (homologyFunctorFactors C 0).hom.app _ ≫ HomologicalComplex.homologyMap f 0 ≫
        (homologyFunctorFactors C 0).inv.app K := by
    rw [← homologyFunctorFactors_hom_naturality_assoc]
    simp
  refine (congrArg₂ (· ≫ ·) (singleFunctorCompHomologyFunctorIso_inv_app_zero C P) h).trans ?_
  rw [assoc, Iso.inv_hom_id_app_assoc]
  exact (reassoc_of% (singleObjHomologySelfIso_inv_homologyMap P f)) _

omit [HasDerivedCategory C] in
/-- A morphism of complexes `f : P[0] ⟶ K` is null-homotopic if the corresponding morphism
`P ⟶ K⁰` factors through `K⁻¹`. -/
lemma nonempty_homotopy_zero_of_single {P : C} {K : CochainComplex C ℤ}
    (f : (CochainComplex.singleFunctor C 0).obj P ⟶ K) (h : P ⟶ K.X (-1))
    (hf : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0 = h ≫ K.d (-1) 0) :
    Nonempty (Homotopy f 0) := by
  refine ⟨(Cochain.equivHomotopy f 0).symm ⟨Cochain.fromSingleMk h (p := 0) (by simp), ?_⟩⟩
  rw [Cochain.δ_fromSingleMk _ _ 0 0 (by simp), Cochain.ofHom_zero, add_zero]
  apply (Cochain.fromSingleEquiv (X := P) (K := K) (p := 0) (q := 0) (n := 0) (by simp)).injective
  simpa [Cochain.fromSingleEquiv] using hf


/-- For a projective object `P`, the map `(P[0] ⟶ Q(K)) → (P ⟶ H⁰(Q(K)))` induced by `H⁰` is
bijective. -/
lemma bijective_singleFunctorCompHomologyFunctorIso_inv_app_comp_Q_obj (P : C) [Projective P]
    (K : CochainComplex C ℤ) :
    Function.Bijective fun (φ : (singleFunctor C 0).obj P ⟶ Q.obj K) ↦
      ((singleFunctorCompHomologyFunctorIso C 0).inv.app P ≫ (homologyFunctor C 0).map φ :
        P ⟶ (homologyFunctor C 0).obj (Q.obj K)) := by
  have : CochainComplex.IsKProjective ((HomologicalComplex.single C (.up ℤ) 0).obj P) :=
    inferInstanceAs ((CochainComplex.singleFunctor C 0).obj P).IsKProjective
  have hK := ShortComplex.exact_of_g_is_cokernel (ShortComplex.mk (K.toCycles (-1) 0)
    (K.homologyπ 0) (by simp)) (K.homologyIsCokernel (-1) 0 (by simp))
  refine ⟨fun φ₁ φ₂ h ↦ ?_, fun ψ ↦ ?_⟩
  · rw [← sub_eq_zero]
    obtain ⟨f, hf⟩ := exists_Q_map_eq_of_isKProjective
      ((HomologicalComplex.single C (.up ℤ) 0).obj P) K (φ₁ - φ₂)
    replace h : (singleFunctorCompHomologyFunctorIso C 0).inv.app P ≫
        (homologyFunctor C 0).map (Q.map f) = 0 := by
      rw [hf, Functor.map_sub, Preadditive.comp_sub, sub_eq_zero]
      exact h
    rw [singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map_Q_map,
      ← assoc, Preadditive.IsIso.comp_right_eq_zero] at h
    obtain ⟨g⟩ := nonempty_homotopy_zero_of_single f (hK.liftFromProjective _ h) (by
      rw [← HomologicalComplex.toCycles_i, ← assoc, hK.liftFromProjective_comp,
        HomologicalComplex.liftCycles_i])
    rw [← hf, Q_map_eq_of_homotopy (C := C) g, Functor.map_zero]
  · obtain ⟨x, hx'⟩ : ∃ x, x ≫ K.homologyπ 0 = ψ ≫ (homologyFunctorFactors C 0).hom.app K :=
      ⟨_, Projective.factorThru_comp _ _⟩
    let f := HomologicalComplex.mkHomFromSingle (x ≫ K.iCycles 0) (fun k _ ↦ by simp)
    refine ⟨Q.map f, ?_⟩
    have hx : K.liftCycles ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0) 1
        (by simp) (by simp [f]) = x := by
      rw [← cancel_mono (K.iCycles 0), HomologicalComplex.liftCycles_i]
      simp [f]
    dsimp only
    rw [singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map_Q_map, hx,
      reassoc_of% hx', Iso.hom_inv_id_app]
    exact comp_id ψ


/-- For a projective object `P` and `X` in the derived category, the map
`(P[0] ⟶ X) → (P ⟶ H⁰(X))` induced by `H⁰` is bijective. -/
lemma bijective_singleFunctorCompHomologyFunctorIso_inv_app_comp (P : C) [Projective P]
    (X : DerivedCategory C) :
    Function.Bijective fun (φ : (singleFunctor C 0).obj P ⟶ X) ↦
      ((singleFunctorCompHomologyFunctorIso C 0).inv.app P ≫ (homologyFunctor C 0).map φ :
        P ⟶ (homologyFunctor C 0).obj X) := by
  let e := Q.objObjPreimageIso X
  have : (fun (φ : (singleFunctor C 0).obj P ⟶ X) ↦
      ((singleFunctorCompHomologyFunctorIso C 0).inv.app P ≫ (homologyFunctor C 0).map φ :
        P ⟶ (homologyFunctor C 0).obj X)) =
      ((Iso.refl P).homCongr ((homologyFunctor C 0).mapIso e)) ∘
        (fun (φ : (singleFunctor C 0).obj P ⟶ Q.obj (Q.objPreimage X)) ↦
          ((singleFunctorCompHomologyFunctorIso C 0).inv.app P ≫ (homologyFunctor C 0).map φ :
            P ⟶ (homologyFunctor C 0).obj (Q.obj (Q.objPreimage X)))) ∘
        ((Iso.refl _).homCongr e).symm := by
    ext φ
    simp [← Functor.map_comp]
  rw [this]
  exact (Equiv.bijective _).comp
    ((bijective_singleFunctorCompHomologyFunctorIso_inv_app_comp_Q_obj P _).comp
      (Equiv.bijective _))

/-- For a projective object `P` and `X` in the derived category, taking `H⁰` induces a bijection
`(P[0] ⟶ X) ≃ (P ⟶ H⁰(X))`. -/
noncomputable def singleFunctorZeroHomEquiv (P : C) [Projective P] (X : DerivedCategory C) :
    ((singleFunctor C 0).obj P ⟶ X) ≃ (P ⟶ (homologyFunctor C 0).obj X) :=
  Equiv.ofBijective _ (bijective_singleFunctorCompHomologyFunctorIso_inv_app_comp P X)

@[simp]
lemma singleFunctorZeroHomEquiv_apply (P : C) [Projective P] {X : DerivedCategory C}
    (φ : (singleFunctor C 0).obj P ⟶ X) :
    singleFunctorZeroHomEquiv P X φ =
      (singleFunctorCompHomologyFunctorIso C 0).inv.app P ≫ (homologyFunctor C 0).map φ :=
  rfl

end DerivedCategory
