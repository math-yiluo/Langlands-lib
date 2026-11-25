/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.Algebra.Homology.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Right derived functors of a sequence of functors exact on injectives

Let `S : F₁ ⟶ F₂ ⟶ F₃` be a short complex of additive functors `C ⥤ D` between abelian
categories which is short exact on injective objects: `0 ⟶ F₁(I) ⟶ F₂(I) ⟶ F₃(I) ⟶ 0` is
exact for every injective `I`. Then the right derived functors fit, on the bounded below
derived category `D⁺(C)`, in a distinguished triangle

`RF₁(K) ⟶ RF₂(K) ⟶ RF₃(K) ⟶ RF₁(K)[1]`

which is natural in `K` and in `S`. On a bounded below K-injective complex `I` of injectives the
connecting map is the one of the short exact sequence of complexes `0 ⟶ F₁(I) ⟶ F₂(I) ⟶ F₃(I) ⟶ 0`
(`DerivedCategory.triangleOfSESδ`).

## Main definitions

- `CategoryTheory.ShortComplex.ShortExactOnInjectives`
- `CategoryTheory.ShortComplex.rightDerivedδ`: the natural connecting map
  `RF₃ ⟶ RF₁[1]` on `D⁺(C)`.
- `CategoryTheory.ShortComplex.rightDerivedTriangle`: the functor `D⁺(C) ⥤ Triangle D(D)`.
- `CategoryTheory.ShortComplex.rightDerivedTriangleMap`: its functoriality in `S`.

## Main statements

- `CategoryTheory.ShortComplex.rightDerivedTriangle_obj_distinguished`
- `CategoryTheory.ShortComplex.exact_homology_rightDerivedTriangle`
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated DerivedCategory

namespace CochainComplex

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- A morphism `Q(K) ⟶ Q(L)` in the derived category into a K-injective complex `L` is the
image of a morphism of complexes. -/
lemma IsKInjective.exists_Q_map_eq (K L : CochainComplex C ℤ) [L.IsKInjective]
    (g : Q.obj K ⟶ Q.obj L) : ∃ φ : K ⟶ L, Q.map φ = g := by
  obtain ⟨g', hg'⟩ := (IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (.up ℤ)).obj K) L).2
      ((quotientCompQhIso C).hom.app K ≫ g ≫ (quotientCompQhIso C).inv.app L)
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g'
  refine ⟨φ, ?_⟩
  have h := (quotientCompQhIso C).hom.naturality φ
  dsimp at h hg'
  rw [← cancel_epi ((quotientCompQhIso C).hom.app K), ← h, hg']
  simp

end CochainComplex

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- A model of an object `M` of the derived category by a K-injective complex of injective
objects. -/
structure InjectiveModel (M : DerivedCategory C) where
  /-- The K-injective complex of injectives. -/
  I : CochainComplex C ℤ
  injective (n : ℤ) : Injective (I.X n) := by infer_instance
  isKInjective : I.IsKInjective := by infer_instance
  /-- The isomorphism `Q(I) ≅ M`. -/
  iso : Q.obj I ≅ M

attribute [instance] InjectiveModel.injective InjectiveModel.isKInjective

/-- In an abelian category with enough injectives, a bounded below object of the derived
category is modelled by a K-injective complex of injectives. -/
lemma InjectiveModel.nonempty [EnoughInjectives C] (M : DerivedCategory C) (n : ℤ)
    [M.IsGE n] : Nonempty M.InjectiveModel := by
  obtain ⟨L, _, ⟨eL⟩⟩ := M.exists_iso_Q_obj_of_isGE n
  obtain ⟨R, -, hR⟩ := CochainComplex.KInjectiveResolution.exists_of_isStrictlyGE L n
  have : IsIso (Q.map R.ι) := by
    rw [isIso_Q_map_iff_quasiIso]
    infer_instance
  exact ⟨{ I := R.I, injective := hR, iso := (asIso (Q.map R.ι)).symm ≪≫ eL.symm }⟩

/-- A chosen model of an object of the bounded below derived category by a K-injective complex
of injectives. -/
noncomputable def Plus.injectiveModel [EnoughInjectives C] (M : Plus C) :
    M.obj.InjectiveModel :=
  Classical.choice (by
    obtain ⟨n, hn⟩ := M.property
    have : M.obj.IsGE n := hn
    exact InjectiveModel.nonempty M.obj n)

end DerivedCategory

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

section

variable [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]

namespace Functor

/-- On a K-injective complex `I`, the natural transformation `RF ⟶ RG` induced by `τ : F ⟶ G` is
`τ` applied termwise, through the identifications `RF(I) ≅ F(I)` and `RG(I) ≅ G(I)`. -/
lemma rightDerivedFunctorNatTrans_app_Q_obj {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) (I : CochainComplex C ℤ) [I.IsKInjective] :
    (rightDerivedFunctorNatTrans τ).app (DerivedCategory.Q.obj I) ≫
        (G.rightDerivedFunctorObjQIso I).hom =
      (F.rightDerivedFunctorObjQIso I).hom ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ _).app I) := by
  have h₁ := (rightDerivedFunctorNatTrans τ).naturality
    ((DerivedCategory.quotientCompQhIso C).inv.app I)
  have h₂ : F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I) ≫
      (rightDerivedFunctorNatTrans τ).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex τ _).app I)) ≫
        G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I) :=
    rightDerivedNatTrans_app F.rightDerivedFunctor G.rightDerivedFunctor
      F.rightDerivedFunctorUnit G.rightDerivedFunctorUnit
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      (Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ))
        DerivedCategory.Qh) ((HomotopyCategory.quotient _ _).obj I)
  have h₃ := (DerivedCategory.quotientCompQhIso D).hom.naturality
    ((NatTrans.mapHomologicalComplex τ _).app I)
  dsimp at h₁ h₃
  dsimp only [rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  rw [← reassoc_of% h₁]
  simp only [assoc]
  congr 1
  rw [← cancel_epi (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I)),
    IsIso.hom_inv_id_assoc, reassoc_of% h₂, IsIso.hom_inv_id_assoc]
  exact h₃

/-- The identification `RF(Q I) ≅ Q(F I)` on K-injective complexes is natural. -/
@[reassoc]
lemma rightDerivedFunctor_map_Q_map_comp_objQIso_hom (F : C ⥤ D) [F.Additive]
    {I J : CochainComplex C ℤ} [I.IsKInjective] [J.IsKInjective] (φ : I ⟶ J) :
    F.rightDerivedFunctor.map (DerivedCategory.Q.map φ) ≫
        (F.rightDerivedFunctorObjQIso J).hom =
      (F.rightDerivedFunctorObjQIso I).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex _).map φ) := by
  have h₁ := (DerivedCategory.quotientCompQhIso C).inv.naturality φ
  have h₂ := F.rightDerivedFunctorUnit.naturality ((HomotopyCategory.quotient _ _).map φ)
  have h₃ := (DerivedCategory.quotientCompQhIso D).hom.naturality
    ((F.mapHomologicalComplex _).map φ)
  dsimp at h₁ h₂ h₃
  dsimp only [rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  rw [← F.rightDerivedFunctor.map_comp_assoc, h₁, F.rightDerivedFunctor.map_comp, assoc, assoc,
    cancel_epi, assoc, IsIso.eq_inv_comp, ← reassoc_of% h₂]
  simp only [IsIso.hom_inv_id_assoc]
  exact h₃

@[reassoc]
lemma rightDerivedFunctor_map_Q_map_comp_objQIso_inv (F : C ⥤ D) [F.Additive]
    {I J : CochainComplex C ℤ} [I.IsKInjective] [J.IsKInjective] (φ : I ⟶ J) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex _).map φ) ≫
        (F.rightDerivedFunctorObjQIso J).inv =
      (F.rightDerivedFunctorObjQIso I).inv ≫
        F.rightDerivedFunctor.map (DerivedCategory.Q.map φ) := by
  rw [Iso.comp_inv_eq, assoc, rightDerivedFunctor_map_Q_map_comp_objQIso_hom,
    Iso.inv_hom_id_assoc]

lemma rightDerivedFunctorNatTrans_comp {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    (τ : F ⟶ G) (τ' : G ⟶ H) :
    rightDerivedFunctorNatTrans (τ ≫ τ') =
      rightDerivedFunctorNatTrans τ ≫ rightDerivedFunctorNatTrans τ' := by
  simp only [rightDerivedFunctorNatTrans, NatTrans.mapHomotopyCategory_comp,
    Functor.whiskerRight_comp, rightDerivedNatTrans_comp]

end Functor

end

namespace ShortComplex

variable (S : ShortComplex (C ⥤ D)) [S.X₁.Additive] [S.X₂.Additive] [S.X₃.Additive]

/-- The short complex `S.X₁(K) ⟶ S.X₂(K) ⟶ S.X₃(K)` of cochain complexes obtained by applying
the functors of `S` termwise to a cochain complex `K`. -/
@[simps]
noncomputable def mapCochainComplex (K : CochainComplex C ℤ) :
    ShortComplex (CochainComplex D ℤ) :=
  ShortComplex.mk ((NatTrans.mapHomologicalComplex S.f _).app K)
    ((NatTrans.mapHomologicalComplex S.g _).app K) (by
      ext n
      simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
        HomologicalComplex.zero_f]
      rw [← NatTrans.comp_app, S.zero, NatTrans.app_zero])

/-- The morphism `S(K) ⟶ S(L)` of short complexes of cochain complexes induced by a morphism
of complexes `K ⟶ L`. -/
@[simps]
noncomputable def mapCochainComplexMap {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    S.mapCochainComplex K ⟶ S.mapCochainComplex L where
  τ₁ := (S.X₁.mapHomologicalComplex _).map φ
  τ₂ := (S.X₂.mapHomologicalComplex _).map φ
  τ₃ := (S.X₃.mapHomologicalComplex _).map φ
  comm₁₂ := by ext n; simp
  comm₂₃ := by ext n; simp

/-- The morphism `S(K) ⟶ S'(K)` of short complexes of cochain complexes induced by a morphism
of short complexes of functors `S ⟶ S'`. -/
@[simps]
noncomputable def mapCochainComplexMapOfHom {S S' : ShortComplex (C ⥤ D)} [S.X₁.Additive]
    [S.X₂.Additive] [S.X₃.Additive] [S'.X₁.Additive] [S'.X₂.Additive] [S'.X₃.Additive]
    (τ : S ⟶ S') (K : CochainComplex C ℤ) :
    S.mapCochainComplex K ⟶ S'.mapCochainComplex K where
  τ₁ := (NatTrans.mapHomologicalComplex τ.τ₁ _).app K
  τ₂ := (NatTrans.mapHomologicalComplex τ.τ₂ _).app K
  τ₃ := (NatTrans.mapHomologicalComplex τ.τ₃ _).app K
  comm₁₂ := by ext n; simpa using congr_app τ.comm₁₂ (K.X n)
  comm₂₃ := by ext n; simpa using congr_app τ.comm₂₃ (K.X n)

/-- A short complex of functors `S` is *short exact on injectives* if
`0 ⟶ S.X₁(I) ⟶ S.X₂(I) ⟶ S.X₃(I) ⟶ 0` is short exact for every injective object `I`. -/
def ShortExactOnInjectives : Prop :=
  ∀ (I : C) [Injective I], (ShortComplex.mk (S.f.app I) (S.g.app I)
    (by rw [← NatTrans.comp_app, S.zero, NatTrans.app_zero])).ShortExact

variable {S}

lemma ShortExactOnInjectives.shortExact_mapCochainComplex (hS : S.ShortExactOnInjectives)
    (K : CochainComplex C ℤ) [∀ n, Injective (K.X n)] : (S.mapCochainComplex K).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ hS (K.X n)

variable [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
  (hS : S.ShortExactOnInjectives)

/-- The connecting map `RF₃(I) ⟶ RF₁(I)[1]` on a K-injective complex of injectives `I`: the
connecting map of the short exact sequence of complexes `0 ⟶ F₁(I) ⟶ F₂(I) ⟶ F₃(I) ⟶ 0`. -/
noncomputable def rightDerivedδQObj (I : CochainComplex C ℤ) [∀ n, Injective (I.X n)]
    [I.IsKInjective] :
    S.X₃.rightDerivedFunctor.obj (Q.obj I) ⟶ (S.X₁.rightDerivedFunctor.obj (Q.obj I))⟦(1 : ℤ)⟧ :=
  (S.X₃.rightDerivedFunctorObjQIso I).hom ≫ triangleOfSESδ (hS.shortExact_mapCochainComplex I) ≫
    (S.X₁.rightDerivedFunctorObjQIso I).inv⟦(1 : ℤ)⟧'

lemma rightDerivedδQObj_naturality {I J : CochainComplex C ℤ} [∀ n, Injective (I.X n)]
    [I.IsKInjective] [∀ n, Injective (J.X n)] [J.IsKInjective] (φ : I ⟶ J) :
    S.X₃.rightDerivedFunctor.map (Q.map φ) ≫ rightDerivedδQObj hS J =
      rightDerivedδQObj hS I ≫ (S.X₁.rightDerivedFunctor.map (Q.map φ))⟦(1 : ℤ)⟧' := by
  have h := triangleOfSESδ_naturality (hS.shortExact_mapCochainComplex I)
    (hS.shortExact_mapCochainComplex J) (S.mapCochainComplexMap φ)
  simp only [mapCochainComplexMap_τ₁, mapCochainComplexMap_τ₃] at h
  simp only [rightDerivedδQObj, assoc,
    Functor.rightDerivedFunctor_map_Q_map_comp_objQIso_hom_assoc, ← reassoc_of% h,
    ← Functor.map_comp, Functor.rightDerivedFunctor_map_Q_map_comp_objQIso_inv]

@[reassoc]
lemma rightDerivedδQObj_natTrans {S' : ShortComplex (C ⥤ D)} [S'.X₁.Additive] [S'.X₂.Additive]
    [S'.X₃.Additive] (hS' : S'.ShortExactOnInjectives) (τ : S ⟶ S') (I : CochainComplex C ℤ)
    [∀ n, Injective (I.X n)] [I.IsKInjective] :
    (Functor.rightDerivedFunctorNatTrans τ.τ₃).app (Q.obj I) ≫ rightDerivedδQObj hS' I =
      rightDerivedδQObj hS I ≫
        ((Functor.rightDerivedFunctorNatTrans τ.τ₁).app (Q.obj I))⟦(1 : ℤ)⟧' := by
  have h := triangleOfSESδ_naturality (hS.shortExact_mapCochainComplex I)
    (hS'.shortExact_mapCochainComplex I) (mapCochainComplexMapOfHom τ I)
  have h₁ := Functor.rightDerivedFunctorNatTrans_app_Q_obj τ.τ₁ I
  rw [← Iso.eq_comp_inv, assoc] at h₁
  simp only [mapCochainComplexMapOfHom_τ₁, mapCochainComplexMapOfHom_τ₃] at h
  simp only [rightDerivedδQObj, assoc, reassoc_of% (Functor.rightDerivedFunctorNatTrans_app_Q_obj
    τ.τ₃ I), ← reassoc_of% h, h₁, ← Functor.map_comp, Iso.inv_hom_id_assoc]

/-- The connecting map `RF₃(M) ⟶ RF₁(M)[1]` computed with a model `R` of `M`. -/
noncomputable def rightDerivedδAux (M : DerivedCategory C) (R : M.InjectiveModel) :
    S.X₃.rightDerivedFunctor.obj M ⟶ (S.X₁.rightDerivedFunctor.obj M)⟦(1 : ℤ)⟧ :=
  S.X₃.rightDerivedFunctor.map R.iso.inv ≫ rightDerivedδQObj hS R.I ≫
    (S.X₁.rightDerivedFunctor.map R.iso.hom)⟦(1 : ℤ)⟧'

lemma rightDerivedδAux_naturality {M N : DerivedCategory C} (R : M.InjectiveModel)
    (R' : N.InjectiveModel) (f : M ⟶ N) :
    S.X₃.rightDerivedFunctor.map f ≫ rightDerivedδAux hS N R' =
      rightDerivedδAux hS M R ≫ (S.X₁.rightDerivedFunctor.map f)⟦(1 : ℤ)⟧' := by
  obtain ⟨φ, hφ⟩ := CochainComplex.IsKInjective.exists_Q_map_eq R.I R'.I
    (R.iso.hom ≫ f ≫ R'.iso.inv)
  have hf : f = R.iso.inv ≫ Q.map φ ≫ R'.iso.hom := by
    rw [hφ]; simp only [assoc, Iso.inv_hom_id, comp_id, Iso.inv_hom_id_assoc]
  have h := rightDerivedδQObj_naturality hS φ
  have k {Y : DerivedCategory D}
      (g : (S.X₁.rightDerivedFunctor.obj (Q.obj R.I))⟦(1 : ℤ)⟧ ⟶ Y) :
      (S.X₁.rightDerivedFunctor.map R.iso.hom)⟦(1 : ℤ)⟧' ≫
        (S.X₁.rightDerivedFunctor.map R.iso.inv)⟦(1 : ℤ)⟧' ≫ g = g := by
    rw [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id,
      Functor.map_id, id_comp]
  rw [hf]
  simp only [rightDerivedδAux, Functor.map_comp, assoc, Iso.hom_inv_id_map_assoc,
    reassoc_of% h, k]

variable [EnoughInjectives C]

/-- The connecting map `δ : RF₃ ⟶ RF₁[1]` of the right derived functors of a short complex of
functors which is short exact on injectives, as a natural transformation on the bounded below
derived category. -/
noncomputable def rightDerivedδ :
    Plus.ι ⋙ S.X₃.rightDerivedFunctor ⟶
      Plus.ι ⋙ S.X₁.rightDerivedFunctor ⋙ shiftFunctor _ (1 : ℤ) where
  app M := rightDerivedδAux hS M.obj (Plus.injectiveModel M)
  naturality _ _ f := rightDerivedδAux_naturality hS _ _ (Plus.ι.map f)

/-- The connecting map `δ` may be computed with any model by a K-injective complex of
injectives. -/
lemma rightDerivedδ_app_eq (M : Plus C) (R : M.obj.InjectiveModel) :
    (rightDerivedδ hS).app M = rightDerivedδAux hS M.obj R := by
  have h := rightDerivedδAux_naturality hS (Plus.injectiveModel M) R (𝟙 _)
  simp only [Functor.map_id, id_comp, comp_id] at h
  exact h.symm

/-- The triangle of right derived functors `RF₁(K) ⟶ RF₂(K) ⟶ RF₃(K) ⟶ RF₁(K)[1]`, as a functor
of `K` in the bounded below derived category. -/
noncomputable def rightDerivedTriangle : Plus C ⥤ Triangle (DerivedCategory D) :=
  Triangle.functorMk (Functor.whiskerLeft Plus.ι (Functor.rightDerivedFunctorNatTrans S.f))
    (Functor.whiskerLeft Plus.ι (Functor.rightDerivedFunctorNatTrans S.g)) (rightDerivedδ hS)

@[simp]
lemma rightDerivedTriangle_obj (M : Plus C) :
    (rightDerivedTriangle hS).obj M =
      Triangle.mk ((Functor.rightDerivedFunctorNatTrans S.f).app M.obj)
        ((Functor.rightDerivedFunctorNatTrans S.g).app M.obj) ((rightDerivedδ hS).app M) :=
  rfl

omit [EnoughInjectives C] in
/-- On a K-injective complex of injectives `I`, the triangle of right derived functors is
isomorphic to the triangle of the short exact sequence `0 ⟶ F₁(I) ⟶ F₂(I) ⟶ F₃(I) ⟶ 0`. -/
lemma triangle_rightDerivedδQObj_distinguished (I : CochainComplex C ℤ)
    [∀ n, Injective (I.X n)] [I.IsKInjective] :
    Triangle.mk ((Functor.rightDerivedFunctorNatTrans S.f).app (Q.obj I))
      ((Functor.rightDerivedFunctorNatTrans S.g).app (Q.obj I)) (rightDerivedδQObj hS I) ∈
        distTriang _ := by
  refine isomorphic_distinguished _
    (triangleOfSES_distinguished (hS.shortExact_mapCochainComplex I)) _
    (Triangle.isoMk _ _ (S.X₁.rightDerivedFunctorObjQIso I) (S.X₂.rightDerivedFunctorObjQIso I)
      (S.X₃.rightDerivedFunctorObjQIso I) ?_ ?_ ?_)
  · exact Functor.rightDerivedFunctorNatTrans_app_Q_obj _ I
  · exact Functor.rightDerivedFunctorNatTrans_app_Q_obj _ I
  · simp only [Triangle.mk_mor₃, rightDerivedδQObj, triangleOfSES_mor₃, assoc,
      ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, comp_id]

/-- **The distinguished triangle of right derived functors.** For a short complex of functors
`F₁ ⟶ F₂ ⟶ F₃` which is short exact on injectives and a bounded below complex `K`, the triangle
`RF₁(K) ⟶ RF₂(K) ⟶ RF₃(K) ⟶ RF₁(K)[1]` is distinguished. -/
lemma rightDerivedTriangle_obj_distinguished (M : Plus C) :
    (rightDerivedTriangle hS).obj M ∈ distTriang _ := by
  set R := Plus.injectiveModel M
  refine isomorphic_distinguished _ (triangle_rightDerivedδQObj_distinguished hS R.I) _
    (Triangle.isoMk _ _ (S.X₁.rightDerivedFunctor.mapIso R.iso.symm)
      (S.X₂.rightDerivedFunctor.mapIso R.iso.symm)
      (S.X₃.rightDerivedFunctor.mapIso R.iso.symm) ?_ ?_ ?_)
  · exact ((Functor.rightDerivedFunctorNatTrans _).naturality R.iso.inv).symm
  · exact ((Functor.rightDerivedFunctorNatTrans _).naturality R.iso.inv).symm
  · simp only [rightDerivedTriangle_obj, Triangle.mk_mor₃, Functor.mapIso_hom, Iso.symm_hom]
    rw [rightDerivedδ_app_eq hS M R]
    simp only [rightDerivedδAux, assoc, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id,
      comp_id]

/-- **The long exact sequence of right derived functors.** For a short complex of functors
`F₁ ⟶ F₂ ⟶ F₃` which is short exact on injectives and a bounded below complex `K`, the sequence

`⋯ ⟶ H^q(RF₁ K) ⟶ H^q(RF₂ K) ⟶ H^q(RF₃ K) ⟶ H^{q+1}(RF₁ K) ⟶ ⋯`

is exact; all the maps are natural in `K` (`rightDerivedTriangle` is a functor). -/
lemma exact_homology_rightDerivedTriangle (M : Plus C) (q₀ q₁ : ℤ) (h : q₀ + 1 = q₁) :
    (ShortComplex.mk _ _ (DerivedCategory.HomologySequence.comp_δ _
        (rightDerivedTriangle_obj_distinguished hS M) q₀ q₁ h)).Exact ∧
      (ShortComplex.mk _ _ (DerivedCategory.HomologySequence.δ_comp _
        (rightDerivedTriangle_obj_distinguished hS M) q₀ q₁ h)).Exact ∧
      (ShortComplex.mk ((DerivedCategory.homologyFunctor D q₀).map
          ((rightDerivedTriangle hS).obj M).mor₁)
        ((DerivedCategory.homologyFunctor D q₀).map ((rightDerivedTriangle hS).obj M).mor₂)
        (by simp only [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _
          (rightDerivedTriangle_obj_distinguished hS M), Functor.map_zero])).Exact :=
  ⟨DerivedCategory.HomologySequence.exact₃ _ (rightDerivedTriangle_obj_distinguished hS M) q₀ q₁ h,
    DerivedCategory.HomologySequence.exact₁ _ (rightDerivedTriangle_obj_distinguished hS M) q₀ q₁ h,
    DerivedCategory.HomologySequence.exact₂ _ (rightDerivedTriangle_obj_distinguished hS M) q₀⟩

variable {S' : ShortComplex (C ⥤ D)} [S'.X₁.Additive] [S'.X₂.Additive] [S'.X₃.Additive]
  (hS' : S'.ShortExactOnInjectives)

lemma rightDerivedδ_natTrans (τ : S ⟶ S') :
    rightDerivedδ hS ≫ Functor.whiskerRight
        (Functor.whiskerLeft Plus.ι (Functor.rightDerivedFunctorNatTrans τ.τ₁))
        (shiftFunctor _ (1 : ℤ)) =
      Functor.whiskerLeft Plus.ι (Functor.rightDerivedFunctorNatTrans τ.τ₃) ≫
        rightDerivedδ hS' := by
  ext M
  set R := Plus.injectiveModel M
  have h₁ := (Functor.rightDerivedFunctorNatTrans τ.τ₁).naturality R.iso.hom
  have h₃ := (Functor.rightDerivedFunctorNatTrans τ.τ₃).naturality R.iso.inv
  dsimp at h₁ h₃ ⊢
  rw [rightDerivedδ_app_eq hS M R, rightDerivedδ_app_eq hS' M R]
  simp only [rightDerivedδAux, assoc]
  rw [← reassoc_of% h₃, rightDerivedδQObj_natTrans_assoc hS hS' τ R.I]
  simp only [← Functor.map_comp, h₁]

/-- The functoriality of the triangle of right derived functors in the short complex of
functors. -/
noncomputable def rightDerivedTriangleMap (τ : S ⟶ S') :
    rightDerivedTriangle hS ⟶ rightDerivedTriangle hS' :=
  Triangle.functorHomMk' (Functor.whiskerLeft Plus.ι (Functor.rightDerivedFunctorNatTrans τ.τ₁))
    (Functor.whiskerLeft Plus.ι (Functor.rightDerivedFunctorNatTrans τ.τ₂))
    (Functor.whiskerLeft Plus.ι (Functor.rightDerivedFunctorNatTrans τ.τ₃))
    (by rw [← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp,
      ← Functor.rightDerivedFunctorNatTrans_comp, ← Functor.rightDerivedFunctorNatTrans_comp,
      τ.comm₁₂])
    (by rw [← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp,
      ← Functor.rightDerivedFunctorNatTrans_comp, ← Functor.rightDerivedFunctorNatTrans_comp,
      τ.comm₂₃])
    (rightDerivedδ_natTrans hS hS' τ)

end ShortComplex

end CategoryTheory
