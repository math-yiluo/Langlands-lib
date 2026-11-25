/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.CategoryTheory.Monoidal.Multifunctor
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.KFlatBifunctorIsoDescent
import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided

/-! # Tensor comparison on K-flat representatives

Source: Stacks Project, Cohomology, Tag 079U and Section 20.27
(blueprint: lem-pc-derived-pullback-kflat-tensor-model).
-/

@[expose] public section

universe uModel wModel

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

noncomputable local instance kFlatTensorModelPullbackDescentModuleTensor (S : Scheme.{uModel}) :
    MonoidalCategory (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  SheafOfModules.monoidalCategory S.sheaf

noncomputable local instance kFlatTensorModelModuleSymmetric (S : Scheme.{uModel}) :
    SymmetricCategory (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  SheafOfModules.symmetricCategory S.sheaf

noncomputable local instance kFlatTensorModelModulePreadditive (S : Scheme.{uModel}) :
    MonoidalPreadditive (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed S.sheaf).1

noncomputable local instance kFlatTensorModelModuleClosed (S : Scheme.{uModel}) :
    MonoidalClosed (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed S.sheaf).2.1

attribute [local instance] kFlatBifunctorDescentModuleGrothendieck

local instance kFlatTensorModelModuleResolutions (S : Scheme.{uModel}) :
    Abelian.HasFunctorialFlatResolution
      (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution S

local instance kFlatTensorModelModuleDerivedMonoidal (S : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))] :
    Functor.HasDerivedMonoidalCategory
      (DerivedCategory.Qh (C := SheafOfModules.{uModel} (moduleRings S.toRingedSpace)))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) (ComplexShape.up ℤ)) :=
  DerivedCategory.hasDerivedMonoidalCategory _

local instance kFlatTensorModelHasTensor (S : Scheme.{uModel})
    (P N : GradedObject ℤ (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))) :
    GradedObject.HasTensor P N :=
  inferInstance

-- Share the concrete tensor structures instead of rebuilding them in each use of Q.
noncomputable local instance kFlatTensorModelComplexTensor (S : Scheme.{uModel}) :
    MonoidalCategory
      (CochainComplex (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) ℤ) :=
  inferInstance

noncomputable local instance kFlatTensorModelHomotopyTensor (S : Scheme.{uModel}) :
    MonoidalCategory
      (HomotopyCategory (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) (.up ℤ)) :=
  inferInstance

noncomputable local instance kFlatTensorModelDerivedTensor (S : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))] :
    MonoidalCategory (schemeDerivedCategory S) :=
  inferInstance

-- The quotient tensorator is the identity; record its data without unfolding
noncomputable local instance kFlatTensorModelQuotientLax (S : Scheme.{uModel}) :
    Functor.LaxMonoidal
      (HomotopyCategory.quotient
        (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) (.up ℤ)) :=
  { (inferInstance : Functor.LaxMonoidal
      (HomotopyCategory.quotient
        (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) (.up ℤ))) with
    ε := 𝟙 _
    μ := fun _ _ ↦ 𝟙 _ }

noncomputable local instance kFlatTensorModelQhLax (S : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))] :
    Functor.LaxMonoidal
      (DerivedCategory.Qh (C := SheafOfModules.{uModel} (moduleRings S.toRingedSpace))) :=
  inferInstance

noncomputable local instance kFlatTensorModelQuotientCompQhLax (S : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))] :
    Functor.LaxMonoidal
      (HomotopyCategory.quotient
        (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) (.up ℤ) ⋙
        DerivedCategory.Qh) :=
  Functor.LaxMonoidal.comp _ _

noncomputable local instance kFlatTensorModelPullbackDescentQLax (S : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))] :
    Functor.LaxMonoidal
      (DerivedCategory.Q (C := SheafOfModules.{uModel} (moduleRings S.toRingedSpace))) :=
  Functor.LaxMonoidal.ofIso
    (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)))

private theorem tensorSquare_natural {D : Type*} [Category* D] [MonoidalCategory D]
    {A A' B B' C C' E E' Z Z' : D}
    {a : A ⟶ A'} {b : B ⟶ B'} {c : C ⟶ C'} {d : E ⟶ E'}
    {εA : A ⟶ C} {εA' : A' ⟶ C'} {εB : B ⟶ E} {εB' : B' ⟶ E'}
    {m : C ⊗ E ⟶ Z} {m' : C' ⊗ E' ⟶ Z'} {t : Z ⟶ Z'}
    (ha : a ≫ εA' = εA ≫ c) (hb : b ≫ εB' = εB ≫ d)
    (hm : (c ⊗ₘ d) ≫ m' = m ≫ t) :
    (a ⊗ₘ b) ≫ (εA' ⊗ₘ εB') ≫ m' = (εA ⊗ₘ εB) ≫ m ≫ t := by
  rw [← Category.assoc, tensorHom_comp_tensorHom, ha, hb,
    ← tensorHom_comp_tensorHom, Category.assoc, hm]

private theorem comparisonSquare_natural {D : Type*} [Category* D]
    {S S' U U' V V' Z Z' : D}
    {v : S ⟶ S'} {u : U ⟶ U'} {z : Z ⟶ Z'}
    {A : U ⟶ V} {A' : U' ⟶ V'} {B : V ⟶ Z} {B' : V' ⟶ Z'}
    [IsIso A'] [IsIso B'] {C : S ⟶ Z} {C' : S' ⟶ Z'}
    {e : S ⟶ U} {e' : S' ⟶ U'}
    (he : e ≫ A ≫ B = C) (he' : e' ≫ A' ≫ B' = C')
    (hAB : u ≫ A' ≫ B' = A ≫ B ≫ z) (hC : v ≫ C' = C ≫ z) :
    v ≫ e' = e ≫ u := by
  apply (cancel_mono (A' ≫ B')).1
  simp only [Category.assoc]
  rw [he', hC, hAB, reassoc_of% he]

-- Paste the naturality squares before specializing to the concrete tensor structures.
private theorem mappedComparisonSquare_natural
    {D E H : Type*} [Category* D] [Category* E] [Category* H]
    (L : D ⥤ E) (Q : H ⥤ E)
    {U U' V V' : D} {W W' Z Z' : H}
    {u : U ⟶ U'} {v : V ⟶ V'} {w : W ⟶ W'} {z : Z ⟶ Z'}
    {a : U ⟶ V} {a' : U' ⟶ V'}
    {b : L.obj V ⟶ Q.obj W} {b' : L.obj V' ⟶ Q.obj W'}
    {c : W ⟶ Z} {c' : W' ⟶ Z'}
    (ha : u ≫ a' = a ≫ v) (hb : L.map v ≫ b' = b ≫ Q.map w)
    (hc : w ≫ c' = c ≫ z) :
    L.map u ≫ L.map a' ≫ (b' ≫ Q.map c') =
      L.map a ≫ (b ≫ Q.map c) ≫ Q.map z := by
  rw [← L.map_comp_assoc, ha, L.map_comp_assoc, reassoc_of% hb]
  simp only [Category.assoc]
  rw [← Q.map_comp, hc, Q.map_comp]

private theorem tensorModel_isIso (X : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    (P N : CochainComplex (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P N) := by
  let C := SheafOfModules.{uModel} (moduleRings X.toRingedSpace)
  have : Limits.HasColimitsOfSize.{0, 0} C :=
    Limits.hasColimitsOfSizeShrink.{0, 0, uModel, uModel} C
  have hk : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
      ((HomotopyCategory.quotient C (.up ℤ)).obj P) := by
    rw [HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro N hN
    obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
    have h := hP N hN
    have hright : HomotopyCategory.subcategoryAcyclic C
        ((HomotopyCategory.quotient C (.up ℤ)).obj N ⊗
          (HomotopyCategory.quotient C (.up ℤ)).obj P) := by
      exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 h
    exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso
      (β_ _ _) hright, hright⟩
  have hq := DerivedMonoidal.isIso_counit_app_app_of_kFlat_left
      (DerivedCategory.Qh (C := C)) (HomotopyCategory.quasiIso C (.up ℤ))
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)
      ((HomotopyCategory.quotient C (.up ℤ)).obj N) hk
  have : IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Qh (C := C))
        ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj N)) := hq
  change IsIso (_ ≫ _ ≫ _)
  change IsIso (_ ≫ (Functor.LaxMonoidal.μ (DerivedCategory.Qh (C := C))
    ((HomotopyCategory.quotient C (.up ℤ)).obj P)
    ((HomotopyCategory.quotient C (.up ℤ)).obj N) ≫
      DerivedCategory.Qh.map (𝟙 _)) ≫ _)
  infer_instance

private theorem tensorModel_natural (X : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    {P P' N N' : CochainComplex (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ}
    (a : P ⟶ P') (b : N ⟶ N') :
    (DerivedCategory.Q.map a ⊗ₘ DerivedCategory.Q.map b) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q P' N' =
      Functor.LaxMonoidal.μ DerivedCategory.Q P N ≫ DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap a b (curriedTensor _) (.up ℤ)) := by
  exact Functor.LaxMonoidal.μ_natural DerivedCategory.Q a b

private theorem counitModel_isIso {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (hmap : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    [F.Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh (C := SheafOfModules.{uModel} (moduleRings T.toRingedSpace)))
    (hε : (derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso _ (.up ℤ)))
    (P : CochainComplex (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P) :
    IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  have hF' : F = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF (fun M N a ↦ hmap a)
  subst F
  obtain ⟨_, _, _, _, _, _, _, F, hF, hmap, hAdd, δ, hδ, _, hK⟩ :=
    derivedPullback_spec.{uModel, wModel} g
  have hF' : F = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF (fun M N a ↦ hmap a)
  subst F
  change (derivedPullback g).IsLeftDerivedFunctor δ
    (HomotopyCategory.quasiIso _ (.up ℤ)) at hδ
  have := hε
  have := hδ
  have hfac := Functor.leftDerivedNatTrans_app
    (derivedPullback g) (derivedPullback g) δ ε
    (HomotopyCategory.quasiIso _ (.up ℤ)) (𝟙 _)
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  have := hK P hP
  have : IsIso (Functor.leftDerivedNatTrans
      (derivedPullback g) (derivedPullback g) δ ε
      (HomotopyCategory.quasiIso _ (.up ℤ)) (𝟙 _)) :=
    (Functor.leftDerivedUnique (derivedPullback g) (derivedPullback g) δ ε
      (HomotopyCategory.quasiIso _ (.up ℤ))).isIso_hom
  have : IsIso ((Functor.leftDerivedNatTrans
      (derivedPullback g) (derivedPullback g) δ ε
      (HomotopyCategory.quasiIso _ (.up ℤ)) (𝟙 _)).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
    rw [hfac]
    simpa using hK P hP
  exact IsIso.of_isIso_comp_left
    ((Functor.leftDerivedNatTrans
      (derivedPullback g) (derivedPullback g) δ ε
      (HomotopyCategory.quasiIso _ (.up ℤ)) (𝟙 _)).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) _

/-- The comparison on K-flat cochain representatives, before localization in either
variable. Source: Stacks Project, Cohomology, Tags 079U, 06YC and 06YH; steps 1 and 2
and the representative naturality calculation of the parent proof.
(blueprint: lem-pc-derived-pullback-kflat-tensor-model).

Proof: identify F with tensorPullback by functor extensionality. Uniqueness of the
left-derived functor compares epsilon with the recorded K-flat counit; hence epsilon
is invertible on K-flat complexes. Pullback preserves K-flatness (06YC). The derived
localization tensorator is invertible when its first argument is K-flat (06YH), both
on X and on T after F. For a K-flat pair let A=L(mu_Q), B=epsilon_tensor followed by
Q(phi), and C=(epsilon_P tensor epsilon_N) followed by mu_Q(FP,FN). A and C are
invertible by those computations and B by hiso. Set e=C followed by B inverse and
A inverse. Cancellation gives e;A;B=C. Naturality of the lax tensorator, epsilon
and phi gives u;A'B'=AB;z and v;C'=C;z for the induced source, target and model maps.
Postcompose v;e' and e;u with the invertible A'B' and use these two equalities;
cancellation proves simultaneous naturality. No localization of the K-flat full
subcategory, or extension to arbitrary derived objects, occurs in this lemma.
The construction includes the identity and empty scheme without a flatness hypothesis. -/
theorem derivedPullback_kFlat_tensor_model {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (hmap : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    [F.Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : (derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)))
    (φ : ∀ P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CochainComplex.mapBifunctor P N (curriedTensor _)) ≅
          CochainComplex.mapBifunctor
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (curriedTensor _))
    (hnatural : ∀ (P P' N N' : CochainComplex
              (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
            (a : P ⟶ P') (b : N ⟶ N'),
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (HomologicalComplex.mapBifunctorMap a b (curriedTensor _) (ComplexShape.up ℤ)) ≫
              (φ P' N').hom =
            (φ P N).hom ≫
              HomologicalComplex.mapBifunctorMap
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map a)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map b) (curriedTensor _)
                (ComplexShape.up ℤ))
    (hiso : ∀ P N : CochainComplex (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsKFlatTensor (R := X.sheaf) P →
      CochainComplex.IsKFlatTensor (R := X.sheaf) N →
            IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
              DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
                (φ P N).hom)))
    : ∃ e : ∀ (P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ),
        CochainComplex.IsKFlatTensor (R := X.sheaf) P →
        CochainComplex.IsKFlatTensor (R := X.sheaf) N →
          (((derivedPullback g).obj (DerivedCategory.Q.obj P) ⊗
            (derivedPullback g).obj (DerivedCategory.Q.obj N)) ≅
          (derivedPullback g).obj (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N)),
      (∀ (P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
        (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
        (hN : CochainComplex.IsKFlatTensor (R := X.sheaf) N),
        (e P N hP hN).hom ≫
            (derivedPullback g).map (Functor.LaxMonoidal.μ DerivedCategory.Q P N) ≫
            cast (by rfl) (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
              (CochainComplex.mapBifunctor P N (curriedTensor _)))) ≫
            DerivedCategory.Q.map (φ P N).hom =
          cast (by rfl) (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
            ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
            Functor.LaxMonoidal.μ DerivedCategory.Q
              ((F.mapHomologicalComplex (.up ℤ)).obj P)
              ((F.mapHomologicalComplex (.up ℤ)).obj N)) ∧
      (∀ (P P' N N' : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
        (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
        (hP' : CochainComplex.IsKFlatTensor (R := X.sheaf) P')
        (hN : CochainComplex.IsKFlatTensor (R := X.sheaf) N)
        (hN' : CochainComplex.IsKFlatTensor (R := X.sheaf) N') (a : P ⟶ P') (b : N ⟶ N'),
        ((curriedTensorPre (derivedPullback g)).map (DerivedCategory.Q.map a)).app
            (DerivedCategory.Q.obj N) ≫
            ((curriedTensorPre (derivedPullback g)).obj (DerivedCategory.Q.obj P')).map
              (DerivedCategory.Q.map b) ≫ (e P' N' hP' hN').hom =
          (e P N hP hN).hom ≫
            ((curriedTensorPost (derivedPullback g)).map (DerivedCategory.Q.map a)).app
              (DerivedCategory.Q.obj N) ≫
            ((curriedTensorPost (derivedPullback g)).obj (DerivedCategory.Q.obj P')).map
              (DerivedCategory.Q.map b)) := by
  classical
  have hF' : F = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF (fun M N a ↦ hmap a)
  let L := derivedPullback g
  let Q := DerivedCategory.Q
    (C := SheafOfModules.{uModel} (moduleRings X.toRingedSpace))
  let Qt := DerivedCategory.Q
    (C := SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
  let q := HomotopyCategory.quotient
    (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (.up ℤ)
  let Fc : CochainComplex
      (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ ⥤
      CochainComplex (SheafOfModules.{uModel} (moduleRings T.toRingedSpace)) ℤ :=
    F.mapHomologicalComplex (.up ℤ)
  let A P N := L.map (Functor.LaxMonoidal.μ Q P N)
  let B P N := ε.app (q.obj (P ⊗ N)) ≫ Qt.map (φ P N).hom
  let C P N := (ε.app (q.obj P) ⊗ₘ ε.app (q.obj N)) ≫
    Functor.LaxMonoidal.μ Qt (Fc.obj P) (Fc.obj N)
  have hA P N (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P) : IsIso (A P N) := by
    have := tensorModel_isIso X P N hP
    dsimp only [A]
    infer_instance
  have hB P N (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
      (hN : CochainComplex.IsKFlatTensor (R := X.sheaf) N) : IsIso (B P N) := hiso P N hP hN
  have hC P N (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
      (hN : CochainComplex.IsKFlatTensor (R := X.sheaf) N) : IsIso (C P N) := by
    have hFP : CochainComplex.IsKFlatTensor (R := T.sheaf) (Fc.obj P) := by
      clear hA hB A B C ε hε φ hnatural hiso hF hmap
      subst F
      convert CochainComplex.isKFlat_pullback g.base T.sheaf X.sheaf ⟨g.c⟩ P hP using 1
      rfl
    dsimp only [C]
    have : IsIso (ε.app (q.obj P)) := counitModel_isIso g F hF hmap ε hε P hP
    have : IsIso (ε.app (q.obj N)) := counitModel_isIso g F hF hmap ε hε N hN
    have : IsIso (Functor.LaxMonoidal.μ Qt (Fc.obj P) (Fc.obj N)) :=
      tensorModel_isIso T (Fc.obj P) (Fc.obj N) hFP
    infer_instance
  let e P N (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
      (hN : CochainComplex.IsKFlatTensor (R := X.sheaf) N) :=
    have := hA P N hP
    have := hB P N hP hN
    have := hC P N hP hN
    asIso (C P N) ≪≫ (asIso (B P N)).symm ≪≫ (asIso (A P N)).symm
  have he P N hP hN : (e P N hP hN).hom ≫ A P N ≫ B P N = C P N := by
    have := hA P N hP
    have := hB P N hP hN
    have := hC P N hP hN
    simp [e, Category.assoc]
  refine ⟨e, ?_, ?_⟩
  · intro P N hP hN
    exact he P N hP hN
  · intro P P' N N' hP hP' hN hN' a b
    have := hA P' N' hP'
    have := hB P' N' hP' hN'
    let t := a ⊗ₘ b
    let tf := Fc.map a ⊗ₘ Fc.map b
    have hεt : L.map (Q.map t) ≫ ε.app (q.obj (P' ⊗ N')) =
        ε.app (q.obj (P ⊗ N)) ≫ Qt.map (Fc.map t) := by
      exact ε.naturality (q.map t)
    have hεa : L.map (Q.map a) ≫ ε.app (q.obj P') =
        ε.app (q.obj P) ≫ Qt.map (Fc.map a) := by
      exact ε.naturality (q.map a)
    have hεb : L.map (Q.map b) ≫ ε.app (q.obj N') =
        ε.app (q.obj N) ≫ Qt.map (Fc.map b) := by
      exact ε.naturality (q.map b)
    have hAB : L.map (Q.map a ⊗ₘ Q.map b) ≫ A P' N' ≫ B P' N' =
        A P N ≫ B P N ≫ Qt.map tf := by
      exact mappedComparisonSquare_natural L Qt
        (tensorModel_natural X a b) hεt (hnatural P P' N N' a b)
    have hCnat : (L.map (Q.map a) ⊗ₘ L.map (Q.map b)) ≫ C P' N' =
        C P N ≫ Qt.map tf := by
      dsimp only [C]
      have hμ : (Qt.map (Fc.map a) ⊗ₘ Qt.map (Fc.map b)) ≫
          Functor.LaxMonoidal.μ Qt (Fc.obj P') (Fc.obj N') =
          Functor.LaxMonoidal.μ Qt (Fc.obj P) (Fc.obj N) ≫ Qt.map tf := by
        exact tensorModel_natural T (Fc.map a) (Fc.map b)
      simpa only [Category.assoc] using tensorSquare_natural hεa hεb hμ
    have hn := comparisonSquare_natural (he P N hP hN) (he P' N' hP' hN') hAB hCnat
    change (L.map (Q.map a) ▷ L.obj (Q.obj N)) ≫
        (L.obj (Q.obj P') ◁ L.map (Q.map b)) ≫ (e P' N' hP' hN').hom =
      (e P N hP hN).hom ≫ L.map (Q.map a ▷ Q.obj N) ≫
        L.map (Q.obj P' ◁ Q.map b)
    simpa only [tensorHom_def, Functor.map_comp, Category.assoc] using hn

end AlgebraicGeometry
