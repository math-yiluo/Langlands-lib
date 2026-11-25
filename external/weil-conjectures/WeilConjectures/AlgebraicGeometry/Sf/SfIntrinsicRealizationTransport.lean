/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-!
# Canonical realization and constant-coefficient direct image

The normalization on the scalar-unit sections fixes the comparison, including its direction.

## Main definitions

- `sfIntrinsicDerivedEquivalence`: the specified realization on derived categories.
- `sfIntrinsicDirectImageComparison` and `sfIntrinsicDerivedDirectImageComparison`:
  the comparisons uniquely normalized on sections and K-injective representatives.
- `sfIntrinsicConstantModuleAdjunction`: the transported inverse-image adjunction.
- `AlgebraicGeometry.ProEtale.sfFixedDerivedPullback`: exact termwise inverse image.

## References

* Stacks Tag 03D1
* Stacks Tag 07A5
* Stacks Tags 00YV and 03D3
* Stacks Tag 04JC
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
section
universe uA vA wA uT vT
set_option backward.isDefEq.respectTransparency false

-- Extend the prescribed comparison from K-injective representatives, as in
-- ExactPostcompositionKInjectiveDescent; all helpers here are private and proved.
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {T : Type uT} [Category.{vT} T]

private theorem representative (h : ∀ N : CochainComplex A ℤ,
    ∃ (I : CochainComplex A ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (X : DerivedCategory A) :
    ∃ I : CochainComplex A ℤ, I.IsKInjective ∧ Nonempty (X ≅ DerivedCategory.Q.obj I) := by
  obtain ⟨I, a, hI, ha⟩ := h (DerivedCategory.Q.objPreimage X)
  exact ⟨I, hI, ⟨(DerivedCategory.Q.objObjPreimageIso X).symm ≪≫
    asIso (DerivedCategory.Q.map a)⟩⟩

private theorem representative_ext
    (h : ∀ N : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
    {F G : DerivedCategory A ⥤ T} (α β : F ⟶ G)
    (he : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      α.app (DerivedCategory.Q.obj I) = β.app (DerivedCategory.Q.obj I)) : α = β := by
  ext X
  obtain ⟨I, hI, ⟨e⟩⟩ := representative h X
  apply (cancel_mono (G.map e.hom)).mp
  rw [← α.naturality, ← β.naturality, he I]

private theorem representative_map_surjective (I J : CochainComplex A ℤ)
    [J.IsKInjective] (f : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj J) :
    ∃ g : I ⟶ J, DerivedCategory.Q.map g = f := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A (.up ℤ)).obj I) J).surjective
      ((DerivedCategory.quotientCompQhIso A).hom.app I ≫ f ≫
        (DerivedCategory.quotientCompQhIso A).inv.app J)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective g
  refine ⟨g, ?_⟩
  have hn := (DerivedCategory.quotientCompQhIso A).hom.naturality g
  dsimp at hn
  rw [hg] at hn
  simpa using congrArg
    (fun t ↦ (DerivedCategory.quotientCompQhIso A).inv.app I ≫ t) hn.symm

private theorem extend_representatives
    (h : ∀ N : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
    {F G : DerivedCategory A ⥤ T}
    (t : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      F.obj (DerivedCategory.Q.obj I) ≅ G.obj (DerivedCategory.Q.obj I))
    (ht : ∀ (I J : CochainComplex A ℤ) [I.IsKInjective] [J.IsKInjective] (g : I ⟶ J),
      F.map (DerivedCategory.Q.map g) ≫ (t J).hom =
        (t I).hom ≫ G.map (DerivedCategory.Q.map g)) :
    ∃ r : F ≅ G, ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      r.hom.app (DerivedCategory.Q.obj I) = (t I).hom := by
  classical
  choose I hI e using representative h
  let e' (X : DerivedCategory A) := (e X).some
  have hn (I J : CochainComplex A ℤ) [I.IsKInjective] [J.IsKInjective]
      (f : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj J) :
      F.map f ≫ (t J).hom = (t I).hom ≫ G.map f := by
    obtain ⟨g, rfl⟩ := representative_map_surjective I J f
    exact ht I J g
  let r : F ≅ G := NatIso.ofComponents
    (fun X ↦ F.mapIso (e' X) ≪≫ t (I X) ≪≫ (G.mapIso (e' X)).symm)
    (by
      intro X Y f
      have hh := hn (I X) (I Y) ((e' X).inv ≫ f ≫ (e' Y).hom)
      dsimp
      simp only [Functor.map_comp, Category.assoc] at hh ⊢
      have hh' := congrArg (fun z ↦ F.map (e' X).hom ≫ z ≫ G.map (e' Y).inv) hh
      simpa [← Functor.map_comp, Category.assoc] using hh')
  refine ⟨r, ?_⟩
  intro J hJ
  have hh := hn J (I (DerivedCategory.Q.obj J)) (e' (DerivedCategory.Q.obj J)).hom
  dsimp [r]
  rw [← Category.assoc, hh]
  simp [← G.map_comp]

private theorem extend_units
    (h : ∀ N : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a)
    {F G : DerivedCategory A ⥤ T} {S : CochainComplex A ℤ ⥤ T}
    (u : S ⟶ DerivedCategory.Q ⋙ F) (v : S ⟶ DerivedCategory.Q ⋙ G)
    (hu : ∀ (I : CochainComplex A ℤ) [I.IsKInjective], IsIso (u.app I))
    (hv : ∀ (I : CochainComplex A ℤ) [I.IsKInjective], IsIso (v.app I)) :
    ∃ r : F ≅ G, ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      u.app I ≫ r.hom.app (DerivedCategory.Q.obj I) = v.app I := by
  let t (I : CochainComplex A ℤ) [I.IsKInjective] :
      F.obj (DerivedCategory.Q.obj I) ≅ G.obj (DerivedCategory.Q.obj I) :=
    letI := hu I
    letI := hv I
    (asIso (u.app I)).symm ≪≫ asIso (v.app I)
  have ht (I : CochainComplex A ℤ) [I.IsKInjective] :
      u.app I ≫ (t I).hom = v.app I := by
    let := hu I
    simp [t]
  obtain ⟨r, hr⟩ := extend_representatives h t (by
    intro I J hI hJ a
    let := hu I
    apply (cancel_epi (u.app I)).mp
    have hn := u.naturality a
    have hn' := v.naturality a
    dsimp only [Functor.comp_map] at hn hn'
    rw [← Category.assoc, ← hn, Category.assoc, ht J,
      ← Category.assoc, ht I, hn'])
  refine ⟨r, ?_⟩
  intro I hI
  rw [hr I]
  exact ht I

end

private noncomputable def intrinsicDerivedUnitNat
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app := F.rightDerivedFunctorUnitQ
  naturality _ _ g := F.rightDerivedFunctorUnitQ_naturality g

section
universe uC uD uC' uD' vC vD vC' vD' wC wD wC' wD'
set_option backward.isDefEq.respectTransparency false

private theorem intrinsicDerivedSquare
    {C : Type uC} {D : Type uD} {C' : Type uC'} {D' : Type uD'}
    [Category.{vC} C] [Category.{vD} D] [Category.{vC'} C'] [Category.{vD'} D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [HasDerivedCategory.{wC'} C'] [HasDerivedCategory.{wD'} D']
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
    (L : C ⥤ C') [L.Additive] [L.IsEquivalence]
    (R : D ⥤ D') [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (H : C ⥤ D) [H.Additive] (G : C' ⥤ D') [G.Additive]
    (α : L ⋙ G ≅ H ⋙ R) :
    ∃! e : L.mapDerivedCategory ⋙ G.rightDerivedFunctor ≅
      H.rightDerivedFunctor ⋙ R.mapDerivedCategory,
      ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
        e.hom.app (DerivedCategory.Q.obj I) ≫
            R.mapDerivedCategory.map (H.rightDerivedFunctorObjQIso I).hom ≫
            R.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj I) =
          G.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.hom.app I) ≫
            (G.rightDerivedFunctorObjQIso ((L.mapHomologicalComplex (.up ℤ)).obj I)).hom ≫
            DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app I) := by
  let u : (L ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (L.mapDerivedCategory ⋙ G.rightDerivedFunctor) :=
    Functor.whiskerLeft (L.mapHomologicalComplex (.up ℤ)) (intrinsicDerivedUnitNat G) ≫
      Functor.whiskerRight L.mapDerivedCategoryFactors.inv G.rightDerivedFunctor
  let v : (L ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (H.rightDerivedFunctor ⋙ R.mapDerivedCategory) :=
    Functor.whiskerRight (NatTrans.mapHomologicalComplex α.hom (.up ℤ)) DerivedCategory.Q ≫
      Functor.whiskerLeft (H.mapHomologicalComplex (.up ℤ)) R.mapDerivedCategoryFactors.inv ≫
      Functor.whiskerRight (intrinsicDerivedUnitNat H) R.mapDerivedCategory
  have hu (I : CochainComplex
      C ℤ)
      [I.IsKInjective] : IsIso (u.app I) := by
    dsimp only [u, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      intrinsicDerivedUnitNat]
    rw [G.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have hv (I : CochainComplex
      C ℤ)
      [I.IsKInjective] : IsIso (v.app I) := by
    dsimp only [v, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      intrinsicDerivedUnitNat]
    rw [H.rightDerivedFunctorUnitQ_eq]
    have : IsIso ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app I) :=
      ((NatIso.mapHomologicalComplex α (.up ℤ)).app I).isIso_hom
    infer_instance
  obtain ⟨e, he⟩ := extend_units
    (fun N ↦ by
      obtain ⟨I, _, a, _, _⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective N
      exact ⟨I, a, inferInstance, inferInstance⟩) u v hu hv
  have hnorm : ∀ (I : CochainComplex
      C ℤ)
      [I.IsKInjective],
      e.hom.app (DerivedCategory.Q.obj I) ≫
          R.mapDerivedCategory.map (H.rightDerivedFunctorObjQIso I).hom ≫
          R.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj I) =
        G.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.hom.app I) ≫
          (G.rightDerivedFunctorObjQIso ((L.mapHomologicalComplex (.up ℤ)).obj I)).hom ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app I) := by
    intro I hI
    have h := he I
    dsimp only [u, v, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      intrinsicDerivedUnitNat] at h
    rw [G.rightDerivedFunctorUnitQ_eq, H.rightDerivedFunctorUnitQ_eq] at h
    apply (cancel_epi
      ((G.rightDerivedFunctorObjQIso ((L.mapHomologicalComplex (.up ℤ)).obj I)).inv ≫
        G.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.inv.app I))).mp
    simp only [Category.assoc]
    rw [← Category.assoc, ← Category.assoc, h]
    simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_map_assoc,
      Iso.inv_hom_id_app, cancelIso, Iso.inv_hom_id_assoc]
    exact Category.comp_id _
  refine ⟨e, hnorm, ?_⟩
  intro e' he'
  apply Iso.ext
  apply representative_ext
    (fun N ↦ by
      obtain ⟨I, _, a, _, _⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective N
      exact ⟨I, a, inferInstance, inferInstance⟩)
  intro I hI
  apply (cancel_mono (R.mapDerivedCategory.map (H.rightDerivedFunctorObjQIso I).hom ≫
    R.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj I))).mp
  exact (he' I).trans (hnorm I).symm

end

namespace AlgebraicGeometry.Scheme

/-- The derived equivalence induced by the recorded canonical coefficient realization. -/
noncomputable def sfIntrinsicDerivedEquivalence (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ≌
      proEtaleDerivedCategory T A :=
  (sfIntrinsicModuleEquivalence T A).mapDerivedCategory

/-- The scalar-unit section of the canonical associated module sheaf. -/
noncomputable def sfIntrinsicRealizationUnit (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A]
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (W : T.ProEtᵒᵖ) (m : M.obj.obj W) :
    ((sfIntrinsicModuleEquivalence T A).functor.obj M).val.obj W :=
  ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap T A)).unit.app
      ((ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} A)).obj M.obj)).app
        W m

private noncomputable def intrinsicEmbedding (T : Scheme.{u})
    (A : Type u) [CommRing A] :=
  sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⋙
    ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} A)

private noncomputable def intrinsicRestriction (T : Scheme.{u})
    (A : Type u) [CommRing A] :=
  SheafOfModules.forget.{u + 1} _ ⋙
    PresheafOfModules.restrictScalars.{u + 1}
      (ProEtale.finiteCoefficientIntrinsicScalarMap T A)

private noncomputable def intrinsicUnitIso (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    intrinsicEmbedding T A ≅ (sfIntrinsicModuleEquivalence T A).functor ⋙
      intrinsicRestriction T A := by
  let η := Functor.whiskerLeft (intrinsicEmbedding T A)
    (PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
      (ProEtale.finiteCoefficientIntrinsicScalarMap T A)).unit
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    change IsIso ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
      (ProEtale.finiteCoefficientIntrinsicScalarMap T A)).unit.app
        ((intrinsicEmbedding T A).obj M))
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1})).obj M).property
  exact asIso η

private theorem intrinsicScalarSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :
    ProEtale.finiteCoefficientIntrinsicScalarMap Y A ≫
        Functor.whiskerRight (proEtaleCoefficientDirectImageMap f A).hom
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) =
      Functor.whiskerLeft (proEtaleBaseChange f).op
        (ProEtale.finiteCoefficientIntrinsicScalarMap X A) := by
  have h := ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))
    ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
      (proEtaleConstantRing X A))).apply_symm_apply
    (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))))
  change toSheafify _ _ ≫ (proEtaleCoefficientDirectImageMap f A).hom = _ at h
  exact congrArg (fun z ↦ Functor.whiskerRight z
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) h

private noncomputable def intrinsicRestrictionDirectImageIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] :
    proEtaleConstantModuleDirectImage f A ⋙ intrinsicRestriction Y A ≅
      intrinsicRestriction X A ⋙
        PresheafOfModules.pushforward₀ (proEtaleBaseChange f)
          ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A))) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let L := (proEtaleConstantModuleDirectImage f A ⋙ intrinsicRestriction Y A).obj M
    let R := (intrinsicRestriction X A ⋙
      PresheafOfModules.pushforward₀ (proEtaleBaseChange f)
        ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A)))).obj M
    change L ≅ R
    refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
    · let g : L.obj U ≃ₗ[ULift.{u + 1, u} A] R.obj U :=
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro r m
            have h := congrArg (fun t ↦ (t.app U).hom r) (intrinsicScalarSquare f A)
            exact congrArg (fun a ↦ a •
              (show M.val.obj ((proEtaleBaseChange f).op.obj U) from m)) h }
      exact g.toModuleIso
    · intro U V g
      ext x
      rfl
  · intro M N g
    ext U x
    rfl

/-- The unique section-normalized comparison of direct images in the two coefficient
presentations. -/
theorem sfIntrinsicDirectImageComparison_existsUnique
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [Finite A] :
    ∃! e : (sfIntrinsicModuleEquivalence X A).functor ⋙
          proEtaleConstantModuleDirectImage f A ≅
        ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
          (sfIntrinsicModuleEquivalence Y A).functor,
      ∀ (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
        (W : Y.ProEtᵒᵖ) (m : M.obj.obj ((proEtaleBaseChange f).op.obj W)),
        (e.hom.app M).val.app W
            (sfIntrinsicRealizationUnit X A M ((proEtaleBaseChange f).op.obj W) m) =
          sfIntrinsicRealizationUnit Y A
            ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj M) W m := by
  let P := PresheafOfModules.pushforward₀ (proEtaleBaseChange f)
    ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A)))
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap Y A)
  have : (intrinsicRestriction Y A).Full := adj.fullyFaithfulROfIsIsoCounit.full
  have : (intrinsicRestriction Y A).Faithful := adj.fullyFaithfulROfIsIsoCounit.faithful
  let e : ((sfIntrinsicModuleEquivalence X A).functor ⋙
        proEtaleConstantModuleDirectImage f A) ⋙ intrinsicRestriction Y A ≅
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
        (sfIntrinsicModuleEquivalence Y A).functor) ⋙ intrinsicRestriction Y A :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (intrinsicRestrictionDirectImageIso f A) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (intrinsicUnitIso X A).symm P ≪≫
      (Iso.refl _ : intrinsicEmbedding X A ⋙ P ≅
        ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
          intrinsicEmbedding Y A) ≪≫
      Functor.isoWhiskerLeft
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
        (intrinsicUnitIso Y A) ≪≫
      (Functor.associator _ _ _).symm
  let c := Functor.fullyFaithfulCancelRight (intrinsicRestriction Y A) e
  have hc : ∀ M W m, (c.hom.app M).val.app W
      (sfIntrinsicRealizationUnit X A M ((proEtaleBaseChange f).op.obj W) m) =
      sfIntrinsicRealizationUnit Y A
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj M) W m := by
    intro M W m
    have h := (intrinsicRestriction Y A).map_preimage (e.hom.app M)
    have h' := congrArg (fun k ↦ k.app W
      (sfIntrinsicRealizationUnit X A M ((proEtaleBaseChange f).op.obj W) m)) h
    change (c.hom.app M).val.app W _ = _ at h'
    rw [h']
    change ((intrinsicUnitIso Y A).hom.app
      ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj M)).app W
      (((intrinsicUnitIso X A).inv.app M).app ((proEtaleBaseChange f).op.obj W)
        (((intrinsicUnitIso X A).hom.app M).app ((proEtaleBaseChange f).op.obj W) m)) = _
    have hunit := ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.app ((proEtaleBaseChange f).op.obj W))
        ((intrinsicUnitIso X A).hom_inv_id_app M)) m
    exact congrArg
      (fun x ↦ ((intrinsicUnitIso Y A).hom.app
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj M)).app W x)
      hunit
  refine ⟨c, hc, ?_⟩
  intro d hd
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  let U := (proEtaleBaseChange f).op.obj W
  let η := ((intrinsicUnitIso X A).hom.app M).app U
  let η' := ((intrinsicUnitIso X A).inv.app M).app U
  have hη : η (η' x) = x := by
    change (((intrinsicUnitIso X A).inv.app M ≫
      (intrinsicUnitIso X A).hom.app M).app U) x = x
    rw [Iso.inv_hom_id_app]
    rfl
  have h := (hd M W (η' x)).trans (hc M W (η' x)).symm
  change (d.hom.app M).val.app W (η (η' x)) =
    (c.hom.app M).val.app W (η (η' x)) at h
  rw [hη] at h
  exact h

/-- The actual comparison, selected by its unique scalar-section normalization. -/
noncomputable def sfIntrinsicDirectImageComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [Finite A] :=
  (sfIntrinsicDirectImageComparison_existsUnique f A).exists.choose

/-- The uniquely normalized derived direct-image comparison. -/
theorem sfIntrinsicDerivedDirectImageComparison_existsUnique
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [Finite A] :
    ∃! e : (sfIntrinsicDerivedEquivalence X A).functor ⋙
          proEtaleConstantDerivedDirectImage f A ≅
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor ⋙
          (sfIntrinsicDerivedEquivalence Y A).functor,
      ∀ (J : CochainComplex
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ)
        [J.IsKInjective],
        e.hom.app (DerivedCategory.Q.obj J) ≫
            (sfIntrinsicDerivedEquivalence Y A).functor.map
              ((ProEtale.lowerStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctorObjQIso J).hom ≫
            (sfIntrinsicModuleEquivalence Y A).functor.mapDerivedCategoryFactors.hom.app
              (((ProEtale.lowerStar
                (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).mapHomologicalComplex (.up ℤ)).obj J) =
          (proEtaleConstantDerivedDirectImage f A).map
              ((sfIntrinsicModuleEquivalence X A).functor.mapDerivedCategoryFactors.hom.app J) ≫
            ((proEtaleConstantModuleDirectImage f A).rightDerivedFunctorObjQIso
              (((sfIntrinsicModuleEquivalence X A).functor.mapHomologicalComplex
                (.up ℤ)).obj J)).hom ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex
                (sfIntrinsicDirectImageComparison f A).hom (.up ℤ)).app J) := by
  exact intrinsicDerivedSquare (sfIntrinsicModuleEquivalence X A).functor
    (sfIntrinsicModuleEquivalence Y A).functor
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
    (proEtaleConstantModuleDirectImage f A) (sfIntrinsicDirectImageComparison f A)

/-- The actual derived comparison determined on K-injective representatives. -/
noncomputable def sfIntrinsicDerivedDirectImageComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [Finite A] :=
  (sfIntrinsicDerivedDirectImageComparison_existsUnique f A).exists.choose

/-- The actual inverse-image/direct-image adjunction, conjugated through the canonical
section-normalized comparison. This fixes the units and counits of inverse image. -/
noncomputable def sfIntrinsicConstantModuleAdjunction
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [Finite A] :
    sfIntrinsicPullback A f ⊣ proEtaleConstantModuleDirectImage f A :=
  (((sfIntrinsicModuleEquivalence Y A).symm.toAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)).comp
      (sfIntrinsicModuleEquivalence X A).toAdjunction).ofNatIsoRight
        (Functor.isoWhiskerLeft _ (sfIntrinsicDirectImageComparison f A).symm ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence X A).counitIso _ ≪≫
          Functor.leftUnitor _)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Exact termwise inverse image, in fixed-scalar coordinates. -/
noncomputable abbrev sfFixedDerivedPullback (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).mapDerivedCategory

end AlgebraicGeometry.ProEtale
