/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import Mathlib.CategoryTheory.Adjunction.Mates

import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcActualScalarPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
/-! # Ringed exchange for the canonical completed coefficient maps

The arbitrary invertible-coefficient interface is reexported; the following
specialization also retains the noninvertible completed coefficient structure maps.

## References

* Stacks Tag 03D8
* Stacks Tag 0D6D
* Stacks Tag 099N
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace AlgebraicGeometry.Scheme
variable {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

private theorem actualCoefficient_eq {S T : Scheme.{u}} (f : S ⟶ T) :
    completedCoefficientMap f d = (d.integralRingIso f).hom := by
  apply limit.hom_ext
  intro n
  change completedCoefficientMap f d ≫ d.projection S n.unop =
    (d.integralRingIso f).hom ≫ d.projection S n.unop
  rw [d.projection_comm]
  exact limit.lift_π _ n

/-- Fiber-product pasting determines the ordinary direct-image comparison on sections. -/
theorem pbcActualModuleDirectCompIso_exists :
    ∃! e : pbcActualModulePush h d ⋙ pbcActualModulePush k d ≅
        pbcActualModulePush (h ≫ k) d,
      ∀ (N : pbcModules Z (pbcAdicCompletion Z d)) (U : V.ProEt)
        (m : ((pbcActualModulePush h d ⋙
          pbcActualModulePush k d).obj N).val.obj (op U)),
        (e.hom.app N).val.app (op U) m =
          N.val.map ((MorphismProperty.Over.pullbackComp h k).hom.app U).op m := by
  unfold pbcActualModulePush completedModuleDirectImage completedCoefficientDirectImageMap
  rw [actualCoefficient_eq d h, actualCoefficient_eq d k, actualCoefficient_eq d (h ≫ k)]
  obtain ⟨_, _, _, _, _, _, e, he, _⟩ := proEtaleRingDerivedPullbackComposition h k
    (d.completedRing V) (d.completedRing W) (d.completedRing Z)
    (d.integralRingIso k) (d.integralRingIso h) (d.integralRingIso (h ≫ k))
    (d.integralRingIso_comp h k)
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  ext N U m
  exact (he' N U.unop m).trans (he N U.unop m).symm

/-- The unique fiber-product-pasting comparison. -/
def pbcActualModuleDirectCompIso := (pbcActualModuleDirectCompIso_exists h k d).exists.choose

/-- The ordinary pullback composition is the adjunction conjugate of actual pasting. -/
def pbcActualModulePullCompIso :
    pbcActualModulePull (h ≫ k) d ≅
      pbcActualModulePull k d ⋙ pbcActualModulePull h d :=
  (conjugateIsoEquiv
    ((pbcActualModuleAdjunction k d).comp
      (pbcActualModuleAdjunction h d))
    (pbcActualModuleAdjunction (h ≫ k) d)).symm
        (pbcActualModuleDirectCompIso h k d)

/-- Its degreewise comparison on cochain complexes. -/
def pbcActualModulePullCompComplexIso :
    (pbcActualModulePull (h ≫ k) d).mapHomologicalComplex (.up ℤ) ≅
      (pbcActualModulePull k d).mapHomologicalComplex (.up ℤ) ⋙
        (pbcActualModulePull h d).mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (pbcActualModulePullCompIso h k d) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm

/-- Universal derived counits retain the ordinary composition comparison on K-flat models. -/
theorem pbcActualDerivedPullCompIso_exists :
    ∃! e : pbcActualDerivedPull (h ≫ k) d ≅
        pbcActualDerivedPull k d ⋙ pbcActualDerivedPull h d,
      ∀ P : CochainComplex (pbcModules V (pbcAdicCompletion V d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (R := pbcAdicCompletion V d) P →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (R := pbcAdicCompletion V d) (P.X n)) →
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (pbcActualDerivedPull h d).map (pbcActualPullComplexCounit k d P) ≫
            pbcActualPullComplexCounit h d
              (((pbcActualModulePull k d).mapHomologicalComplex (.up ℤ)).obj P) =
          pbcActualPullComplexCounit (h ≫ k) d P ≫
            DerivedCategory.Q.map ((pbcActualModulePullCompComplexIso h k d).hom.app P) := by
  let C := pbcModules V (pbcAdicCompletion V d)
  let P : ObjectProperty (CochainComplex C ℤ) := fun K ↦
    K.IsKFlatIndependentCoefficients ∧ ∀ n : ℤ,
      SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := pbcAdicCompletion V d)
        (K.X n)
  let H : ObjectProperty (HomotopyCategory C (.up ℤ)) := fun K ↦ P K.as
  have hres : ∀ K : HomotopyCategory C (.up ℤ),
      ∃ (L : H.FullSubcategory) (s : L.obj ⟶ K),
        HomotopyCategory.quasiIso C (.up ℤ) s := by
    intro K
    obtain ⟨L, s, hl, hf, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients K.as
    refine ⟨⟨(HomotopyCategory.quotient C (.up ℤ)).obj L, hl, ?_⟩,
      (HomotopyCategory.quotient C (.up ℤ)).map s,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
    intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (pbcAdicCompletion V d) (L.X n)).symm (hf n)
  let Gk := (pbcActualModulePull k d).mapHomologicalComplex (.up ℤ)
  let Gh := (pbcActualModulePull h d).mapHomologicalComplex (.up ℤ)
  let Gc := (pbcActualModulePull (h ≫ k) d).mapHomologicalComplex (.up ℤ)
  let Lk := pbcActualDerivedPull k d
  let Lh := pbcActualDerivedPull h d
  let Lc := pbcActualDerivedPull (h ≫ k) d
  let ck := complexCounit (pbcActualModulePull k d) Lk (pbcActualPullCounit k d)
  let ch := complexCounit (pbcActualModulePull h d) Lh (pbcActualPullCounit h d)
  let cc := complexCounit (pbcActualModulePull (h ≫ k) d) Lc
    (pbcActualPullCounit (h ≫ k) d)
  let r : DerivedCategory.Q ⋙ (Lk ⋙ Lh) ⟶ (Gk ⋙ Gh) ⋙ DerivedCategory.Q :=
    whiskerRight ck Lh ≫ whiskerLeft Gk ch
  have hl (K : P.FullSubcategory) : IsIso (cc.app K.obj) := by
    exact pull_counit_iso (h ≫ k) d K.obj K.property.1
  have hr (K : P.FullSubcategory) : IsIso (r.app K.obj) := by
    have := pull_counit_iso k d K.obj K.property.1
    have := pull_counit_iso h d (Gk.obj K.obj)
      (pull_good k d K.obj K.property.1 K.property.2).1
    change IsIso (Lh.map (pbcActualPullComplexCounit k d K.obj) ≫
      pbcActualPullComplexCounit h d (Gk.obj K.obj))
    infer_instance
  let b := isoWhiskerRight (pbcActualModulePullCompComplexIso h k d) DerivedCategory.Q
  obtain ⟨e, he, hu⟩ := comparison_on_resolutions P hres Lc (Lk ⋙ Lh)
    (Gc ⋙ DerivedCategory.Q) ((Gk ⋙ Gh) ⋙ DerivedCategory.Q) cc r b hl hr
  have normalize (e' : Lc ≅ Lk ⋙ Lh) (K : CochainComplex C ℤ) :
      (e'.hom.app (DerivedCategory.Q.obj K) ≫ r.app K = cc.app K ≫ b.hom.app K) ↔
        (e'.hom.app (DerivedCategory.Q.obj K) ≫
            Lh.map (pbcActualPullComplexCounit k d K) ≫
            pbcActualPullComplexCounit h d (Gk.obj K) =
          pbcActualPullComplexCounit (h ≫ k) d K ≫
            DerivedCategory.Q.map ((pbcActualModulePullCompComplexIso h k d).hom.app K)) := by
    simp only [r, b, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      ck, ch, cc, complexCounit, pbcActualPullComplexCounit, isoWhiskerRight_hom,
      Category.assoc]
    rfl
  refine ⟨e, ?_, ?_⟩
  · intro K hp hf
    exact (normalize e K).1 (he K ⟨hp, hf⟩)
  · intro e' he'
    apply hu e'
    intro K hp
    exact (normalize e' K).2 (he' K hp.1 hp.2)

/-- The derived composition comparison with its resolving normalization retained. -/
def pbcActualDerivedPullCompIso := (pbcActualDerivedPullCompIso_exists h k d).exists.choose

/-- The identity direct image is normalized by the actual identity fiber-product map. -/
theorem pbcActualModuleDirectIdIso_exists (T : Scheme.{u}) :
    ∃! e : pbcActualModulePush (𝟙 T) d ≅ 𝟭 _,
      ∀ (N : pbcModules T (pbcAdicCompletion T d)) (U : T.ProEt)
        (m : ((pbcActualModulePush (𝟙 T) d).obj N).val.obj (op U)),
        (e.hom.app N).val.app (op U) m =
          N.val.map ((MorphismProperty.Over.pullbackId _ _ T).inv.app U).op m := by
  unfold pbcActualModulePush completedModuleDirectImage completedCoefficientDirectImageMap
  rw [actualCoefficient_eq d (𝟙 T)]
  exact d.modulePushId_existsUnique T

/-- The ordinary identity direct-image comparison with its fiber-product normalization. -/
def pbcActualModuleDirectIdIso (T : Scheme.{u}) := (pbcActualModuleDirectIdIso_exists d
  T).exists.choose

/-- The ordinary pullback unit is the adjunction conjugate of identity fiber-product pasting. -/
def pbcActualModulePullIdIso (T : Scheme.{u}) : pbcActualModulePull (𝟙 T) d ≅ 𝟭 _ :=
  ((conjugateIsoEquiv
    (pbcActualModuleAdjunction (𝟙 T) d)
    (Adjunction.id : (𝟭 (pbcModules T (pbcAdicCompletion T d))) ⊣ 𝟭 _)).symm
      (pbcActualModuleDirectIdIso d T)).symm

/-- The ordinary identity comparison on actual cochain complexes. -/
def pbcActualModulePullIdComplexIso (T : Scheme.{u}) :
    (pbcActualModulePull (𝟙 T) d).mapHomologicalComplex (.up ℤ) ≅ 𝟭 _ :=
  NatIso.mapHomologicalComplex (pbcActualModulePullIdIso d T) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)

/-- The derived identity is uniquely fixed on resolving models by the ordinary identity. -/
theorem pbcActualDerivedPullIdIso_exists (T : Scheme.{u}) :
    ∃! e : pbcActualDerivedPull (𝟙 T) d ≅ 𝟭 _,
      ∀ P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (R := pbcAdicCompletion T d) P →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (R := pbcAdicCompletion T d) (P.X n)) →
        e.hom.app (DerivedCategory.Q.obj P) =
          pbcActualPullComplexCounit (𝟙 T) d P ≫
            DerivedCategory.Q.map ((pbcActualModulePullIdComplexIso d T).hom.app P) := by
  let C := pbcModules T (pbcAdicCompletion T d)
  let P : ObjectProperty (CochainComplex C ℤ) := fun K ↦
    K.IsKFlatIndependentCoefficients ∧ ∀ n : ℤ,
      SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := pbcAdicCompletion T d)
        (K.X n)
  let H : ObjectProperty (HomotopyCategory C (.up ℤ)) := fun K ↦ P K.as
  have hres : ∀ K : HomotopyCategory C (.up ℤ),
      ∃ (L : H.FullSubcategory) (s : L.obj ⟶ K),
        HomotopyCategory.quasiIso C (.up ℤ) s := by
    intro K
    obtain ⟨L, s, hl, hf, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients K.as
    refine ⟨⟨(HomotopyCategory.quotient C (.up ℤ)).obj L, hl, ?_⟩,
      (HomotopyCategory.quotient C (.up ℤ)).map s,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
    intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (pbcAdicCompletion T d) (L.X n)).symm (hf n)
  let L := pbcActualDerivedPull (𝟙 T) d
  let G := (pbcActualModulePull (𝟙 T) d).mapHomologicalComplex (.up ℤ)
  let c := complexCounit (pbcActualModulePull (𝟙 T) d) L (pbcActualPullCounit (𝟙 T) d)
  let b : G ⋙ DerivedCategory.Q ≅ DerivedCategory.Q :=
    isoWhiskerRight (pbcActualModulePullIdComplexIso d T) DerivedCategory.Q ≪≫
      Functor.leftUnitor DerivedCategory.Q
  have hc (K : P.FullSubcategory) : IsIso (c.app K.obj) :=
    pull_counit_iso (𝟙 T) d K.obj K.property.1
  obtain ⟨e, he, hu⟩ := comparison_on_resolutions P hres L (𝟭 _)
    (G ⋙ DerivedCategory.Q) DerivedCategory.Q c (𝟙 _) b hc (fun _ ↦ inferInstance)
  have normalize (e' : L ≅ 𝟭 _) (K : CochainComplex C ℤ) :
      (e'.hom.app (DerivedCategory.Q.obj K) ≫ 𝟙 (DerivedCategory.Q.obj K) =
        c.app K ≫ b.hom.app K) ↔
      (e'.hom.app (DerivedCategory.Q.obj K) =
        pbcActualPullComplexCounit (𝟙 T) d K ≫
          DerivedCategory.Q.map ((pbcActualModulePullIdComplexIso d T).hom.app K)) := by
    change (e'.hom.app (DerivedCategory.Q.obj K) ≫ 𝟙 _ =
      pbcActualPullComplexCounit (𝟙 T) d K ≫
        (DerivedCategory.Q.map ((pbcActualModulePullIdComplexIso d T).hom.app K) ≫ 𝟙 _)) ↔ _
    simp only [Category.comp_id]
  refine ⟨e, ?_, ?_⟩
  · intro K hp hf
    exact (normalize e K).1 (he K ⟨hp, hf⟩)
  · intro e' he'
    apply hu e'
    intro K hp
    exact (normalize e' K).2 (he' K hp.1 hp.2)

/-- The derived pullback identity with its ordinary normalization retained. -/
def pbcActualDerivedPullIdIso (T : Scheme.{u}) := (pbcActualDerivedPullIdIso_exists d
  T).exists.choose

/-- Derived direct-image identity is conjugate to the normalized pullback identity. -/
def pbcActualDerivedDirectIdIso (T : Scheme.{u}) :
    pbcActualDerivedPush (𝟙 T) d ≅ 𝟭 _ :=
  conjugateIsoEquiv (pbcActualDerivedAdjunction (𝟙 T) d)
    (Adjunction.id : (𝟭 (PbcCompletedDerived T d)) ⊣ 𝟭 _)
    (pbcActualDerivedPullIdIso d T).symm

-- Compare two universal arrows from the same functor into the same full subcategory.
/-- Completed identity pullback fixes complete objects through its actual unit. -/
theorem pbcActualCompletedPullIdIso_exists (T : Scheme.{u}) :
    ∃! e : ObjectProperty.ι (PbcIsIntrinsicallyComplete T d) ⋙
        pbcActualCompletedPull (𝟙 T) d ≅ ObjectProperty.ι (PbcIsIntrinsicallyComplete T d),
      ∀ K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete T d),
        (pbcActualCompletedPullUnit (𝟙 T) d).app K.obj ≫ e.hom.app K =
          (pbcActualDerivedPullIdIso d T).hom.app K.obj := by
  let P : ObjectProperty (PbcCompletedDerived T d) := PbcIsIntrinsicallyComplete T d
  let I := ObjectProperty.ι P
  let L := pbcActualDerivedPull (𝟙 T) d
  let c := pbcActualDerivedPullIdIso d T
  let q : I ⋙ L ⟶ I ⋙ pbcActualCompletedPull (𝟙 T) d :=
    whiskerLeft I (pbcActualCompletedPullUnit (𝟙 T) d)
  have hq (K : ObjectProperty.FullSubcategory P) : IsIso (q.app K) := by
    change IsIso ((pbcActualCompletionUnit d T).app (L.obj K.obj))
    exact (Adjunction.ofIsRightAdjoint I).isIso_unit_app_iff_mem_essImage.mpr
      ⟨K, ⟨(c.app K.obj).symm⟩⟩
  let : ∀ K, IsIso (q.app K) := hq
  have : IsIso q := NatIso.isIso_of_isIso_app q
  let e : I ⋙ pbcActualCompletedPull (𝟙 T) d ≅ I :=
    (asIso q).symm ≪≫ isoWhiskerLeft I c ≪≫ Functor.rightUnitor I
  have he (K : ObjectProperty.FullSubcategory P) :
      (pbcActualCompletedPullUnit (𝟙 T) d).app K.obj ≫ e.hom.app K =
        c.hom.app K.obj := by
    change q.app K ≫ ((inv q).app K ≫ c.hom.app K.obj ≫ 𝟙 _) = _
    simp
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  ext K
  apply (cancel_epi (q.app K)).1
  exact (he' K).trans (he K).symm

/-- The completed identity comparison on the actual complete subcategory. -/
def pbcActualCompletedPullIdIso (T : Scheme.{u}) :=
  (pbcActualCompletedPullIdIso_exists d T).exists.choose

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

/-- The ringed pullback square is formed solely from canonical composition and commutativity. -/
def pbcActualCompletedPullSquareIso :
    pbcActualDerivedPull g d ⋙ pbcActualDerivedPull f' d ≅
      pbcActualDerivedPull f d ⋙ pbcActualDerivedPull g' d :=
  (pbcActualDerivedPullCompIso f' g d).symm ≪≫
    eqToIso (congrArg (fun a ↦ pbcActualDerivedPull a d) sq.w.symm) ≪≫
    pbcActualDerivedPullCompIso g' f d

/-- Ambient exchange is the adjunction mate of the actual ringed pullback square.
It precedes completion and constructibility. -/
def pbcActualCompletedAmbientExchange :
    pbcActualDerivedPush f d ⋙ pbcActualDerivedPull g d ⟶
      pbcActualDerivedPull g' d ⋙ pbcActualDerivedPush f' d :=
  (mateEquiv (pbcActualDerivedAdjunction f d) (pbcActualDerivedAdjunction f' d)
    (TwoSquare.mk _ _ _ _ (pbcActualCompletedPullSquareIso d sq).hom))

/-- Completed exchange is the ambient mate followed by completion and its direct-image
comparison, with the canonical pullback-completion identifications on both sides. -/
def pbcActualCompletedExchange :
    pbcActualDerivedPush f d ⋙ pbcActualCompletedPull g d ⟶
      pbcActualCompletedPull g' d ⋙ pbcActualDerivedPush f' d :=
  (isoWhiskerLeft _ (Iso.refl (pbcActualCompletedPull g d))).hom ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (pbcActualCompletedAmbientExchange d sq) (pbcActualCompletion d Y') ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft _ (pbcActualDirectCompletionIso f' d).hom ≫
    (Functor.associator _ _ _).inv ≫
    (isoWhiskerRight (Iso.refl (pbcActualCompletedPull g' d)).symm _).hom

end AlgebraicGeometry.Scheme
