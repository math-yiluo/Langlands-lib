/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficients
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.Mathlib.Algebra.Homology.Localization

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
/-! # Derived reduction and restriction of scalars

Source: Stacks Project, Tags 07A6, 06YY, 03CZ, 09T5 and 0DVC;
blueprint `prose-03-02`, order 1468
(auxiliary; not a blueprint node).

The index n denotes exponent n+1. All constructions use the completed coefficient
sheaf, with no auxiliary finite-field datum or restriction on the characteristic of Y.
The derived adjunction is normalized by its unit on every K-flat representative.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

universe t u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules.ScalarReductionProof

open scoped ChangeOfRings

section SameSiteAdjunction

universe a b r

variable {D : Type a} [Category.{b} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify K AddCommGrpCat.{r}]

private abbrev ringSheaf (A : Sheaf K CommRingCat.{r}) :=
  (sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj A

private noncomputable abbrev restriction
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :=
  restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map c)

private local instance {A : Sheaf K CommRingCat.{r}}
    {M : SheafOfModules.{r} (ringSheaf A)} {X Y : Dᵒᵖ} (i : X ⟶ Y) :
    Module (A.obj.obj Y)
      ((ModuleCat.restrictScalars ((ringSheaf A).obj.map i).hom).obj (M.val.obj Y)) :=
  inferInstanceAs (Module (A.obj.obj Y) (M.val.obj Y))

private theorem tensorRestriction_tmul
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) (M : SheafOfModules.{r} (ringSheaf A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (changeOfRingsPresheaf.{b, a, r} c M).map i (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  Classical.choose_spec (exists_changeOfRingsMap.{b, a, r} c M i) s m

private noncomputable def tensorPresheafFunctor
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :
    SheafOfModules.{r} (ringSheaf A) ⥤ PresheafOfModules.{r} (ringSheaf S).obj where
  obj M := changeOfRingsPresheaf.{b, a, r} c M
  map {M N} f :=
    show changeOfRingsPresheaf.{b, a, r} c M ⟶
      changeOfRingsPresheaf.{b, a, r} c N from
    { app := fun W ↦ (ModuleCat.extendScalars (c.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturality.{b, a, r} c _ f }
  map_id M := by
    ext W : 1
    change (ModuleCat.extendScalars (c.hom.app W).hom).map (𝟙 _) = _
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_comp _ _

private noncomputable def tensorFunctor
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :
    SheafOfModules.{r} (ringSheaf A) ⥤ SheafOfModules.{r} (ringSheaf S) :=
  tensorPresheafFunctor c ⋙ PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)

private noncomputable def tensorToRestriction
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (ringSheaf A)) (H : SheafOfModules.{r} (ringSheaf S))
    (f : changeOfRingsPresheaf.{b, a, r} c M ⟶ H.val) : M ⟶ (restriction c).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul, map_one] at h
        exact h }

private noncomputable def restrictionToTensor
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (ringSheaf A)) (H : SheafOfModules.{r} (ringSheaf S))
    (g : M ⟶ (restriction c).obj H) : changeOfRingsPresheaf.{b, a, r} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (c.hom.app Y).hom (g.val.app Y)
        ((changeOfRingsPresheaf.{b, a, r} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul, map_one]
    have atOne (W : Dᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (ringSheaf A)) (H : SheafOfModules.{r} (ringSheaf S)) :
    (changeOfRingsPresheaf.{b, a, r} c M ⟶ H.val) ≃ (M ⟶ (restriction c).obj H) where
  toFun := tensorToRestriction c M H
  invFun := restrictionToTensor c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
      (g.val.app W)

private noncomputable def tensorHomEquiv
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (ringSheaf A)) (H : SheafOfModules.{r} (ringSheaf S)) :
    ((tensorFunctor c).obj M ⟶ H) ≃ (M ⟶ (restriction c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

private theorem tensorHomEquiv_naturality_left
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    {M N : SheafOfModules.{r} (ringSheaf A)} (a : M ⟶ N)
    (H : SheafOfModules.{r} (ringSheaf S)) (f : (tensorFunctor c).obj N ⟶ H) :
    tensorHomEquiv c M H ((tensorFunctor c).map a ≫ f) =
      a ≫ tensorHomEquiv c N H f := by
  change tensorPresheafHomEquiv c M H
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)).map
          ((tensorPresheafFunctor c).map a) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext W m
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv
    (changeOfRingsPresheaf.{b, a, r} c N) H f).app W
      ((ModuleCat.extendScalars (c.hom.app W).hom).map (a.val.app W)
        ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

private theorem tensorHomEquiv_naturality_right
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (ringSheaf A))
    {H H' : SheafOfModules.{r} (ringSheaf S)}
    (f : (tensorFunctor c).obj M ⟶ H) (b : H ⟶ H') :
    tensorHomEquiv c M H' (f ≫ b) =
      tensorHomEquiv c M H f ≫ (restriction c).map b := by
  change tensorPresheafHomEquiv c M H'
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        (f ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def tensorAdjunction
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) : tensorFunctor c ⊣ restriction c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv c
      homEquiv_naturality_left_symm := by
        intro M N H a g
        apply (tensorHomEquiv c M H).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ tensorHomEquiv_naturality_right c _ f b }

private theorem tensorAdjunction_unit_apply
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (ringSheaf A)) (W : Dᵒᵖ) (m : M.val.obj W) :
    ((tensorAdjunction c).unit.app M).val.app W m =
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).unit.app
        (changeOfRingsPresheaf.{b, a, r} c M)).app W
          ((ModuleCat.extendRestrictScalarsAdj (c.hom.app W).hom).unit.app
            (M.val.obj W) m)) := by
  rw [← Adjunction.homEquiv_id, tensorAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

private theorem tensorAdjunction_of_identifications
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (E : SheafOfModules.{r} (ringSheaf A) ⥤ SheafOfModules.{r} (ringSheaf S))
    (h : ∀ M, E.obj M = changeOfRings c M)
    (hm : ∀ {M N} (f : M ⟶ N),
      E.map f = eqToHom (h M) ≫ changeOfRingsHom c M f ≫ eqToHom (h N).symm) :
    ∃ adj : E ⊣ restriction c,
      ∀ (M : SheafOfModules.{r} (ringSheaf A)) (W : Dᵒᵖ) (m : M.val.obj W),
        (adj.unit.app M).val.app W m = (eqToHom (h M).symm).val.app W
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).unit.app
            (changeOfRingsPresheaf.{b, a, r} c M)).app W
              ((ModuleCat.extendRestrictScalarsAdj (c.hom.app W).hom).unit.app
                (M.val.obj W) m)) := by
  let e : E ≅ tensorFunctor c := NatIso.ofComponents (fun M ↦ eqToIso (h M)) (by
    intro M N f
    change E.map f ≫ eqToHom (h N) = eqToHom (h M) ≫ changeOfRingsHom c M f
    rw [hm]
    simp)
  refine ⟨(tensorAdjunction c).ofNatIsoLeft e.symm, ?_⟩
  intro M W m
  change (e.inv.app M).val.app W (((tensorAdjunction c).unit.app M).val.app W m) = _
  rw [tensorAdjunction_unit_apply]
  rfl

end SameSiteAdjunction

end SheafOfModules.ScalarReductionProof

namespace ScalarReductionDerivedProof

set_option linter.style.haveILetI false in
private theorem ind_of_eventually_constant {J C : Type*} [Category* J] [Category* C]
    [IsFiltered J] (F : J ⥤ C) (j₀ : J)
    (hevent : F.IsEventuallyConstantFrom j₀) :
    ∃ X, IsEssentiallyConstantIndDiagram F X := by
  let c := hevent.cocone
  letI : IsIso (c.ι.app j₀) := hevent.isIso_ι_of_isColimit hevent.isColimitCocone
  refine ⟨c.pt, ⟨inferInstance, c.ι, j₀, (asIso (c.ι.app j₀)).inv, ?_, ?_⟩⟩
  · exact (asIso (c.ι.app j₀)).inv_hom_id
  · intro j
    let k := IsFiltered.max j₀ j
    let a : j₀ ⟶ k := IsFiltered.leftToMax _ _
    let b : j ⟶ k := IsFiltered.rightToMax _ _
    refine ⟨k, a, b, ?_⟩
    letI : IsIso (c.ι.app k) := hevent.isIso_ι_of_isColimit' hevent.isColimitCocone k a
    apply (cancel_mono (c.ι.app k)).1
    rw [c.ι.naturality b]
    simp only [Functor.const_obj_map, Category.assoc]
    rw [← Category.assoc, c.ι.naturality a]
    simp

set_option linter.style.haveILetI false in
private theorem exactFunctor_ind_essentialConstancy
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (R : B ⥤ A) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R] :
    ∀ X : HomotopyCategory B (.up ℤ),
      ∃ Y : DerivedCategory A,
        IsEssentiallyConstantIndDiagram
          (MorphismProperty.Under.forget (HomotopyCategory.quasiIso B (.up ℤ)) ⊤ X ⋙
            Under.forget X ⋙ R.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) Y := by
  intro X
  let W := HomotopyCategory.quasiIso B (.up ℤ)
  let J := W.Under ⊤ X
  let D := MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙
    R.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  letI : IsFiltered J := by
    let j₀ : J := MorphismProperty.Under.mk ⊤ (𝟙 X) (W.id_mem X)
    refine { nonempty := ⟨j₀⟩, cocone_objs := ?_, cocone_maps := ?_ }
    · intro j j'
      obtain ⟨ψ, hψ⟩ := (MorphismProperty.RightFraction.mk j.hom j.prop j'.hom).exists_leftFraction
      let k : J := MorphismProperty.Under.mk ⊤ (j'.hom ≫ ψ.s)
        (W.comp_mem _ _ j'.prop ψ.hs)
      exact ⟨k, MorphismProperty.Under.homMk ψ.f hψ.symm,
        MorphismProperty.Under.homMk ψ.s, trivial⟩
    · intro j j' f g
      obtain ⟨Z, t, ht, heq⟩ := MorphismProperty.HasLeftCalculusOfFractions.ext
        f.right g.right j.hom j.prop (by simp)
      let k : J := MorphismProperty.Under.mk ⊤ (j'.hom ≫ t)
        (W.comp_mem _ _ j'.prop ht)
      refine ⟨k, MorphismProperty.Under.homMk t, ?_⟩
      exact MorphismProperty.Under.Hom.ext heq
  let j₀ : J := MorphismProperty.Under.mk ⊤ (𝟙 X) (W.id_mem X)
  let hevent : D.IsEventuallyConstantFrom j₀ := by
    intro j f
    change IsIso (DerivedCategory.Qh.map ((R.mapHomotopyCategory (.up ℤ)).map f.right))
    have hfj : f.right = j.hom := by
      simpa [j₀] using f.w.symm
    have hf : W f.right := by
      rw [hfj]
      exact j.prop
    obtain ⟨g, hg⟩ := (HomotopyCategory.quotient B (.up ℤ)).map_surjective f.right
    have hq : HomologicalComplex.quasiIso B (.up ℤ) g := by
      apply (HomotopyCategory.quotient_map_mem_quasiIso_iff g).1
      rw [hg]
      exact hf
    letI : QuasiIso g := hq
    have hmap : HomologicalComplex.quasiIso A (.up ℤ)
        ((R.mapHomologicalComplex (.up ℤ)).map g) := by
      exact HomologicalComplex.quasiIso_map_of_preservesHomology g R
    have hmap' : HomotopyCategory.quasiIso A (.up ℤ)
        ((R.mapHomotopyCategory (.up ℤ)).map
          ((HomotopyCategory.quotient B (.up ℤ)).map g)) := by
      change HomotopyCategory.quasiIso A (.up ℤ)
        ((HomotopyCategory.quotient A (.up ℤ)).map
          ((R.mapHomologicalComplex (.up ℤ)).map g))
      rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
      exact hmap
    simpa only [hg] using (Localization.inverts DerivedCategory.Qh _ _ hmap')
  exact ind_of_eventually_constant D j₀ hevent

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem derivedAdjunction_of_resolutions
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (L : A ⥤ B) (R : B ⥤ A) [L.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (adj : L ⊣ R)
    (LD : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ LD ⟶
      L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hLD : LD.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ)))
    (hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X),
        IsIso (ε.app Y) ∧ HomotopyCategory.quasiIso A (.up ℤ) s) :
    ∃ d : LD ⊣ R.mapDerivedCategory,
      ∀ X : HomotopyCategory A (.up ℤ),
        d.unit.app (DerivedCategory.Qh.obj X) ≫ R.mapDerivedCategory.map (ε.app X) ≫
          R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj X) =
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app X) := by
  have hR : ∀ K : HomotopyCategory B (.up ℤ),
      ∃ X : DerivedCategory A,
        IsEssentiallyConstantIndDiagram
          (MorphismProperty.Under.forget (HomotopyCategory.quasiIso B (.up ℤ)) ⊤ K ⋙
            Under.forget K ⋙ R.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) X := by
    intro K
    exact exactFunctor_ind_essentialConstancy R K
  let P : Set (HomotopyCategory A (.up ℤ)) := {X | IsIso (ε.app X)}
  have hL : ∀ M : HomotopyCategory A (.up ℤ),
      ∃ X : DerivedCategory B,
        IsEssentiallyConstantProDiagram
          (MorphismProperty.Over.forget (HomotopyCategory.quasiIso A (.up ℤ)) ⊤ M ⋙
            Over.forget M ⋙ L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) X := by
    intro M
    obtain ⟨Y, u, hY, _⟩ := Functor.resolvingClass_essentialConstancy
      (HomotopyCategory.quasiIso A (.up ℤ))
      (L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) P hres (by
        intro X Y s hX hY hs
        have : IsIso (ε.app X) := hX
        have : IsIso (ε.app Y) := hY
        have : IsIso (DerivedCategory.Qh.map s) :=
          Localization.inverts DerivedCategory.Qh _ _ hs
        have hn := ε.naturality s
        change LD.map (DerivedCategory.Qh.map s) ≫ ε.app Y =
          ε.app X ≫ (L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map s at hn
        rw [← isIso_comp_left_iff (ε.app X), ← hn]
        infer_instance) M
    exact ⟨Y, hY⟩
  let β : R.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ≅
      DerivedCategory.Qh ⋙ R.mapDerivedCategory :=
    (R.mapDerivedCategoryFactorsh).symm
  have hRF : R.mapDerivedCategory.IsRightDerivedFunctor β.hom
      (HomotopyCategory.quasiIso B (.up ℤ)) := by
    exact Functor.isRightDerivedFunctor_of_inverts
      (HomotopyCategory.quasiIso B (.up ℤ)) _ R.mapDerivedCategoryFactorsh
  obtain ⟨d, hd⟩ := exists_derived_adjunction_compatibility
    R L adj hR hL R.mapDerivedCategory LD β.hom ε hRF hLD
  refine ⟨d, ?_⟩
  intro X
  have h := hd X ((L.mapHomotopyCategory (.up ℤ)).obj X) (𝟙 _)
  rw [DerivedCategory.Qh.map_id] at h
  erw [Category.comp_id] at h
  rw [Adjunction.homEquiv_id (adj.mapHomotopyCategory (.up ℤ)) X] at h
  have hn := Adjunction.homEquiv_naturality_right d
    (𝟙 (LD.obj (DerivedCategory.Qh.obj X))) (ε.app X)
  rw [Category.id_comp] at hn
  have hn' : d.homEquiv (DerivedCategory.Qh.obj X)
      (DerivedCategory.Qh.obj ((L.mapHomotopyCategory (.up ℤ)).obj X)) (ε.app X) =
      d.unit.app (DerivedCategory.Qh.obj X) ≫ R.mapDerivedCategory.map (ε.app X) := by
    simpa only [Functor.comp_obj, Adjunction.homEquiv_id] using hn
  rw [hn'] at h
  calc
    _ = (d.unit.app (DerivedCategory.Qh.obj X) ≫
        R.mapDerivedCategory.map (ε.app X)) ≫
        R.mapDerivedCategoryFactorsh.hom.app
          ((L.mapHomotopyCategory (.up ℤ)).obj X) := by rw [Category.assoc]
    _ = (DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
        R.mapDerivedCategoryFactorsh.inv.app
          ((L.mapHomotopyCategory (.up ℤ)).obj X)) ≫
        R.mapDerivedCategoryFactorsh.hom.app
          ((L.mapHomotopyCategory (.up ℤ)).obj X) := by
      rw [h]
      dsimp [β]
    _ = _ := by simp

section KFlatResolutions

universe a b r

private theorem kFlatResolutions
    {C : Type a} [Category.{b} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {O : Sheaf J CommRingCat.{r}}
    (G : CochainComplex (SheafOfModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J O)) ℤ) :
    ∃ (K : CochainComplex (SheafOfModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J O)) ℤ) (s : K ⟶ G),
      K.IsKFlatIndependentCoefficients ∧ QuasiIso s := by
  obtain ⟨K, s, hK, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients G
  exact ⟨K, s, hK, hs⟩

end KFlatResolutions

end ScalarReductionDerivedProof

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})

/-- Modules over the completed coefficient ring, without a finite-field convention.
Source: Stacks Tag 06YY
(auxiliary; not a blueprint node). -/
@[reducible]
noncomputable def scalarReductionSource :=
  SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y))

/-- Modules over the constant finite quotient ring at exponent n+1.
Source: Stacks Tag 06YY
(auxiliary; not a blueprint node). -/
@[reducible]
noncomputable def scalarReductionTarget (n : ℕ) :=
  SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n)

/-- The standard localization of completed-coefficient module complexes.
Source: Stacks Tag 05RU
(auxiliary; not a blueprint node). -/
noncomputable instance scalarReductionSourceDerived :
    HasDerivedCategory (scalarReductionSource l E Y) := HasDerivedCategory.standard _

/-- The standard localization of finite-coefficient module complexes.
Source: Stacks Tag 05RU
(auxiliary; not a blueprint node). -/
noncomputable instance scalarReductionTargetDerived (n : ℕ) :
    HasDerivedCategory (scalarReductionTarget l E Y n) := HasDerivedCategory.standard _

/-- The site fits in the chosen module universe via its standard small model.
Source: blueprint small-site convention
(auxiliary; not a blueprint node). -/
theorem scalarReductionSiteSmall :
    EssentiallySmall.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt Y) :=
  essentiallySmallSelf _

attribute [local instance] scalarReductionSiteSmall

variable (n : ℕ)

/-- Restriction along the coordinate projection of the completed ring sheaf.
Source: Stacks Tag 03CZ
(auxiliary; not a blueprint node). -/
@[reducible]
noncomputable def scalarReductionRestriction :
    scalarReductionTarget l E Y n ⥤ scalarReductionSource l E Y :=
  SheafOfModules.restrictScalars
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E Y n))

/-- Additivity of the explicit scalar-restriction functor.
Source: Stacks Tag 03CZ
(auxiliary; not a blueprint node). -/
instance scalarReductionRestrictionAdditive :
    (scalarReductionRestriction l E Y n).Additive := by
  unfold scalarReductionRestriction
  infer_instance

/-- Restriction is exact, since it leaves underlying abelian sheaves unchanged.
Source: Stacks Tags 03DA and 03CZ
(auxiliary; not a blueprint node).
Proof: a kernel is the same sectionwise kernel with restricted action. A cokernel
is the sheafification of the same sectionwise abelian-group quotient in both
module categories; its action is precomposed with the coefficient projection.
Thus restriction preserves kernels and cokernels and is additive, hence exact. -/
theorem scalarReductionRestriction_exact :
    PreservesFiniteLimits (scalarReductionRestriction l E Y n) ∧
      PreservesFiniteColimits (scalarReductionRestriction l E Y n) := by
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} Y
  let R := SheafOfModules.derivedChangeRingIndependentCoefficients
    (AlgebraicGeometry.Scheme.ProEt.topology Y)
    (completedIntegralCommRingSheafUnrestricted l E Y)
  let S := integralCoefficientSheaf l E Y n
  have : PreservesFiniteLimits
      (scalarReductionRestriction l E Y n ⋙ SheafOfModules.toSheaf R) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf S))
  have : PreservesFiniteColimits
      (scalarReductionRestriction l E Y n ⋙ SheafOfModules.toSheaf R) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf S))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf R),
    preservesFiniteColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf R)⟩

/-- Finite-limit preservation supplied by exactness.
Source: Stacks Tag 03DA
(auxiliary; not a blueprint node). -/
theorem scalarReductionRestrictionLimits :
    PreservesFiniteLimits (scalarReductionRestriction l E Y n) :=
  (scalarReductionRestriction_exact l E Y n).1

attribute [local instance] scalarReductionRestrictionLimits

/-- Finite-colimit preservation supplied by exactness.
Source: Stacks Tag 03DA
(auxiliary; not a blueprint node). -/
theorem scalarReductionRestrictionColimits :
    PreservesFiniteColimits (scalarReductionRestriction l E Y n) :=
  (scalarReductionRestriction_exact l E Y n).2

attribute [local instance] scalarReductionRestrictionColimits

set_option linter.defProp false in
/-- The canonical universal derived-change-of-rings witness for the limit projection.
Source: Stacks Tag 06YY
(auxiliary; not a blueprint node). -/
noncomputable def scalarReductionExistence :=
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)))
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y n)))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
    (O := completedIntegralCommRingSheafUnrestricted l E Y)
    (O' := integralCoefficientCommRingSheaf l E Y n)
    (completedIntegralCommRingProjectionUnrestricted l E Y n)

/-- Ordinary scalar extension, with the sectionwise tensor objects and maps fixed
by the derived-change-of-rings witness.
Source: Stacks Tag 06YY
(auxiliary; not a blueprint node). -/
noncomputable def scalarReductionExtension :
    scalarReductionSource l E Y ⥤ scalarReductionTarget l E Y n :=
  (scalarReductionExistence l E Y n).choose

/-- Additivity of tensor extension.
Source: Stacks Tag 06YY
(auxiliary; not a blueprint node). -/
theorem scalarReductionExtensionAdditive :
    (scalarReductionExtension l E Y n).Additive :=
  (scalarReductionExistence l E Y n).choose_spec.choose_spec.choose_spec.choose

attribute [local instance] scalarReductionExtensionAdditive

attribute [local irreducible] scalarReductionExistence scalarReductionExtension
  HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option linter.defProp false in
/-- The universal derived pair, including the K-flat computation and exactness.
Source: Stacks Tag 06YY
(auxiliary; not a blueprint node). -/
noncomputable def scalarReductionDerivedExistence :
    ∃ (LF : DerivedCategory (scalarReductionSource l E Y) ⥤
        DerivedCategory (scalarReductionTarget l E Y n))
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (scalarReductionExtension l E Y n).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (scalarReductionSource l E Y) (.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ P : CochainComplex (scalarReductionSource l E Y) ℤ,
          P.IsKFlatIndependentCoefficients →
            IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  unfold scalarReductionExtension
  exact (scalarReductionExistence l E Y n).choose_spec.choose_spec.choose_spec.choose_spec.2.2

attribute [local semireducible] scalarReductionExtension

attribute [local irreducible] scalarReductionDerivedExistence

end WeilConjectures

namespace WeilConjectures

section

set_option autoImplicit false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})
variable (n : ℕ)
attribute [local instance] scalarReductionSiteSmall
attribute [local instance] scalarReductionRestrictionLimits
attribute [local instance] scalarReductionRestrictionColimits
attribute [local instance] scalarReductionExtensionAdditive

/-- Termwise exact restriction descended through localization.
Source: Stacks Tag 015F
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction). -/
noncomputable def scalarReductionDerivedRestriction :=
  (scalarReductionRestriction l E Y n).mapDerivedCategory

/-- Derived tensor with the finite quotient over the completed coefficient ring.
Its universal property determines it up to unique compatible isomorphism.
Source: Stacks Tag 06YY
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction). -/
noncomputable def scalarReductionDerivedExtension :
    DerivedCategory (scalarReductionSource l E Y) ⥤
      DerivedCategory (scalarReductionTarget l E Y n) :=
  (scalarReductionDerivedExistence l E Y n).choose

/-- The universal comparison on homotopy complexes, an isomorphism on K-flat ones.
Source: Stacks Tag 06YY
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction). -/
noncomputable def scalarReductionCounit :
    DerivedCategory.Qh ⋙ scalarReductionDerivedExtension l E Y n ⟶
      (scalarReductionExtension l E Y n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  (scalarReductionDerivedExistence l E Y n).choose_spec.choose

-- The proof-valued witnesses have large types; their bodies are never needed below.

end

end WeilConjectures

namespace WeilConjectures

section

set_option autoImplicit false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})
variable (n : ℕ)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The underived tensor/restriction adjunction with its sectionwise unit normalization.
Source: Stacks Tag 03CZ
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction).
Proof: send a tensor-linear map v to x ↦ v(1 tensor x), and send w to
s tensor x ↦ s w(x). Balancing and restriction compatibility descend both maps
through sheafification. Their composites are identities on tensor generators.
Consequently the unit is precisely the image of 1 tensor x in the sheafification. -/
theorem scalarReductionExtension_adjunction :
    ∃ adj : scalarReductionExtension l E Y n ⊣ scalarReductionRestriction l E Y n,
      ∀ (M : scalarReductionSource l E Y)
        (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) (x : M.val.obj U),
        (adj.unit.app M).val.app U x =
          (eqToHom ((scalarReductionExistence l E Y n).choose_spec.choose M).symm).val.app U
            (((PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
              (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
              (R := integralCoefficientSheaf l E Y n)
              (𝟙 (integralCoefficientSheaf l E Y n).obj)).unit.app
              (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)}
                (completedIntegralCommRingProjectionUnrestricted l E Y n) M)).app U
              ((ModuleCat.extendRestrictScalarsAdj
                ((completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app U).hom).unit.app
                  (M.val.obj U) x)) := by
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} Y
  exact SheafOfModules.ScalarReductionProof.tensorAdjunction_of_identifications
    (K := AlgebraicGeometry.Scheme.ProEt.topology Y)
    (A := completedIntegralCommRingSheafUnrestricted l E Y)
    (S := integralCoefficientCommRingSheaf l E Y n)
    (completedIntegralCommRingProjectionUnrestricted l E Y n)
    (scalarReductionExtension l E Y n)
    (scalarReductionExistence l E Y n).choose_spec.choose
    (scalarReductionExistence l E Y n).choose_spec.choose_spec.choose

end

end WeilConjectures
