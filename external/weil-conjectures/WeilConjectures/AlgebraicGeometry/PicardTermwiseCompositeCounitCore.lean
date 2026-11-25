/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardTermwiseModels

/-! # Core counit composition calculation

Source: Stacks Project, Tags 06YJ and 0D5S.
(blueprint: lem-sc-picard-termwise-composite-counit-core)

This is the two-morphism counit factorization on a complex. The general
compatibility equation additionally uses naturality at the fixed morphism
and the associativity law for three derived pullbacks.
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

attribute [local instance] Functor.additive_of_preserves_binary_products

attribute [local irreducible] picardTermwiseCounit Modules.tensorPullbackCompositionIso
  Modules.tensorPullback Modules.tensorPullbackObj
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] Modules.Hom DerivedCategory
  HomotopyCategory DerivedCategory.Q DerivedCategory.Qh

private theorem invert_factorization_map
    {C D : Type*} [Category C] [Category D] (Q : C ⥤ D)
    {A B M : D} {X Y : C} (c : A ≅ B) (b : X ≅ Y)
    (e : B ⟶ Q.obj Y) (f : A ⟶ M) (g : M ⟶ Q.obj X)
    (h : c.hom ≫ e = f ≫ g ≫ Q.map b.hom) :
    c.inv ≫ f ≫ g = e ≫ Q.map b.inv := by
  apply (Iso.inv_comp_eq c).2
  rw [← Category.assoc, h]
  simp only [Category.assoc, ← Q.map_comp, b.hom_inv_id, Q.map_id, Category.comp_id]

private theorem normalize_counit
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ E) (Q : D ⥤ E) (A : C) (B : D) (e : L.obj A ⟶ Q.obj B) :
    L.map (𝟙 A) ≫ e ≫ Q.map (𝟙 B) ≫ 𝟙 (Q.obj B) = e := by
  simp

private theorem invert_factorization_map_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (M : D ⥤ E) (N : C ⥤ E) (c : L ⋙ M ≅ N)
    {X X' : C} {Y Y' : D} {Z Z' R R' : E}
    (eX : X ≅ X') (eY : Y ≅ Y') (eZ : Z ≅ Z') (eR : R ≅ R')
    (f : L.obj X ⟶ Y) (g : M.obj Y ⟶ Z) (h : N.obj X ⟶ R)
    (k : R ⟶ Z) (k' : R' ⟶ Z')
    (hf : c.inv.app X ≫ M.map f ≫ g = h ≫ k)
    (hk : k ≫ eZ.hom = eR.hom ≫ k') :
    c.inv.app X' ≫ M.map (L.map eX.inv ≫ f ≫ eY.hom) ≫
        (M.map eY.inv ≫ g ≫ eZ.hom) =
      (N.map eX.inv ≫ h ≫ eR.hom) ≫ k' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← M.map_comp_assoc eY.hom eY.inv, eY.hom_inv_id, M.map_id, Category.id_comp]
  have hn := c.inv.naturality eX.inv
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, reassoc_of% hf, hk]

private theorem pushforwardCongr_refl {X Y : Scheme.{v}} (f : X ⟶ Y) :
    Modules.pushforwardCongr (rfl : f = f) = Iso.refl _ := by
  ext M U
  simp

private theorem tensor_composition_inv
    {X Y Z : Scheme.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Modules.tensorPullbackCompositionIso f g (f ≫ g) rfl).inv =
      ((conjugateIsoEquiv
        (Classical.choose (Modules.exists_tensorPullbackAdjunction (f ≫ g)))
        ((Classical.choose (Modules.exists_tensorPullbackAdjunction g)).comp
          (Classical.choose (Modules.exists_tensorPullbackAdjunction f)))).symm
        (Modules.pushforwardComp f g).symm).hom := by
  unfold Modules.tensorPullbackCompositionIso
  rw [pushforwardCongr_refl]
  simp only [Iso.trans_refl, conjugateIsoEquiv_symm_apply_inv,
    conjugateIsoEquiv_symm_apply_hom, Iso.symm_hom]

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

-- The pinned dependent counits require substantial instance elaboration.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Composition of the termwise counits on a complex.

Source: Stacks Project, Tags 06YJ and 0D5S.
(blueprint: lem-sc-picard-termwise-composite-counit-core)

Proof: evaluate the defining left-derived-lift equation for the pinned comparison
at the homotopy class of P = overEquiv(U)(K). Whisker it with the quotient from
complexes. Naturality of quotientCompQhIso and mapHomotopyCategoryFactors rewrites
its three counits as picardTermwiseCounit. The ordinary tensor comparison becomes
the inverse of the termwise model restriction comparison. Precompose with the
inverse derived comparison and postcompose with the ordinary comparison to get
the displayed equation. Only these comparisons are canceled; no counit needs to
be invertible, so this works for zero complexes and empty schemes as well. -/
theorem picard_termwise_counit_composition
    (W : Scheme.{v}) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    {T T' : Scheme.{v}} (i : T' ⟶ T) (s : T ⟶ U.toScheme) :
    let c : ∀ {X Y Z : Scheme.{v}} (f : X ⟶ Y) (g : Y ⟶ Z),
        derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g) :=
      fun f g ↦ Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) f g
    let P := ((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K
    (c i s).inv.app (DerivedCategory.Q.obj P) ≫
        (derivedPullback i).map ((picardTermwiseCounit s).app P) ≫
          (picardTermwiseCounit i).app (picardTermwiseModel W U K s) =
      (picardTermwiseCounit (i ≫ s)).app P ≫
        DerivedCategory.Q.map
          (picardTermwiseModelRestrictionIso W U K i s (i ≫ s) rfl).hom := by
  classical
  let P : CochainComplex U.toScheme.Modules ℤ :=
    (((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K)
  let a : ∀ {X Y : Scheme.{v}} (f : X ⟶ Y), (Modules.tensorPullback f).Additive :=
    fun f ↦ Classical.choose exists_derivedPullbackComposition f
  let ε : ∀ {X Y : Scheme.{v}} (f : X ⟶ Y),
      DerivedCategory.Qh ⋙ derivedPullback f ⟶
        (Modules.tensorPullback f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    fun f ↦ Classical.choose (Classical.choose_spec exists_derivedPullbackComposition) f
  let c : ∀ {X Y Z : Scheme.{v}} (f : X ⟶ Y) (g : Y ⟶ Z),
      derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g) :=
    fun f g ↦ Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f g
  let q := (HomotopyCategory.quotient
    (SheafOfModules.{v} (moduleRings U.toScheme.toRingedSpace)) (.up ℤ)).obj P
  let := a i
  let := a s
  let := a (i ≫ s)
  have : (derivedPullback (i ≫ s)).IsLeftDerivedFunctor (ε (i ≫ s))
      (HomotopyCategory.quasiIso U.toScheme.Modules (.up ℤ)) :=
    Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)) (i ≫ s)
  let δ := ((conjugateIsoEquiv
      (Classical.choose (Modules.exists_tensorPullbackAdjunction (i ≫ s)))
      ((Classical.choose (Modules.exists_tensorPullbackAdjunction s)).comp
        (Classical.choose (Modules.exists_tensorPullbackAdjunction i)))).symm
      (Modules.pushforwardComp i s).symm)
  let t := Functor.mapHomotopyCategoryCompIso δ (.up ℤ)
  let b := (Functor.mapHomologicalComplexCompIso
    (Modules.tensorPullbackCompositionIso i s (i ≫ s) rfl).symm (.up ℤ)).app P
  let β : DerivedCategory.Qh ⋙ (derivedPullback s ⋙ derivedPullback i) ⟶
      (Modules.tensorPullback (i ≫ s)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    (Functor.associator DerivedCategory.Qh (derivedPullback s) (derivedPullback i)).inv ≫
      Functor.whiskerRight (ε s) (derivedPullback i) ≫
      (Functor.associator _ DerivedCategory.Qh (derivedPullback i)).hom ≫
      Functor.whiskerLeft _ (ε i) ≫
      (Functor.associator _ _ DerivedCategory.Qh).inv ≫
      Functor.whiskerRight t.hom DerivedCategory.Qh
  have hc' : (c i s).hom = (derivedPullback (i ≫ s)).leftDerivedLift (ε (i ≫ s))
      (HomotopyCategory.quasiIso U.toScheme.Modules (.up ℤ))
      (derivedPullback s ⋙ derivedPullback i) β :=
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))).1 i s
  have fac₀ := congrArg
    (fun k ↦ k.app (DerivedCategory.Qh.obj q) ≫ (ε (i ≫ s)).app q) hc'
  have fac₁ := (derivedPullback (i ≫ s)).leftDerived_fac_app (ε (i ≫ s))
    (HomotopyCategory.quasiIso U.toScheme.Modules (.up ℤ))
    (derivedPullback s ⋙ derivedPullback i) β q
  have fac : (c i s).hom.app (DerivedCategory.Qh.obj q) ≫ (ε (i ≫ s)).app q =
      (derivedPullback i).map ((ε s).app q) ≫
        (ε i).app (((Modules.tensorPullback s).mapHomotopyCategory (.up ℤ)).obj q) ≫
          DerivedCategory.Qh.map (t.hom.app q) := by
    exact fac₀.trans (fac₁.trans (by
      simp only [β, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp]))
  have ht : t.hom.app q = (HomotopyCategory.quotient _ (.up ℤ)).map b.hom := by
    change (HomotopyCategory.quotient _ (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex δ.hom (.up ℤ)).app P) = _
    have hb : δ.hom = (Modules.tensorPullbackCompositionIso i s (i ≫ s) rfl).inv :=
      (tensor_composition_inv i s).symm
    rw [hb]
    rfl
  rw [ht] at fac
  have hfac := invert_factorization_map
    (DerivedCategory.Qh (C := T'.Modules))
    ((c i s).app (DerivedCategory.Qh.obj q))
    ((HomotopyCategory.quotient T'.Modules (.up ℤ)).mapIso b)
    ((ε (i ≫ s)).app q) ((derivedPullback i).map ((ε s).app q))
    ((ε i).app (((Modules.tensorPullback s).mapHomotopyCategory (.up ℤ)).obj q)) fac
  let PS := ((Modules.tensorPullback s).mapHomologicalComplex (.up ℤ)).obj P
  let e := DerivedCategory.quotientCompQhIso U.toScheme.Modules
  let eT := DerivedCategory.quotientCompQhIso T.Modules
  let eT' := DerivedCategory.quotientCompQhIso T'.Modules
  dsimp only [picardTermwiseModel, picardTermwiseModelRestrictionIso]
  simp only [picardTermwiseCounit, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Functor.mapHomotopyCategoryFactors_hom_app]
  change (c i s).inv.app (DerivedCategory.Q.obj P) ≫
      (derivedPullback i).map
        ((derivedPullback s).map (e.inv.app P) ≫ (ε s).app q ≫
          DerivedCategory.Qh.map (𝟙 _) ≫ eT.hom.app PS) ≫
      ((derivedPullback i).map (eT.inv.app PS) ≫
        (ε i).app (((Modules.tensorPullback s).mapHomotopyCategory (.up ℤ)).obj q) ≫
          DerivedCategory.Qh.map (𝟙 _) ≫ eT'.hom.app _) =
    ((derivedPullback (i ≫ s)).map (e.inv.app P) ≫
      (ε (i ≫ s)).app q ≫ DerivedCategory.Qh.map (𝟙 _) ≫ eT'.hom.app _) ≫
        DerivedCategory.Q.map b.inv
  erw [(DerivedCategory.Qh (C := T.Modules)).map_id, Category.id_comp,
    (DerivedCategory.Qh (C := T'.Modules)).map_id, Category.id_comp,
    (DerivedCategory.Qh (C := T'.Modules)).map_id, Category.id_comp]
  exact invert_factorization_map_transport
    (derivedPullback s) (derivedPullback i) (derivedPullback (i ≫ s)) (c i s)
    (e.app P) (eT.app PS) (eT'.app _) (eT'.app _)
    ((ε s).app q)
    ((ε i).app (((Modules.tensorPullback s).mapHomotopyCategory (.up ℤ)).obj q))
    ((ε (i ≫ s)).app q) _ (DerivedCategory.Q.map b.inv) hfac
    (DerivedCategory.quotientCompQhIso_hom_naturality b.inv)

end
end AlgebraicGeometry.Scheme
