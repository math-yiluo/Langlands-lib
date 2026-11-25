/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Higher direct images as sheafified cohomology presheaves

Source: Stacks Project, Tag 03Q8 (blueprint: proposition-base-change-larger-algebraically-closed).
The presheaf is written using derived Hom from the free abelian sheaf of an etale
representable. This is the standard representation of restricted hypercohomology:
Hom(Z[U ×_X Y][0], K[q]) = H^q(U ×_X Y, K|). Its restriction maps are precomposition.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/- The following local comparisons adapt the proved module-coefficient argument in
WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomPresheaf
(the sections DerivedSections and CohomologyPresheaf) to free abelian sheaves.
The local lifting argument is Stacks 072W/03Q8; it avoids restricting injectives to
individual etale schemes by working directly with derived Hom and local cycles. -/


namespace AbelianComparison

section LocalComparison

variable {C : Type (u + 1)} [Category.{u} C]
  {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u + 1}]

open Opposite

/-- The free sheaf `ℤ[W]` of abelian groups on an étale `X`-scheme `W`: the sheafification of the
presheaf `V ↦ ℤ^{(Hom_X(V, W))}`. It corepresents sections over `W`, and
`Ext^q(ℤ[W], F)` is the étale cohomology `H^q(W, F|_W)`. -/
noncomputable def freeSheaf (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}] :
    C ⥤ Sheaf J (AddCommGrpCat.{u + 1}) :=
  uliftYoneda.{u + 1} ⋙ (Functor.whiskeringRight _ _ _).obj (AddCommGrpCat.free) ⋙
    presheafToSheaf _ _

/-- Evaluation at the generator: for a sheaf `G` of abelian groups on `X_ét`, the natural map
`Hom(ℤ[W], G) ⟶ G(W)` sending `f` to the image under `f` of the section of `ℤ[W]` given by
the identity of `W`. -/
noncomputable def freeSheafSections
    (G : Sheaf J (AddCommGrpCat.{u + 1})) :
    (freeSheaf J).op ⋙ preadditiveYoneda.obj G ⟶
      G.obj where
  app W := AddCommGrpCat.ofHom
    { toFun f := (f.hom.app W).hom (((toSheafify J
        (uliftYoneda.{u + 1}.obj W.unop ⋙ AddCommGrpCat.free)).app W).hom
          (FreeAbelianGroup.of (ULift.up (𝟙 W.unop))))
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality W W' g := by
    ext f
    have h₁ := congr_arg (fun k ↦ (k.app W').hom (FreeAbelianGroup.of (ULift.up (𝟙 W'.unop))))
      (toSheafify_naturality J
        (Functor.whiskerRight (uliftYoneda.{u + 1}.map g.unop) (AddCommGrpCat.free)))
    have h₂ := congr_arg (fun k ↦ k.hom (FreeAbelianGroup.of (ULift.up (𝟙 W.unop))))
      ((toSheafify J
        (uliftYoneda.{u + 1}.obj W.unop ⋙ AddCommGrpCat.free)).naturality g)
    have h₃ := congr_arg (fun k ↦ k.hom (((toSheafify J
        (uliftYoneda.{u + 1}.obj W.unop ⋙ AddCommGrpCat.free)).app W).hom
          (FreeAbelianGroup.of (ULift.up (𝟙 W.unop))))) (f.hom.naturality g)
    have h₀ : ((AddCommGrpCat.free).map ((uliftYoneda.{u + 1}.map g.unop).app W')).hom
        (FreeAbelianGroup.of (ULift.up (𝟙 W'.unop))) =
        ((AddCommGrpCat.free).map ((uliftYoneda.{u + 1}.obj W.unop).map g)).hom
          (FreeAbelianGroup.of (ULift.up (𝟙 W.unop))) := by
      simp
    dsimp at h₁ h₂ h₃
    exact (congr_arg (f.hom.app W').hom h₁.symm).trans
      ((congr_arg (fun x ↦ (f.hom.app W').hom
        (((toSheafify J
          (uliftYoneda.{u + 1}.obj W.unop ⋙ AddCommGrpCat.free)).app W').hom x)) h₀).trans
        ((congr_arg (f.hom.app W').hom h₂).trans h₃))


/-- The free sheaf `ℤ[W]` corepresents sections over `W`. -/
private noncomputable def freeSheafHomEquiv (W : C)
    (G : Sheaf J (AddCommGrpCat.{u + 1})) :
    ((freeSheaf J).obj W ⟶ G) ≃ G.obj.obj (op W) :=
  ((sheafificationAdjunction _ _).homEquiv _ _).trans <|
    (((AddCommGrpCat.adj).whiskerRight Cᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv

private lemma freeSheafHomEquiv_apply (W : C)
    (G : Sheaf J (AddCommGrpCat.{u + 1}))
    (f : (freeSheaf J).obj W ⟶ G) :
    freeSheafHomEquiv W G f = (freeSheafSections G).app (op W) f := by
  simp [freeSheafHomEquiv, freeSheafSections]
  rfl

private lemma freeSheafHomEquiv_comp (W : C)
    {G G' : Sheaf J (AddCommGrpCat.{u + 1})}
    (f : (freeSheaf J).obj W ⟶ G) (g : G ⟶ G') :
    freeSheafHomEquiv W G' (f ≫ g) =
      g.hom.app (op W) (freeSheafHomEquiv W G f) := by
  simp only [freeSheafHomEquiv_apply, freeSheafSections]
  rfl

private lemma freeSheafHomEquiv_map {W W' : C} (v : W' ⟶ W)
    (G : Sheaf J (AddCommGrpCat.{u + 1}))
    (f : (freeSheaf J).obj W ⟶ G) :
    freeSheafHomEquiv W' G ((freeSheaf J).map v ≫ f) =
      G.obj.map v.op (freeSheafHomEquiv W G f) := by
  simp only [freeSheafHomEquiv_apply]
  exact congrArg (fun k ↦ k f) ((freeSheafSections G).naturality v.op)



variable [HasDerivedCategory.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]

/-- For `L ∈ D⁺(X_ét)`, the map `Hom(ℤ[W][0], L) ⟶ Hom(ℤ[W], H⁰(L))` induced by the degree-`0`
homology, natural in `W`. -/
noncomputable def derivedHomToHomology
    (L : DerivedCategory.Plus (Sheaf J (AddCommGrpCat.{u + 1}))) :
    (freeSheaf J ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj L ⟶
      (freeSheaf J).op ⋙ preadditiveYoneda.obj
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj L) where
  app W := AddCommGrpCat.ofHom <|
    (Preadditive.leftComp _
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _)).comp
      (DerivedCategory.Plus.homologyFunctor _ 0).mapAddHom
  naturality W W' g := by
    have hs := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
      (C := Sheaf J (AddCommGrpCat.{u + 1})) 0).inv.naturality
        ((freeSheaf J).map g.unop)
    dsimp at hs
    ext f
    revert f
    change ∀ f : (DerivedCategory.Plus.singleFunctor _ 0).obj ((freeSheaf J).obj W.unop) ⟶
        L,
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map ((freeSheaf J).map g.unop) ≫ f) =
      (freeSheaf J).map g.unop ≫
        (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
          ((freeSheaf J).obj W.unop) ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map f
    intro f
    rw [Functor.map_comp, ← reassoc_of% hs]

private lemma derivedHomToHomology_app_apply
    (L : DerivedCategory.Plus (Sheaf J (AddCommGrpCat.{u + 1})))
    (W : Cᵒᵖ)
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((freeSheaf J).obj W.unop) ⟶ L) :
    (derivedHomToHomology L).app W β =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map β :=
  rfl

/-- The sections map of a morphism of sheaves of abelian groups, on the underlying presheaves of
abelian groups. -/
private noncomputable abbrev sectionsMap {G G' : Sheaf J AddCommGrpCat.{u + 1}}
    (g : G ⟶ G') : G.obj ⟶ G'.obj := g.hom

omit [HasDerivedCategory.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})] in
private lemma freeSheafSections_naturality
    {G G' : Sheaf J (AddCommGrpCat.{u + 1})} (g : G ⟶ G') :
    freeSheafSections G ≫ sectionsMap g =
      Functor.whiskerLeft (freeSheaf J).op (preadditiveYoneda.map g) ≫
        freeSheafSections G' := by
  ext W f
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← freeSheafHomEquiv_apply, ← freeSheafHomEquiv_apply]
  exact (freeSheafHomEquiv_comp W.unop f g).symm


section Key

variable [J.HasSheafCompose (forget AddCommGrpCat.{u + 1})]

variable (M : CochainComplex.Plus (Sheaf J (AddCommGrpCat.{u + 1})))

/-- The comparison `H⁰(M) ⟶ H⁰(Q M)` between the homology sheaf of a complex and the homology of
its image in `D⁺`. -/
private noncomputable def homologyComparison :
    M.obj.homology 0 ⟶
      (DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M) :=
  (DerivedCategory.homologyFunctorFactors _ 0).inv.app M.obj

private instance homologyComparison_isIso : IsIso (homologyComparison M) := by
  unfold homologyComparison
  infer_instance

omit [J.HasSheafCompose (forget AddCommGrpCat.{u + 1})] in
private lemma derivedHomToHomology_app_eq {W : Cᵒᵖ}
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((freeSheaf J).obj W.unop) ⟶
      DerivedCategory.Plus.Q.obj M)
    (f : (HomologicalComplex.single _ (.up ℤ) 0).obj ((freeSheaf J).obj W.unop) ⟶ M.obj)
    (hf : DerivedCategory.Plus.ι.map β =
      DerivedCategory.Q.map f) :
    (derivedHomToHomology (DerivedCategory.Plus.Q.obj M)).app W β =
      DerivedCategory.singleCyclesHom _ ≫ HomologicalComplex.cyclesMap f 0 ≫
        M.obj.homologyπ 0 ≫ homologyComparison M :=
  DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map
    β f hf

omit [J.HasSheafCompose (forget AddCommGrpCat.{u + 1})] in
private theorem exists_chainMap_of_cycle {A : Sheaf J AddCommGrpCat.{u + 1}}
    (c' : A ⟶ M.obj.cycles 0) :
    ∃ fM : (HomologicalComplex.single _ (.up ℤ) 0).obj A ⟶ M.obj,
      DerivedCategory.singleCyclesHom A ≫ HomologicalComplex.cyclesMap fM 0 = c' := by
  let τ := DerivedCategory.singleCyclesHom A ≫
    (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 A).hom
  let fM : (HomologicalComplex.single _ (.up ℤ) 0).obj A ⟶ M.obj :=
    HomologicalComplex.mkHomFromSingle (inv τ ≫ c' ≫ M.obj.iCycles 0) (by
      intro k _
      simp)
  refine ⟨fM, ?_⟩
  rw [← cancel_mono (M.obj.iCycles 0), Category.assoc, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.mkHomFromSingle_f]
  have hτ : DerivedCategory.singleCyclesHom A ≫
      ((HomologicalComplex.single _ (.up ℤ) 0).obj A).iCycles 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom = τ := by
    simp [τ, HomologicalComplex.singleObjCyclesSelfIso_hom]
  rw [reassoc_of% hτ, IsIso.hom_inv_id_assoc]

private theorem isLocallySurjective_derivedHomToHomology [M.obj.IsKInjective] :
    Presheaf.IsLocallySurjective J
      (derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
        freeSheafSections
          ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))) := by
  have : Sheaf.IsLocallySurjective (M.obj.homologyπ 0) :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
  constructor
  intro W σ
  let σ' : ToType ((M.obj.homology 0).obj.obj (op W)) :=
    (inv (homologyComparison M)).hom.app (op W) σ
  refine GrothendieckTopology.superset_covering _ ?_
    (Presheaf.imageSieve_mem J (M.obj.homologyπ 0).hom σ')
  rintro V g ⟨c, hc⟩
  let A := (freeSheaf J).obj V
  let c' := (freeSheafHomEquiv V (M.obj.cycles 0)).symm c
  obtain ⟨fM, hfM⟩ := exists_chainMap_of_cycle M c'
  obtain ⟨β, hβ⟩ : ∃ β : (DerivedCategory.Plus.singleFunctor _ 0).obj A ⟶
      DerivedCategory.Plus.Q.obj M, DerivedCategory.Plus.ι.map β =
        DerivedCategory.Q.map fM :=
    ⟨DerivedCategory.Plus.ι.preimage _, Functor.map_preimage _ _⟩
  refine ⟨β, ?_⟩
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply,
    derivedHomToHomology_app_eq M (W := op V) β fM hβ, reassoc_of% hfM,
    ← freeSheafHomEquiv_apply, freeSheafHomEquiv_comp, Equiv.apply_symm_apply]
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply,
    hc]
  erw [NatTrans.naturality_apply (homologyComparison M).hom g.op σ']
  have hσ : (homologyComparison M).hom.app (op W) σ' = σ := by
    simp only [σ']
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, IsIso.inv_hom_id]
    rfl
  rw [hσ]

/-- A map from a single complex whose degree-`0` component factors through the differential
`M⁻¹ ⟶ M⁰` is null-homotopic. -/
private noncomputable def homotopyOfSingle {A : Sheaf J (AddCommGrpCat.{u + 1})}
    (f : (HomologicalComplex.single _ (.up ℤ) 0).obj A ⟶ M.obj) (b : A ⟶ M.obj.X (-1))
    (hb : f.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom ≫ b ≫ M.obj.d (-1) 0) :
    Homotopy f 0 :=
  (Homotopy.ofEq (HomologicalComplex.from_single_hom_ext (j := 0) (by
    rw [hb, Homotopy.nullHomotopicMap'_f (k₂ := -1) (k₀ := 1) (by simp) (by simp)]
    simp
    rfl)) :
      Homotopy f (Homotopy.nullHomotopicMap' (fun i j (_ : j + 1 = i) ↦
        if hi : i = 0 then
          (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 A i hi).hom ≫ b ≫
            eqToHom (by congr 1; lia)
        else 0))).trans (Homotopy.nullHomotopy' _)

omit [J.HasSheafCompose (forget AddCommGrpCat.{u + 1})] in
private theorem derivedMap_zero_of_boundary [M.obj.IsKInjective]
    {A A' : Sheaf J AddCommGrpCat.{u + 1}}
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj A ⟶ DerivedCategory.Plus.Q.obj M)
    (f : (HomologicalComplex.single _ (.up ℤ) 0).obj A ⟶ M.obj)
    (hf : DerivedCategory.Plus.ι.map β =
      DerivedCategory.Q.map f)
    (φ : A' ⟶ A) (b : A' ⟶ M.obj.X (-1))
    (hb : ((HomologicalComplex.single _ (.up ℤ) 0).map φ ≫ f).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A').hom ≫ b ≫ M.obj.d (-1) 0) :
    (DerivedCategory.Plus.singleFunctor _ 0).map φ ≫ β = 0 := by
  let f' := (HomologicalComplex.single _ (.up ℤ) 0).map φ ≫ f
  have hβ' : DerivedCategory.Plus.ι.map
      ((DerivedCategory.Plus.singleFunctor _ 0).map φ ≫ β) =
        DerivedCategory.Q.map f' := by
    rw [Functor.map_comp, hf, Functor.map_comp]
    rfl
  exact DerivedCategory.Plus.eq_zero_of_homotopy _ f' hβ'
    (homotopyOfSingle M f' b hb)

private theorem isLocallyInjective_derivedHomToHomology [M.obj.IsKInjective] :
    Presheaf.IsLocallyInjective J
      (derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
        freeSheafSections
          ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))) := by
  constructor
  intro W x y hxy
  let β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((freeSheaf J).obj W.unop) ⟶
      DerivedCategory.Plus.Q.obj M := x - y
  have hβ : (derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
      freeSheafSections
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))).app W β =
      0 := by
    simp only [β, map_sub]
    exact sub_eq_zero.2 hxy
  have hsieve : Presheaf.equalizerSieve x y = Presheaf.equalizerSieve (x - y) 0 := by
    ext V g
    simp only [Presheaf.equalizerSieve_apply, map_sub, map_zero]
    exact sub_eq_zero.symm
  rw [hsieve]
  let A := (freeSheaf J).obj W.unop
  obtain ⟨f, hf⟩ := DerivedCategory.Plus.exists_ι_map_eq M β
  let z := DerivedCategory.singleCyclesHom A ≫ HomologicalComplex.cyclesMap f 0
  have hz : z ≫ M.obj.homologyπ 0 = (0 : A ⟶ M.obj.homology 0) := by
    have hm : IsIso (homologyComparison M) := by
      dsimp only [homologyComparison]
      infer_instance
    have h2 : z ≫ M.obj.homologyπ 0 ≫ homologyComparison M = 0 := by
      apply (freeSheafHomEquiv W.unop
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))).injective
      rw [freeSheafHomEquiv_apply, freeSheafHomEquiv_apply, map_zero]
      have := derivedHomToHomology_app_eq M β f hf
      simp only [z, Category.assoc]
      rw [← this]
      exact hβ
    calc z ≫ M.obj.homologyπ 0 =
        (z ≫ M.obj.homologyπ 0 ≫ homologyComparison M) ≫
          inv (homologyComparison M) := by
          simp only [Category.assoc, IsIso.hom_inv_id]; erw [Category.comp_id]
      _ = 0 := by rw [h2, Limits.zero_comp]
  let S := ShortComplex.mk (M.obj.toCycles (-1) 0) (M.obj.homologyπ 0) (by simp)
  have hS : S.Exact :=
    ShortComplex.exact_of_g_is_cokernel S (M.obj.homologyIsCokernel (-1) 0 (by simp))
  have : Epi S.toCycles := hS.epi_toCycles
  have : Sheaf.IsLocallySurjective S.toCycles :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
  let k' := S.liftCycles z hz
  let k := freeSheafHomEquiv W.unop S.cycles k'
  refine GrothendieckTopology.superset_covering _ ?_
    (Presheaf.imageSieve_mem J S.toCycles.hom k)
  rintro V g ⟨b, hb⟩
  let φ := (freeSheaf J).map g
  let A' := (freeSheaf J).obj V
  let b' := (freeSheafHomEquiv V (M.obj.X (-1))).symm b
  have hφz : φ ≫ z = b' ≫ M.obj.toCycles (-1) 0 := by
    apply (freeSheafHomEquiv V _).injective
    have hz' : z = k' ≫ S.iCycles := (S.liftCycles_i z hz).symm
    rw [hz', freeSheafHomEquiv_map, freeSheafHomEquiv_comp,
      freeSheafHomEquiv_comp, Equiv.apply_symm_apply]
    erw [← NatTrans.naturality_apply S.iCycles.hom g.op k, ← hb,
      ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, S.toCycles_i]
  let f' := (HomologicalComplex.single _ (.up ℤ) 0).map φ ≫ f
  have hf'z : DerivedCategory.singleCyclesHom A' ≫ HomologicalComplex.cyclesMap f' 0 =
      b' ≫ M.obj.toCycles (-1) 0 := by
    rw [HomologicalComplex.cyclesMap_comp, ← Category.assoc,
      DerivedCategory.singleCyclesHom_naturality, Category.assoc]
    exact hφz
  let τ' := DerivedCategory.singleCyclesHom A' ≫
    (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 A').hom
  have hτ' : DerivedCategory.singleCyclesHom A' ≫
      ((HomologicalComplex.single _ (.up ℤ) 0).obj A').iCycles 0 =
        τ' ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A').inv := by
    simp [τ', HomologicalComplex.singleObjCyclesSelfIso_hom]
  have hf'0 : f'.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A').hom ≫
      (inv τ' ≫ b') ≫ M.obj.d (-1) 0 := by
    have h := hf'z =≫ M.obj.iCycles 0
    rw [Category.assoc, HomologicalComplex.cyclesMap_i, Category.assoc,
      HomologicalComplex.toCycles_i, ← Category.assoc, hτ', Category.assoc] at h
    simp only [Category.assoc]
    rw [← h]
    simp
  have h0 := derivedMap_zero_of_boundary M β f hf φ (inv τ' ≫ b') hf'0
  simp only [Presheaf.equalizerSieve_apply, map_zero, map_sub]
  have h0' : (ConcreteCategory.hom (((freeSheaf J ⋙
      DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj (DerivedCategory.Plus.Q.obj M)).map g.op)) (x - y) = 0 := h0
  rw [map_sub] at h0'
  exact h0'

end Key

variable [J.HasSheafCompose (forget AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]

/-- For every `L ∈ D⁺(X_ét)`, the map `W ↦ (Hom(ℤ[W][0], L) ⟶ Γ(W, H⁰(L)))` is locally
injective and locally surjective: classes of maps to `L` are locally determined by the
section of `H⁰(L)` they induce, and every section of `H⁰(L)` locally comes from such a class. -/
private theorem isLocallyBijective_derivedHomToHomology
    (L : DerivedCategory.Plus (Sheaf J (AddCommGrpCat.{u + 1}))) :
    Presheaf.IsLocallyInjective J
        (derivedHomToHomology L ≫
          freeSheafSections ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)) ∧
      Presheaf.IsLocallySurjective J
        (derivedHomToHomology L ≫
          freeSheafSections ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)) := by
  obtain ⟨n, hn⟩ := L.2
  have : L.IsGE n := (L.isGE_ι_obj_iff n).1 hn
  obtain ⟨L', _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso L n
  let M := (InjectiveObject.ι _).mapCochainComplexPlus.obj L'
  have : M.obj.IsKInjective := inferInstanceAs (CochainComplex.IsKInjective
    (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj L'.obj))
  have := isLocallyInjective_derivedHomToHomology M
  have := isLocallySurjective_derivedHomToHomology M
  have hfac : derivedHomToHomology L ≫
      freeSheafSections ((DerivedCategory.Plus.homologyFunctor _ 0).obj L) =
    (Functor.isoWhiskerLeft (freeSheaf J ⋙ DerivedCategory.Plus.singleFunctor _ 0).op
      (preadditiveYoneda.mapIso e.symm)).hom ≫
      (derivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
        freeSheafSections
          ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))) ≫
      ((sheafToPresheaf _ _).mapIso
        ((DerivedCategory.Plus.homologyFunctor _ 0).mapIso e)).hom := by
    simp only [Category.assoc]
    have hnat := freeSheafSections_naturality
      ((DerivedCategory.Plus.homologyFunctor _ 0).map e.hom)
    change _ = _ ≫ _ ≫ freeSheafSections _ ≫
      sectionsMap ((DerivedCategory.Plus.homologyFunctor _ 0).map e.hom)
    rw [hnat]
    ext W β
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
    apply congrArg (fun f : (freeSheaf J).obj W.unop ⟶
        (DerivedCategory.Plus.homologyFunctor _ 0).obj L ↦
      (freeSheafSections ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)).app W f)
    change _ = ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
      (DerivedCategory.Plus.homologyFunctor _ 0).map (β ≫ e.inv)) ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map e.hom
    rw [derivedHomToHomology_app_apply]
    simp
  rw [hfac]
  constructor <;> infer_instance


noncomputable def sheafifyIsoOfLocallyBijective
    {P : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {G : Sheaf J AddCommGrpCat.{u + 1}}
    (φ : P ⟶ G.obj) [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ] :
    (presheafToSheaf J AddCommGrpCat.{u + 1}).obj P ≅ G := by
  let ψ := ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv _ _).symm φ
  have hfac : toSheafify J P ≫ ψ.hom = φ := by
    have he := ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv
      _ _).apply_symm_apply φ
    rw [Adjunction.homEquiv_unit] at he
    exact he
  have : IsIso ψ := by
    refine (Sheaf.isLocallyBijective_iff_isIso ψ).1 ⟨?_, ?_⟩
    · have : Presheaf.IsLocallyInjective J (toSheafify J P ≫ ψ.hom) := by
        rw [hfac]
        infer_instance
      exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
        J (toSheafify J P) ψ.hom
    · have : Presheaf.IsLocallySurjective J (toSheafify J P ≫ ψ.hom) := by
        rw [hfac]
        infer_instance
      exact Presheaf.isLocallySurjective_of_isLocallySurjective J (toSheafify J P) ψ.hom
  exact asIso ψ

omit [HasDerivedCategory.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})] in
lemma toSheafify_comp_sheafifyIsoOfLocallyBijective_hom
    {P : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {G : Sheaf J AddCommGrpCat.{u + 1}}
    (φ : P ⟶ G.obj) [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ] :
    toSheafify J P ≫ (sheafifyIsoOfLocallyBijective φ).hom.hom = φ := by
  have he := ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv
    _ _).apply_symm_apply φ
  rw [Adjunction.homEquiv_unit] at he
  exact he

private theorem nonempty_sheafifyDerivedHomIso
    (L : DerivedCategory.Plus (Sheaf J AddCommGrpCat.{u + 1})) :
    Nonempty ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj
      ((freeSheaf J ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙ preadditiveYoneda.obj L) ≅
        (DerivedCategory.Plus.homologyFunctor _ 0).obj L) := by
  obtain ⟨_, _⟩ := isLocallyBijective_derivedHomToHomology L
  exact ⟨sheafifyIsoOfLocallyBijective (derivedHomToHomology L ≫ freeSheafSections _)⟩

end LocalComparison

noncomputable def adjunctionPresheafIso
    {B D E : Type*} [Category B] [Category.{u + 1} D] [Category.{u + 1} E]
    [Preadditive D] [Preadditive E] (A : B ⥤ D)
    {F : D ⥤ E} {G : E ⥤ D} [F.Additive] (adj : F ⊣ G) (K : E) :
    (A ⋙ F).op ⋙ preadditiveYoneda.obj K ≅ A.op ⋙ preadditiveYoneda.obj (G.obj K) :=
  NatIso.ofComponents (fun W ↦ (adj.homAddEquiv _ _).toAddCommGrpIso)
    (fun g ↦ by
      ext f
      exact adj.homEquiv_naturality_left _ _)

noncomputable def higherDirectImagePresheaf {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (freeSheaf X.smallEtaleTopology ⋙ upperStar AddCommGrpCat.{u + 1} h ⋙
    DerivedCategory.Plus.singleFunctor _ 0).op ⋙ preadditiveYoneda.obj (K⟦q⟧)

/-- The isomorphism `Hom(h^* ℤ[W][0], K[q]) ≅ Hom(ℤ[W][0], Rh_*(K[q]))`, natural in `W`: the
isomorphism `Lh^*(ℤ[W][0]) ≅ (h^* ℤ[W])[0]` and the adjunction `Lh^* ⊣ Rh_*`. -/
noncomputable def higherDirectImagePresheafIso {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (AddCommGrpCat.{u + 1}))) :
    higherDirectImagePresheaf h q K ≅
      (freeSheaf X.smallEtaleTopology ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj (R+((h)_*[AddCommGrpCat.{u + 1}]).obj (K⟦q⟧)) :=
  Functor.isoWhiskerRight (NatIso.op (Functor.isoWhiskerLeft (freeSheaf X.smallEtaleTopology)
    (((h)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0)))
      (preadditiveYoneda.obj (K⟦q⟧)) ≪≫
  adjunctionPresheafIso
    (freeSheaf X.smallEtaleTopology ⋙ DerivedCategory.Plus.singleFunctor _ 0)
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus (K⟦q⟧)

noncomputable def homologyShiftIso
    {D E : Type*} [Category.{u + 1} D] [Category.{u + 1} E] [Abelian D] [Abelian E]
    [HasDerivedCategory.{u + 1} D] [HasDerivedCategory.{u + 1} E]
    (R : DerivedCategory.Plus D ⥤ DerivedCategory.Plus E) [R.CommShift ℤ]
    (q : ℤ) (K : DerivedCategory.Plus D) :
    (DerivedCategory.Plus.homologyFunctor E 0).obj (R.obj (K⟦q⟧)) ≅
      (DerivedCategory.Plus.homologyFunctor E q).obj (R.obj K) :=
  (DerivedCategory.Plus.homologyFunctor E 0).mapIso ((R.commShiftIso q).app K) ≪≫
    ((DerivedCategory.Plus.homologyFunctor E 0).shiftIso q 0 q (add_zero q)).app _

end AbelianComparison


/-- The restricted cohomology presheaf `U ↦ Hom(h^* ℤ[U][0], K[q]) = H^q(U ×_X Y, K)` on `X_ét`,
for `h : Y ⟶ X` and `K ∈ D⁺(Y_ét)`, where `ℤ[U]` is the sheafification of the free presheaf of
abelian groups on the representable presheaf of `U`.
Source: Stacks Project, Tag 03Q8 (blueprint:
proposition-base-change-larger-algebraically-closed). -/
noncomputable abbrev higherDirectImageRawPresheafAbelian {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  AbelianComparison.higherDirectImagePresheaf h q K

/-- The canonical map from the restricted cohomology presheaf to the sections of
`Rᵠh_* K`: a class `Hom(h^* ℤ[U][0], K[q])` is sent, by the adjunction `h^* ⊣ Rh_*`, to a map
`ℤ[U][0] ⟶ Rh_*(K[q])`, whose degree `0` homology `ℤ[U] ⟶ H⁰(Rh_*(K[q])) = Rᵠh_* K` is
evaluated at the generator of `ℤ[U]`.
Source: Stacks Project, Tag 03Q8 (blueprint:
proposition-base-change-larger-algebraically-closed). -/
noncomputable def higherDirectImagePresheafToHomologyAbelian {X Y : Scheme.{u}} (h : Y ⟶ X)
    (q : ℤ) (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    higherDirectImageRawPresheafAbelian h q K ⟶
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj K)).obj :=
  by
  let R := rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h
  letI : R.CommShift ℤ := by
    dsimp only [R, rightDerivedLowerStarPlus]
    infer_instance
  exact (AbelianComparison.higherDirectImagePresheafIso h q K).hom ≫
    (AbelianComparison.derivedHomToHomology (R.obj (K⟦q⟧)) ≫
      AbelianComparison.freeSheafSections _) ≫
    (AbelianComparison.homologyShiftIso R q K).hom.hom

/-- The canonical map `higherDirectImagePresheafToHomologyAbelian` is locally injective and
locally surjective, so that it induces an isomorphism on sheafifications. -/
theorem isLocallyBijective_higherDirectImagePresheafToHomologyAbelian {X Y : Scheme.{u}}
    (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
        (higherDirectImagePresheafToHomologyAbelian h q K) ∧
      Presheaf.IsLocallySurjective X.smallEtaleTopology
        (higherDirectImagePresheafToHomologyAbelian h q K) := by
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    inferInstance
  let R := rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h
  have : R.CommShift ℤ := by
    dsimp only [R, rightDerivedLowerStarPlus]
    infer_instance
  have := (AbelianComparison.isLocallyBijective_derivedHomToHomology (R.obj (K⟦q⟧))).1
  have := (AbelianComparison.isLocallyBijective_derivedHomToHomology (R.obj (K⟦q⟧))).2
  have : IsIso (AbelianComparison.homologyShiftIso R q K).hom.hom :=
    Functor.map_isIso (sheafToPresheaf _ _) (AbelianComparison.homologyShiftIso R q K).hom
  constructor
  · dsimp only [higherDirectImagePresheafToHomologyAbelian]
    infer_instance
  · dsimp only [higherDirectImagePresheafToHomologyAbelian]
    infer_instance

/-- **Higher direct image is the sheafified restricted cohomology presheaf.** For `h : Y ⟶ X`
and `K ∈ D⁺(Y_ét)`, the canonical map `higherDirectImagePresheafToHomologyAbelian` from the
presheaf `U ↦ H^q(U ×_X Y, K)` to `Rᵠh_* K` induces an isomorphism from its sheafification to
`Rᵠh_* K` (`toSheafify_comp_higherDirectImageIsoSheafificationAbelian_hom`).
Source: Stacks Project, Tag 03Q8 (blueprint: proposition-base-change-larger-algebraically-closed).

Proof:
1. Derived adjunction identifies the displayed presheaf with
   U ↦ Hom(ℤ[U][0], Rh_*(K[q])). Exact pullback commutes with the single functor.
2. For a bounded below derived object L, choose a K-injective complex M representing L.
   The map Hom(ℤ[U][0], L) → Γ(U, H⁰(L)) is locally bijective. Every section locally
   lifts through the epimorphism from cycles to homology, giving a chain map from
   ℤ[U][0]. If its homology section vanishes, the corresponding cycle locally lifts
   through the differential from degree -1, giving an explicit null homotopy. Naturality
   transports these assertions from M to L. The local-bijection criterion for
   sheafification therefore identifies the associated sheaf with H⁰(L).
3. Apply this to L = Rh_*(K[q]). Shift compatibility of derived direct image identifies
   H⁰(Rh_*(K[q])) with H^q(Rh_*K). -/
noncomputable def higherDirectImageIsoSheafificationAbelian {X Y : Scheme.{u}} (h : Y ⟶ X)
    (q : ℤ) (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (higherDirectImageRawPresheafAbelian h q K) ≅
      (DerivedCategory.Plus.homologyFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj K) :=
  have := (isLocallyBijective_higherDirectImagePresheafToHomologyAbelian h q K).1
  have := (isLocallyBijective_higherDirectImagePresheafToHomologyAbelian h q K).2
  AbelianComparison.sheafifyIsoOfLocallyBijective
    (higherDirectImagePresheafToHomologyAbelian h q K)

/-- The isomorphism `higherDirectImageIsoSheafificationAbelian` is compatible with the
sheafification unit: composed with `toSheafify`, it is the canonical map
`higherDirectImagePresheafToHomologyAbelian`. -/
theorem toSheafify_comp_higherDirectImageIsoSheafificationAbelian_hom {X Y : Scheme.{u}}
    (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    toSheafify X.smallEtaleTopology (higherDirectImageRawPresheafAbelian h q K) ≫
        (higherDirectImageIsoSheafificationAbelian h q K).hom.hom =
      higherDirectImagePresheafToHomologyAbelian h q K := by
  have := (isLocallyBijective_higherDirectImagePresheafToHomologyAbelian h q K).1
  have := (isLocallyBijective_higherDirectImagePresheafToHomologyAbelian h q K).2
  exact AbelianComparison.toSheafify_comp_sheafifyIsoOfLocallyBijective_hom _

/-- The sheafified restricted cohomology presheaf is isomorphic to `Rᵠh_* K`; the canonical
isomorphism is `higherDirectImageIsoSheafificationAbelian`.
Source: Stacks Project, Tag 03Q8 (blueprint:
proposition-base-change-larger-algebraically-closed). -/
theorem nonempty_higherDirectImage_iso_sheafification_abelian {X Y : Scheme.{u}} (h : Y ⟶ X)
    (q : ℤ) (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    Nonempty
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (((uliftYoneda.{u + 1} ⋙
          (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
          presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          upperStar AddCommGrpCat.{u + 1} h ⋙
          DerivedCategory.Plus.singleFunctor _ 0).op ⋙
            preadditiveYoneda.obj (K⟦q⟧))) ≅
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj K)) := by
  rw [← Functor.assoc
    ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free)
    (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (upperStar AddCommGrpCat.{u + 1} h ⋙ DerivedCategory.Plus.singleFunctor _ 0)]
  rw [← Functor.assoc uliftYoneda.{u + 1}
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free) ⋙
      presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (upperStar AddCommGrpCat.{u + 1} h ⋙ DerivedCategory.Plus.singleFunctor _ 0)]
  exact ⟨higherDirectImageIsoSheafificationAbelian h q K⟩

/-- The case of a sheaf of `nonempty_higherDirectImage_iso_sheafification_abelian`, with the
canonical isomorphism `higherDirectImageIsoSheafificationAbelian h q (F[0])`.
Source: Stacks Project, Tag 03Q8 (blueprint:
proposition-base-change-larger-algebraically-closed). -/
theorem nonempty_higherDirectImage_iso_sheafification_abelian_single
    {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Nonempty
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (((uliftYoneda.{u + 1} ⋙
          (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
          presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          upperStar AddCommGrpCat.{u + 1} h ⋙
          DerivedCategory.Plus.singleFunctor _ 0).op ⋙
            preadditiveYoneda.obj
              (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦q⟧))) ≅
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  exact nonempty_higherDirectImage_iso_sheafification_abelian h q
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F)

end AlgebraicGeometry.Etale
