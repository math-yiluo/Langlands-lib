/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictLocalCohomologyGerms
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Canonical derived sections and strict-local cohomology germs

Source: Stacks Project, Tags 03Q8 and 03Q9. The derived Hom comparison is the
explicit free-abelian-sheaf construction used in AbelianHigherDirectImagePresheaf.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

namespace GermComparison

section LocalComparison

variable {C : Type (v + 1)} [Category.{v} C]
  {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{v + 1}]

/-- The free sheaf `ℤ[W]` corepresents sections over `W`. -/
private noncomputable def freeSheafHomEquiv (W : C)
    (G : Sheaf J (AddCommGrpCat.{v + 1})) :
    ((strictLocalFreeSheaf J).obj W ⟶ G) ≃ G.obj.obj (op W) :=
  ((sheafificationAdjunction _ _).homEquiv _ _).trans <|
    (((AddCommGrpCat.adj).whiskerRight Cᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv

private lemma freeSheafHomEquiv_apply (W : C)
    (G : Sheaf J (AddCommGrpCat.{v + 1}))
    (f : (strictLocalFreeSheaf J).obj W ⟶ G) :
    freeSheafHomEquiv W G f = (strictLocalFreeSheafSections G).app (op W) f := by
  simp [freeSheafHomEquiv, strictLocalFreeSheafSections]
  rfl

private lemma freeSheafHomEquiv_comp (W : C)
    {G G' : Sheaf J (AddCommGrpCat.{v + 1})}
    (f : (strictLocalFreeSheaf J).obj W ⟶ G) (g : G ⟶ G') :
    freeSheafHomEquiv W G' (f ≫ g) =
      g.hom.app (op W) (freeSheafHomEquiv W G f) := by
  simp only [freeSheafHomEquiv_apply, strictLocalFreeSheafSections]
  rfl

private lemma freeSheafHomEquiv_map {W W' : C} (v : W' ⟶ W)
    (G : Sheaf J (AddCommGrpCat.{v + 1}))
    (f : (strictLocalFreeSheaf J).obj W ⟶ G) :
    freeSheafHomEquiv W' G ((strictLocalFreeSheaf J).map v ≫ f) =
      G.obj.map v.op (freeSheafHomEquiv W G f) := by
  simp only [freeSheafHomEquiv_apply]
  exact congrArg (fun k ↦ k f) ((strictLocalFreeSheafSections G).naturality v.op)



variable [HasDerivedCategory.{v + 1} (Sheaf J AddCommGrpCat.{v + 1})]

private lemma derivedHomToHomology_app_apply
    (L : DerivedCategory.Plus (Sheaf J (AddCommGrpCat.{v + 1})))
    (W : Cᵒᵖ)
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((strictLocalFreeSheaf J).obj W.unop) ⟶ L) :
    (strictLocalDerivedHomToHomology L).app W β =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map β :=
  rfl

/-- The sections map of a morphism of sheaves of abelian groups, on the underlying presheaves of
abelian groups. -/
private noncomputable abbrev sectionsMap {G G' : Sheaf J AddCommGrpCat.{v + 1}}
    (g : G ⟶ G') : G.obj ⟶ G'.obj := g.hom

omit [HasDerivedCategory.{v + 1} (Sheaf J AddCommGrpCat.{v + 1})] in
private lemma freeSheafSections_naturality
    {G G' : Sheaf J (AddCommGrpCat.{v + 1})} (g : G ⟶ G') :
    strictLocalFreeSheafSections G ≫ sectionsMap g =
      Functor.whiskerLeft (strictLocalFreeSheaf J).op (preadditiveYoneda.map g) ≫
        strictLocalFreeSheafSections G' := by
  ext W f
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← freeSheafHomEquiv_apply, ← freeSheafHomEquiv_apply]
  exact (freeSheafHomEquiv_comp W.unop f g).symm


section Key

variable [J.HasSheafCompose (forget AddCommGrpCat.{v + 1})]

variable (M : CochainComplex.Plus (Sheaf J (AddCommGrpCat.{v + 1})))

/-- The comparison `H⁰(M) ⟶ H⁰(Q M)` between the homology sheaf of a complex and the homology of
its image in `D⁺`. -/
private noncomputable def homologyComparison :
    M.obj.homology 0 ⟶
      (DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M) :=
  (DerivedCategory.homologyFunctorFactors _ 0).inv.app M.obj

private instance homologyComparison_isIso : IsIso (homologyComparison M) := by
  unfold homologyComparison
  infer_instance

omit [J.HasSheafCompose (forget AddCommGrpCat.{v + 1})] in
private lemma derivedHomToHomology_app_eq {W : Cᵒᵖ}
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((strictLocalFreeSheaf J).obj W.unop) ⟶
      DerivedCategory.Plus.Q.obj M)
    (f : (HomologicalComplex.single _ (.up ℤ) 0).obj ((strictLocalFreeSheaf J).obj W.unop) ⟶ M.obj)
    (hf : DerivedCategory.Plus.ι.map β =
      DerivedCategory.Q.map f ≫ (DerivedCategory.quotientCompQhIso _).inv.app M.obj) :
    (strictLocalDerivedHomToHomology (DerivedCategory.Plus.Q.obj M)).app W β =
      DerivedCategory.singleCyclesHom _ ≫ HomologicalComplex.cyclesMap f 0 ≫
        M.obj.homologyπ 0 ≫ homologyComparison M := by
  change _ = _ ≫ 𝟙 _ at hf
  rw [Category.comp_id] at hf
  exact DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso_inv_app_comp_homologyFunctor_map
    β f hf

omit [J.HasSheafCompose (forget AddCommGrpCat.{v + 1})] in
private theorem exists_chainMap_of_cycle {A : Sheaf J AddCommGrpCat.{v + 1}}
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
      (strictLocalDerivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
        strictLocalFreeSheafSections
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
  let A := (strictLocalFreeSheaf J).obj V
  let c' := (freeSheafHomEquiv V (M.obj.cycles 0)).symm c
  obtain ⟨fM, hfM⟩ := exists_chainMap_of_cycle M c'
  obtain ⟨β, hβ⟩ : ∃ β : (DerivedCategory.Plus.singleFunctor _ 0).obj A ⟶
      DerivedCategory.Plus.Q.obj M, DerivedCategory.Plus.ι.map β =
        DerivedCategory.Q.map fM :=
    ⟨DerivedCategory.Plus.ι.preimage _, Functor.map_preimage _ _⟩
  refine ⟨β, ?_⟩
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply,
    derivedHomToHomology_app_eq M (W := op V) β fM
      (by change _ = _ ≫ 𝟙 _; simpa using hβ), reassoc_of% hfM,
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
private noncomputable def homotopyOfSingle {A : Sheaf J (AddCommGrpCat.{v + 1})}
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

omit [J.HasSheafCompose (forget AddCommGrpCat.{v + 1})] in
private theorem derivedMap_zero_of_boundary [M.obj.IsKInjective]
    {A A' : Sheaf J AddCommGrpCat.{v + 1}}
    (β : (DerivedCategory.Plus.singleFunctor _ 0).obj A ⟶ DerivedCategory.Plus.Q.obj M)
    (f : (HomologicalComplex.single _ (.up ℤ) 0).obj A ⟶ M.obj)
    (hf : DerivedCategory.Plus.ι.map β =
      DerivedCategory.Q.map f ≫ (DerivedCategory.quotientCompQhIso _).inv.app M.obj)
    (φ : A' ⟶ A) (b : A' ⟶ M.obj.X (-1))
    (hb : ((HomologicalComplex.single _ (.up ℤ) 0).map φ ≫ f).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A').hom ≫ b ≫ M.obj.d (-1) 0) :
    (DerivedCategory.Plus.singleFunctor _ 0).map φ ≫ β = 0 := by
  change _ = _ ≫ 𝟙 _ at hf
  rw [Category.comp_id] at hf
  let f' := (HomologicalComplex.single _ (.up ℤ) 0).map φ ≫ f
  have hβ' : DerivedCategory.Plus.ι.map
      ((DerivedCategory.Plus.singleFunctor _ 0).map φ ≫ β) =
        DerivedCategory.Q.map f' := by
    simp only [f', Functor.map_comp, hf]
    rfl
  exact DerivedCategory.Plus.eq_zero_of_homotopy _ f' hβ'
    (homotopyOfSingle M f' b hb)

private theorem isLocallyInjective_derivedHomToHomology [M.obj.IsKInjective] :
    Presheaf.IsLocallyInjective J
      (strictLocalDerivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
        strictLocalFreeSheafSections
          ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))) := by
  constructor
  intro W x y hxy
  let β : (DerivedCategory.Plus.singleFunctor _ 0).obj ((strictLocalFreeSheaf J).obj W.unop) ⟶
      DerivedCategory.Plus.Q.obj M := x - y
  have hβ : (strictLocalDerivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
      strictLocalFreeSheafSections
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))).app W β =
      0 := by
    simp only [β, map_sub]
    exact sub_eq_zero.2 hxy
  have hsieve : Presheaf.equalizerSieve x y = Presheaf.equalizerSieve (x - y) 0 := by
    ext V g
    simp only [Presheaf.equalizerSieve_apply, map_sub, map_zero]
    exact sub_eq_zero.symm
  rw [hsieve]
  let A := (strictLocalFreeSheaf J).obj W.unop
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
      have := derivedHomToHomology_app_eq M β f
        (by change _ = _ ≫ 𝟙 _; simpa using hf)
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
  let φ := (strictLocalFreeSheaf J).map g
  let A' := (strictLocalFreeSheaf J).obj V
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
  have h0 := derivedMap_zero_of_boundary M β f
    (by change _ = _ ≫ 𝟙 _; simpa using hf) φ (inv τ' ≫ b') hf'0
  simp only [Presheaf.equalizerSieve_apply, map_zero, map_sub]
  have h0' : (ConcreteCategory.hom (((strictLocalFreeSheaf J ⋙
      DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj (DerivedCategory.Plus.Q.obj M)).map g.op)) (x - y) = 0 := h0
  rw [map_sub] at h0'
  exact h0'

end Key

variable [J.HasSheafCompose (forget AddCommGrpCat.{v + 1})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{v + 1})]

/-- For every `L ∈ D⁺(X_ét)`, the map `W ↦ (Hom(ℤ[W][0], L) ⟶ Γ(W, H⁰(L)))` is locally
injective and locally surjective: classes of maps to `L` are locally determined by the
section of `H⁰(L)` they induce, and every section of `H⁰(L)` locally comes from such a class. -/
private theorem isLocallyBijective_derivedHomToHomology
    (L : DerivedCategory.Plus (Sheaf J (AddCommGrpCat.{v + 1}))) :
    Presheaf.IsLocallyInjective J
        (strictLocalDerivedHomToHomology L ≫
          strictLocalFreeSheafSections ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)) ∧
      Presheaf.IsLocallySurjective J
        (strictLocalDerivedHomToHomology L ≫
          strictLocalFreeSheafSections ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)) := by
  obtain ⟨n, hn⟩ := L.2
  have : L.IsGE n := (L.isGE_ι_obj_iff n).1 hn
  obtain ⟨L', _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso L n
  let M := (InjectiveObject.ι _).mapCochainComplexPlus.obj L'
  have : M.obj.IsKInjective := inferInstanceAs (CochainComplex.IsKInjective
    (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj L'.obj))
  have := isLocallyInjective_derivedHomToHomology M
  have := isLocallySurjective_derivedHomToHomology M
  have hfac : strictLocalDerivedHomToHomology L ≫
      strictLocalFreeSheafSections ((DerivedCategory.Plus.homologyFunctor _ 0).obj L) =
    (Functor.isoWhiskerLeft (strictLocalFreeSheaf J ⋙ DerivedCategory.Plus.singleFunctor _ 0).op
      (preadditiveYoneda.mapIso e.symm)).hom ≫
      (strictLocalDerivedHomToHomology (DerivedCategory.Plus.Q.obj M) ≫
        strictLocalFreeSheafSections
          ((DerivedCategory.Plus.homologyFunctor _ 0).obj (DerivedCategory.Plus.Q.obj M))) ≫
      ((sheafToPresheaf _ _).mapIso
        ((DerivedCategory.Plus.homologyFunctor _ 0).mapIso e)).hom := by
    simp only [Category.assoc]
    have hnat := freeSheafSections_naturality
      ((DerivedCategory.Plus.homologyFunctor _ 0).map e.hom)
    change _ = _ ≫ _ ≫ strictLocalFreeSheafSections _ ≫
      sectionsMap ((DerivedCategory.Plus.homologyFunctor _ 0).map e.hom)
    rw [hnat]
    ext W β
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
    apply congrArg (fun f : (strictLocalFreeSheaf J).obj W.unop ⟶
        (DerivedCategory.Plus.homologyFunctor _ 0).obj L ↦
      (strictLocalFreeSheafSections ((DerivedCategory.Plus.homologyFunctor _ 0).obj L)).app W f)
    change _ = ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
      (DerivedCategory.Plus.homologyFunctor _ 0).map (β ≫ e.inv)) ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map e.hom
    rw [derivedHomToHomology_app_apply]
    simp
  rw [hfac]
  constructor <;> infer_instance


end LocalComparison

end GermComparison

/-- The canonical derived-sections comparison induces an isomorphism on geometric stalks.
This is only the local sheafification assertion, with no strict-local limit or base-change mate.
Source: Stacks, Tag 03Q8 and Cohomology on Sites, Tag 0BKV
(blueprint: lem-weil-pbc-derived-cohomology-germ-isomorphism).

Proof: represent L[n] by a bounded below K-injective complex M. The derived Hom from
Z[U][0] is represented by cycles in M(U), modulo boundaries. The displayed map sends
such a cycle to its homology section. Locally, every homology section lifts to a cycle,
because cycles surject onto the homology sheaf. If the homology section of a cycle
vanishes, locally the cycle lifts through the differential from degree -1; the lift is
a null homotopy of the map from Z[U][0]. Hence the comparison is locally bijective.
Sheafification makes it an isomorphism, and geometric stalks are unchanged by
sheafification. Finally the homology shift isomorphism transports H^0(L[n]) to H^n(L).
The cycle and boundary argument applies for every integer n and also for L = 0. -/
theorem isIso_strictLocalCohomologyGermMap {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    IsIso ((Scheme.pointSmallEtale s).presheafFiber.map
      (strictLocalCohomologyGermMap L n)) := by
  obtain ⟨hi, hs⟩ := GermComparison.isLocallyBijective_derivedHomToHomology (L⟦n⟧)
  have := hi
  have := hs
  have : Presheaf.IsLocallyInjective S.smallEtaleTopology
      (strictLocalCohomologyGermMap L n) := by
    unfold strictLocalCohomologyGermMap
    rw [← Category.assoc]
    infer_instance
  have : Presheaf.IsLocallySurjective S.smallEtaleTopology
      (strictLocalCohomologyGermMap L n) := by
    unfold strictLocalCohomologyGermMap
    rw [← Category.assoc]
    infer_instance
  exact (Scheme.pointSmallEtale s).W_isInvertedBy_presheafFiber _
    ((S.smallEtaleTopology.W_iff_isLocallyBijective _).2 ⟨inferInstance, inferInstance⟩)

end AlgebraicGeometry.Etale
