/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Evaluation at affine weakly contractible pro-etale objects

Source: Stacks Project, Tags 0946 (1), 03DA and 0935 (2)
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
universe u

open CategoryTheory CategoryTheory.Limits Opposite Functor

namespace AlgebraicGeometry.Scheme.ProEt

private instance abelianSheaf_colimits (X : Scheme.{u}) :
    HasColimitsOfSize.{u + 1, u + 1} (Sheaf (topology X) AddCommGrpCat.{u + 1}) := by
  let : IsGrothendieckAbelian.{u + 1}
      (Sheaf (topology X) AddCommGrpCat.{u + 1}) :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology _ X
  exact IsGrothendieckAbelian.hasColimits _

/-- A colimit of module sheaves is the sheafification of the presheaf colimit.
The comparison is the sheafification unit followed by an isomorphism, so is locally
surjective on underlying sections. -/
private theorem colimit_comparison_locally_surjective
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {K : Type (u + 1)} [SmallCategory K]
    (D : K ⥤ Sheaf J AddCommGrpCat.{u + 1}) (c : Limits.Cocone D) (hc : Limits.IsColimit c) :
    Presheaf.IsLocallySurjective J
      (Limits.colimit.desc (D ⋙ sheafToPresheaf J AddCommGrpCat.{u + 1})
        ((sheafToPresheaf J AddCommGrpCat.{u + 1}).mapCocone c)) := by
  let U := sheafToPresheaf J AddCommGrpCat.{u + 1}
  let L := presheafToSheaf J AddCommGrpCat.{u + 1}
  let adj : L ⊣ U := sheafificationAdjunction J AddCommGrpCat.{u + 1}
  let P := Limits.colimit.cocone (D ⋙ U)
  let hP := Limits.colimit.isColimit (D ⋙ U)
  let hQ := Limits.isColimitOfPreserves L hP
  let e : (D ⋙ U) ⋙ L ≅ D := Functor.isoWhiskerLeft D (asIso adj.counit)
  let hcE := (Limits.IsColimit.precomposeHomEquiv e c).symm hc
  let θ := hQ.coconePointUniqueUpToIso hcE
  let k := adj.unit.app P.pt ≫ U.map θ.hom
  have hk (i : K) : P.ι.app i ≫ k = U.map (c.ι.app i) := by
    dsimp only [k]
    have hn := adj.unit.naturality (P.ι.app i)
    change P.ι.app i ≫ adj.unit.app P.pt =
      adj.unit.app (U.obj (D.obj i)) ≫ U.map (L.map (P.ι.app i)) at hn
    rw [← Category.assoc, hn, Category.assoc, ← U.map_comp]
    have hθ := hQ.comp_coconePointUniqueUpToIso_hom hcE i
    change L.map (P.ι.app i) ≫ θ.hom = adj.counit.app (D.obj i) ≫ c.ι.app i at hθ
    rw [hθ, U.map_comp, ← Category.assoc, adj.right_triangle_components]
    exact Category.id_comp _
  have heq : Limits.colimit.desc (D ⋙ U) (U.mapCocone c) = k := by
    apply hP.hom_ext
    intro i
    exact (hP.fac _ i).trans (hk i).symm
  rw [heq]
  have : Presheaf.IsLocallySurjective J
      (adj.unit.app P.pt) := by
    change Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P.pt)
    infer_instance
  infer_instance

/-- Every section of a coproduct over an affine object factors through a finite subcoproduct.
View the coproduct as the filtered colimit of finite subcoproducts. Local representatives
and a finite covering refinement give a common finite support. The projection onto that
support fixes the section locally, hence globally by separatedness. -/
private theorem affine_coproduct_section_finite_support
    (X : Scheme.{u})
    (W : X.ProEt) [IsAffine W.left]
    (K : Type (u + 1)) (H : K → Sheaf (topology X) AddCommGrpCat.{u + 1})
    (s : (∐ H).obj.obj (op W)) :
    ∃ (S : Finset K) (t : (∐ (fun k : S ↦ H k.val)).obj.obj (op W)),
      (Sigma.desc (fun k : S ↦ Sigma.ι H k.val)).hom.app (op W) t = s := by
  classical
  let D := CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor H)
  let c := CoproductsFromFiniteFiltered.finiteSubcoproductsCocone H
  let hc := CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone H
  let F := D ⋙ sheafToPresheaf (topology X) AddCommGrpCat.{u + 1}
  let P := colimit F
  let k : P ⟶ (∐ H).obj := colimit.desc F
    ((sheafToPresheaf (topology X) AddCommGrpCat.{u + 1}).mapCocone c)
  let q := k
  have : Presheaf.IsLocallySurjective (topology X) q :=
    colimit_comparison_locally_surjective D c hc
  obtain ⟨I, hI, V, f, hcover, hf⟩ := finite_cover_refinement X W
    (Presheaf.imageSieve q s) (Presheaf.imageSieve_mem (topology X) q s)
  let := hI
  have hrep (i : I) : ∃ (S : Finset (Discrete K))
      (t : (∐ (fun j : S ↦ H j.val.as)).obj.obj (op (V i))),
      (Sigma.desc (fun j : S ↦ Sigma.ι H j.val.as)).hom.app (op (V i)) t =
        (∐ H).obj.map (f i).op s := by
    obtain ⟨t, ht⟩ := hf i
    let E := (CategoryTheory.evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj
      (op (V i)) ⋙ CategoryTheory.forget _
    have : PreservesColimit F E := by dsimp [E]; infer_instance
    obtain ⟨j, a, ha⟩ := Types.jointly_surjective (F ⋙ E)
      (isColimitOfPreserves E (colimit.isColimit F)) t
    refine ⟨j, a, ?_⟩
    have hk := colimit.ι_desc ((sheafToPresheaf (topology X) AddCommGrpCat.{u + 1}).mapCocone c) j
    have hk' := congrArg (fun g ↦ g.app (op (V i)) a) hk
    change k.app (op (V i)) ((colimit.ι F j).app (op (V i)) a) =
      (c.ι.app j).hom.app (op (V i)) a at hk'
    change (colimit.ι F j).app (op (V i)) a = t at ha
    rw [ha] at hk'
    exact hk'.symm.trans ht
  let : Fintype I := Fintype.ofFinite I
  choose S t ht using hrep
  let S' : Finset K := (Finset.univ.biUnion S).image Discrete.as
  have hS (i : I) (j : S i) : j.val.as ∈ S' := by
    exact Finset.mem_image.mpr ⟨j.val,
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, j.property⟩, rfl⟩
  let inc : (∐ (fun j : S' ↦ H j.val)) ⟶ ∐ H :=
    Sigma.desc (fun j ↦ Sigma.ι H j.val)
  let p : (∐ H) ⟶ ∐ (fun j : S' ↦ H j.val) :=
    Sigma.desc (fun j ↦ if h : j ∈ S' then
      Sigma.ι (fun j : S' ↦ H j.val) ⟨j, h⟩ else 0)
  refine ⟨S', p.hom.app (op W) s, ?_⟩
  let G : Sheaf (topology X) (Type (u + 1)) :=
    (sheafCompose (topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
      (∐ H)
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp G.property).isSheafFor _ hcover).isSeparatedFor.ext
  intro Z g hg
  obtain ⟨i⟩ := hg
  change (∐ H).obj.map (f i).op
    (inc.hom.app (op W) (p.hom.app (op W) s)) = (∐ H).obj.map (f i).op s
  rw [← NatTrans.naturality_apply inc.hom,
    ← NatTrans.naturality_apply p.hom, ← ht i]
  let inci : (∐ (fun j : S i ↦ H j.val.as)) ⟶ ∐ H :=
    Sigma.desc (fun j ↦ Sigma.ι H j.val.as)
  have he : inci ≫ p ≫ inc = inci := by
    apply Sigma.hom_ext
    intro j
    simp [inci, p, inc, hS i j]
  exact congrArg (fun e ↦ e.hom.app (op (V i)) (t i)) he

/-- The coproduct comparison is bijective: finite-support sections lift through a finite
comparison isomorphism. A kernel element likewise comes from a finite subcoproduct,
whose split inclusion and invertible comparison force the element to vanish. -/
private theorem affine_evaluation_coproduct_isIso
    (X : Scheme.{u})
    (W : X.ProEt) [IsAffine W.left]
    (K : Type (u + 1)) (H : K → Sheaf (topology X) AddCommGrpCat.{u + 1}) :
    IsIso (sigmaComparison ((sheafSections (topology X) AddCommGrpCat.{u + 1}).obj (op W)) H) := by
  classical
  let ev := (sheafSections (topology X) AddCommGrpCat.{u + 1}).obj (op W)
  have : ev.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteCoproducts ev := by infer_instance
  let E := fun i ↦ ev.obj (H i)
  let q := sigmaComparison ev H
  have hfinite (S : Finset K) : IsIso (sigmaComparison ev (fun i : S ↦ H i.val)) := by
    infer_instance
  have hcomp (S : Finset K) :
      Sigma.desc (fun i : S ↦ Sigma.ι E i.val) ≫ q =
        sigmaComparison ev (fun i : S ↦ H i.val) ≫
          ev.map (Sigma.desc (fun i : S ↦ Sigma.ι H i.val)) := by
    apply Sigma.hom_ext
    intro i
    simp [q, E]
  apply (ConcreteCategory.isIso_iff_bijective q).mpr
  refine ⟨?_, ?_⟩
  · apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    let D := CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor E)
    have hc := isColimitOfPreserves (CategoryTheory.forget _)
      (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone E)
    obtain ⟨S, t, ht⟩ := Types.jointly_surjective
      (D ⋙ CategoryTheory.forget _) hc z
    change (Sigma.desc (fun i : S ↦ Sigma.ι E i.val.as)) t = z at ht
    let H' := fun i : S ↦ H i.val.as
    let inc : (∐ H') ⟶ ∐ H := Sigma.desc (fun i ↦ Sigma.ι H i.val.as)
    let p : (∐ H) ⟶ ∐ H' := Sigma.desc (fun i ↦ if h : Discrete.mk i ∈ S then
      Sigma.ι H' ⟨⟨i⟩, h⟩ else 0)
    have hp : inc ≫ p = 𝟙 _ := by
      apply Sigma.hom_ext
      intro i
      simp [inc, p, H', i.property]
    have hq : sigmaComparison ev H' ≫ ev.map inc ≫ ev.map p =
        sigmaComparison ev H' := by rw [← ev.map_comp, hp, ev.map_id, Category.comp_id]
    have he : (ev.map inc) ((sigmaComparison ev H') t) = 0 := by
      have hh : Sigma.desc (fun i : S ↦ Sigma.ι E i.val.as) ≫ q =
          sigmaComparison ev H' ≫ ev.map inc := by
        apply Sigma.hom_ext
        intro i
        simp [inc, H', q, E]
      rw [← ConcreteCategory.comp_apply, ← hh, ConcreteCategory.comp_apply, ht]
      exact hz
    have hzero : (sigmaComparison ev H') t = 0 := by
      have hh := congrArg (ev.map p) he
      simpa only [← ConcreteCategory.comp_apply, Category.assoc, hq, map_zero] using hh
    have htzero : t = 0 := (AddCommGrpCat.mono_iff_injective (sigmaComparison ev H')).mp
      (by infer_instance) (hzero.trans (map_zero _).symm)
    rw [← ht, htzero, map_zero]
  · intro s
    obtain ⟨S, t, ht⟩ := affine_coproduct_section_finite_support X W K H s
    have : IsIso (sigmaComparison ev (fun i : S ↦ H i.val)) := hfinite S
    let a := inv (sigmaComparison ev (fun i : S ↦ H i.val)) t
    refine ⟨(Sigma.desc (fun i : S ↦ Sigma.ι E i.val)) a, ?_⟩
    rw [← ConcreteCategory.comp_apply, hcomp S, ConcreteCategory.comp_apply]
    dsimp only [a]
    rw [IsIso.inv_hom_id_apply]
    exact ht

/-- Evaluation on an affine pro-etale object preserves coproducts of section-universe size. -/
private theorem affine_evaluation_preserves_coproducts
    (X : Scheme.{u})
    (W : X.ProEt) [IsAffine W.left] (K : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete K)
      ((sheafSections (topology X) AddCommGrpCat.{u + 1}).obj (op W)) := by
  let ev := (sheafSections (topology X) AddCommGrpCat.{u + 1}).obj (op W)
  have (H : K → Sheaf (topology X) AddCommGrpCat.{u + 1}) :
      PreservesColimit (Discrete.functor H) ev := by
    have : IsIso (sigmaComparison ev H) := affine_evaluation_coproduct_isIso X W K H
    exact PreservesCoproduct.of_iso_comparison ev H
  exact preservesColimitsOfShape_of_discrete ev

/-- Abelian evaluation at an affine weakly contractible object is exact and
preserves small colimits.
Source: Stacks Project, Tags 0946(1), 0935(2), and 002F.
(auxiliary; not a blueprint node).
Proof: kernels are sectionwise. Epimorphisms become surjective by weak contractibility.
For coproducts, finite covering refinement bounds the supports of local representatives;
a split projection and separatedness give a finite support globally. Additivity handles
finite coproducts. Their comparisons are therefore bijective, and the presentation by
coproducts and coequalizers gives all small colimits, including the empty colimit. -/
theorem affine_weaklyContractible_abelian_evaluation_colimits
    (X : Scheme.{u}) (W : X.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op W))) :
    let ev := (sheafSections (topology X) AddCommGrpCat.{u + 1}).obj (op W)
    ev.PreservesHomology ∧ PreservesColimitsOfSize.{u + 1, u + 1} ev := by
  let ev := (sheafSections (topology X) AddCommGrpCat.{u + 1}).obj (op W)
  have : ev.Additive := ⟨by intros; rfl⟩
  have : ev.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    have : Sheaf.IsLocallySurjective f :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} f).mpr hf
    let g := (sheafCompose (topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})).map f
    have : Epi g := inferInstance
    exact (AddCommGrpCat.epi_iff_surjective (ev.map f)).mpr (hW _ _ g inferInstance)
  have : HasLimitsOfSize.{u, u + 1} AddCommGrpCat.{u + 1} :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  have : PreservesFiniteLimits ev := by
    change PreservesFiniteLimits
      (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op W))
    infer_instance
  have hex : ev.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels ev
  let : ev.PreservesHomology := hex
  have : PreservesFiniteColimits ev :=
    Functor.preservesFiniteColimits_of_preservesHomology ev
  have (K : Type (u + 1)) : PreservesColimitsOfShape (Discrete K) ev :=
    affine_evaluation_preserves_coproducts X W K
  exact ⟨hex, preservesColimits_of_preservesCoequalizers_and_coproducts ev⟩

end AlgebraicGeometry.Scheme.ProEt
