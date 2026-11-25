/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses

/-!
# Sections over weakly contractible affine pro-étale objects

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-cor-pe-sections/det-pe-sections-limits-colimits.md
(blueprint: det-pe-sections-limits-colimits).
-/

@[expose] public section

universe u r v wJ uJ

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace CategoryTheory

/-- The site is small in every common module universe containing its objects and arrows.
Source: the fixed size convention, realized by Mathlib's small-category transport.
(blueprint: det-pe-sections-limits-colimits). -/
private local instance pe_essentiallySmall (X : Scheme.{u})
    [UnivLE.{u + 1, v}] : EssentiallySmall.{v} X.ProEt := by
  have : Small.{v} X.ProEt := inferInstance
  have : UnivLE.{u, v} := UnivLE.trans.{u, u + 1, v}
  have : LocallySmall.{v} X.ProEt := ⟨fun _ _ ↦ inferInstance⟩
  infer_instance

/-- A colimit of module sheaves is the sheafification of the presheaf colimit.
The comparison is the sheafification unit followed by an isomorphism, so is locally
surjective on underlying sections.
Source: Stacks Project, Tag 03DB, module-colimit construction and Tag 03CY.
(blueprint: det-pe-sections-limits-colimits). -/
private theorem colimit_comparison_locally_surjective
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) [HasSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    {K : Type v} [SmallCategory K]
    (D : K ⥤ SheafOfModules.{v} R) (c : Limits.Cocone D) (hc : Limits.IsColimit c) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map
        (Limits.colimit.desc (D ⋙ SheafOfModules.forget R)
          ((SheafOfModules.forget R).mapCocone c))) := by
  let U := SheafOfModules.forget R
  let L := PresheafOfModules.sheafification (𝟙 R.obj)
  let adj : L ⊣ U := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
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
  rw [heq, Functor.map_comp]
  have : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (adj.unit.app P.pt)) := by
    change Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P.pt.presheaf)
    infer_instance
  infer_instance

/-- Every section of a coproduct over an affine object factors through a finite subcoproduct.
View the coproduct as the filtered colimit of finite subcoproducts. Local representatives
and a finite covering refinement give a common finite support. The projection onto that
support fixes the section locally, hence globally by separatedness.
Source: Stacks Project, Tag 0935 (2); the finite-support paragraph of the blueprint proof.
(blueprint: det-pe-sections-limits-colimits). -/
private theorem pe_coproduct_section_finite_support
    (X : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology X) RingCat.{r})
    (W : X.ProEt) [IsAffine W.left]
    (K : Type (max (u + 1) r v)) (H : K → SheafOfModules.{max (u + 1) r v} R)
    (s : (∐ H).val.obj (op W)) :
    ∃ (S : Finset K) (t : (∐ (fun k : S ↦ H k.val)).val.obj (op W)),
      (Sigma.desc (fun k : S ↦ Sigma.ι H k.val)).val.app (op W) t = s := by
  classical
  let D := CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor H)
  let c := CoproductsFromFiniteFiltered.finiteSubcoproductsCocone H
  let hc := CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone H
  let F := D ⋙ SheafOfModules.forget R
  let P := colimit F
  let k : P ⟶ (∐ H).val := colimit.desc F ((SheafOfModules.forget R).mapCocone c)
  let q := (PresheafOfModules.toPresheaf R.obj).map k
  have : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) q :=
    colimit_comparison_locally_surjective R D c hc
  obtain ⟨I, hI, V, f, hcover, hf⟩ := Scheme.ProEt.finite_cover_refinement X W
    (Presheaf.imageSieve q s) (Presheaf.imageSieve_mem (Scheme.ProEt.topology X) q s)
  let := hI
  have hrep (i : I) : ∃ (S : Finset (Discrete K))
      (t : (∐ (fun j : S ↦ H j.val.as)).val.obj (op (V i))),
      (Sigma.desc (fun j : S ↦ Sigma.ι H j.val.as)).val.app (op (V i)) t =
        (∐ H).val.map (f i).op s := by
    obtain ⟨t, ht⟩ := hf i
    let E := PresheafOfModules.evaluation.{max (u + 1) r v} R.obj (op (V i)) ⋙
      forget₂ _ AddCommGrpCat.{max (u + 1) r v} ⋙ CategoryTheory.forget _
    have : PreservesColimit F E := by dsimp [E]; infer_instance
    obtain ⟨j, a, ha⟩ := Types.jointly_surjective (F ⋙ E)
      (isColimitOfPreserves E (colimit.isColimit F)) t
    refine ⟨j, a, ?_⟩
    have hk := colimit.ι_desc ((SheafOfModules.forget R).mapCocone c) j
    have hk' := congrArg (fun g ↦ g.app (op (V i)) a) hk
    change k.app (op (V i)) ((colimit.ι F j).app (op (V i)) a) =
      (c.ι.app j).val.app (op (V i)) a at hk'
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
  refine ⟨S', p.val.app (op W) s, ?_⟩
  let G : Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) r v)) :=
    (sheafCompose (Scheme.ProEt.topology X)
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) r v})).obj
      ((SheafOfModules.toSheaf R).obj (∐ H))
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp G.property).isSheafFor _ hcover).isSeparatedFor.ext
  intro Z g hg
  obtain ⟨i⟩ := hg
  change (∐ H).val.map (f i).op
    (inc.val.app (op W) (p.val.app (op W) s)) = (∐ H).val.map (f i).op s
  rw [← PresheafOfModules.naturality_apply inc.val,
    ← PresheafOfModules.naturality_apply p.val, ← ht i]
  let inci : (∐ (fun j : S i ↦ H j.val.as)) ⟶ ∐ H :=
    Sigma.desc (fun j ↦ Sigma.ι H j.val.as)
  have he : inci ≫ p ≫ inc = inci := by
    apply Sigma.hom_ext
    intro j
    simp [inci, p, inc, hS i j]
  exact congrArg (fun e ↦ e.val.app (op (V i)) (t i)) he

/-- The coproduct comparison is bijective: finite-support sections lift through a finite
comparison isomorphism. A kernel element likewise comes from a finite subcoproduct,
whose split inclusion and invertible comparison force the element to vanish.
Source: the direct-sum injectivity and surjectivity paragraphs of the blueprint proof.
(blueprint: det-pe-sections-limits-colimits). -/
private theorem pe_evaluation_coproduct_isIso
    (X : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology X) RingCat.{r})
    (W : X.ProEt) [IsAffine W.left]
    (K : Type (max (u + 1) r v)) (H : K → SheafOfModules.{max (u + 1) r v} R) :
    IsIso (sigmaComparison (SheafOfModules.evaluation.{max (u + 1) r v} R (op W)) H) := by
  classical
  let ev := SheafOfModules.evaluation.{max (u + 1) r v} R (op W)
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
  · apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro z hz
    let D := CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor E)
    have hc := isColimitOfPreserves
      (forget₂ (ModuleCat.{max (u + 1) r v} _) AddCommGrpCat ⋙ CategoryTheory.forget _)
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
      rw [← ModuleCat.comp_apply, ← hh, ModuleCat.comp_apply, ht]
      exact hz
    have hzero : (sigmaComparison ev H') t = 0 := by
      have hh := congrArg (ev.map p) he
      simpa only [← ModuleCat.comp_apply, Category.assoc, hq, map_zero] using hh
    have htzero : t = 0 := (ModuleCat.mono_iff_injective (sigmaComparison ev H')).mp
      (by infer_instance) (hzero.trans (map_zero _).symm)
    rw [← ht, htzero, map_zero]
  · intro s
    obtain ⟨S, t, ht⟩ := pe_coproduct_section_finite_support X R W K H s
    have : IsIso (sigmaComparison ev (fun i : S ↦ H i.val)) := hfinite S
    let a := inv (sigmaComparison ev (fun i : S ↦ H i.val)) t
    refine ⟨(Sigma.desc (fun i : S ↦ Sigma.ι E i.val)) a, ?_⟩
    rw [← ModuleCat.comp_apply, hcomp S, ModuleCat.comp_apply]
    dsimp only [a]
    rw [IsIso.inv_hom_id_apply]
    exact ht

/-- Evaluation on an affine pro-etale object preserves coproducts of section-universe size.
Source: Stacks Project, Tag 0935 (2), and the blueprint direct-sum argument above.
(blueprint: det-pe-sections-limits-colimits). -/
private theorem pe_evaluation_preserves_coproducts
    (X : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology X) RingCat.{r})
    (W : X.ProEt) [IsAffine W.left] (K : Type (max (u + 1) r v)) :
    PreservesColimitsOfShape (Discrete K)
      (SheafOfModules.evaluation.{max (u + 1) r v} R (op W)) := by
  let ev := SheafOfModules.evaluation.{max (u + 1) r v} R (op W)
  have (H : K → SheafOfModules.{max (u + 1) r v} R) : PreservesColimit (Discrete.functor H) ev := by
    have : IsIso (sigmaComparison ev H) := pe_evaluation_coproduct_isIso X R W K H
    exact PreservesCoproduct.of_iso_comparison ev H
  exact preservesColimitsOfShape_of_discrete ev

/--
Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-cor-pe-sections/det-pe-sections-limits-colimits.proof.md
(blueprint: corollary-evaluation-weakly-contractible-objects).

First compute limits sectionwise in the common module universe. For coproducts, write
the sum as the filtered colimit of its finite subsums. The comparison from the presheaf
colimit to the sheaf colimit is the sheafification unit followed by an isomorphism.
Local representatives and the finite covering refinement of the affine W give a common
finite support. Projection onto that support fixes the section locally, hence globally
by separatedness. This proves surjectivity of the coproduct comparison. For injectivity,
represent a kernel element in a finite subsum and apply its split retraction together
with the finite comparison isomorphism. The argument includes the empty sum.

For exactness, the functor to abelian sheaves preserves epimorphisms. Such maps are
locally surjective on underlying set sheaves. Weak contractibility gives surjectivity
on W-sections, hence evaluation preserves epimorphisms. Its sectionwise kernels then
give preservation of homology and finite colimits. Coproducts and coequalizers generate
all colimits in the common universe, so evaluation preserves these colimits.

To treat the independent diagram universes, use the existing arbitrary-ring theorem
that module sheaves form a Grothendieck abelian category. Shrink only its hom types to
the common module universe. The special adjoint functor theorem, using its generator
and cogenerator, supplies both adjoints to evaluation on this equivalent category.
Adjoints preserve existing limits or colimits of every size. Transport these properties
back along the equivalence and its unit isomorphism; the evaluation functor and all its
section maps are unchanged.
-/
theorem peSectionsLimitsColimits {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{r})
    (W : X.ProEt) [IsAffine W.left]
    (hW : (Scheme.ProEt.topology X).IsWeaklyContractible.{max (u + 1) r v} W) :
    PreservesLimitsOfSize.{wJ, uJ} ((SheafOfModules.evaluation R (op W)) :
      SheafOfModules.{max (u + 1) r v} R ⥤ ModuleCat.{max (u + 1) r v} (R.obj.obj (op W))) ∧
      PreservesColimitsOfSize.{wJ, uJ} ((SheafOfModules.evaluation R (op W)) :
      SheafOfModules.{max (u + 1) r v} R ⥤ ModuleCat.{max (u + 1) r v} (R.obj.obj (op W))) := by
  let ev := SheafOfModules.evaluation.{max (u + 1) r v} R (op W)
  have : ev.Additive := ⟨by intros; rfl⟩
  have : ev.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    let g := (SheafOfModules.toSheaf R).map f
    have : Epi g := inferInstance
    have : Sheaf.IsLocallySurjective g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max (u + 1) r v} g).mpr
        inferInstance
    let g' := (sheafCompose (Scheme.ProEt.topology X)
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) r v})).map g
    have : Sheaf.IsLocallySurjective g' := inferInstance
    exact (ModuleCat.epi_iff_surjective (ev.map f)).mpr (hW g' inferInstance)
  have : ev.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels ev
  have : PreservesFiniteColimits ev :=
    Functor.preservesFiniteColimits_of_preservesHomology ev
  have (K : Type (max (u + 1) r v)) : PreservesColimitsOfShape (Discrete K) ev :=
    pe_evaluation_preserves_coproducts X R W K
  have : PreservesColimitsOfSize.{max (u + 1) r v, max (u + 1) r v} ev :=
    preservesColimits_of_preservesCoequalizers_and_coproducts ev
  have : IsGrothendieckAbelian.{max (u + 1) r v}
      (SheafOfModules.{max (u + 1) r v} R) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses (Scheme.ProEt.topology X) R
  let e := ShrinkHoms.equivalence.{max (u + 1) r v}
    (SheafOfModules.{max (u + 1) r v} R)
  let ev' := e.inverse ⋙ ev
  have : PreservesLimitsOfSize.{max (u + 1) r v, max (u + 1) r v} ev := by
    dsimp [ev]
    infer_instance
  have : PreservesLimitsOfSize.{max (u + 1) r v, max (u + 1) r v} ev' := by
    dsimp [ev']
    infer_instance
  have : PreservesColimitsOfSize.{max (u + 1) r v, max (u + 1) r v} ev' := by
    dsimp [ev']
    infer_instance
  have : ev'.IsRightAdjoint :=
    isRightAdjoint_of_preservesLimits_of_isCoseparating
      (isCoseparator_coseparator _) ev'
  have : ev'.IsLeftAdjoint :=
    isLeftAdjoint_of_preservesColimits_of_isSeparating (isSeparator_separator _) ev'
  let i : e.functor ⋙ ev' ≅ ev :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.unitIso.symm ev ≪≫ ev.leftUnitor
  have : PreservesLimitsOfSize.{wJ, uJ} (e.functor ⋙ ev') := by infer_instance
  have : PreservesColimitsOfSize.{wJ, uJ} (e.functor ⋙ ev') := by infer_instance
  exact ⟨preservesLimits_of_natIso i, preservesColimits_of_natIso i⟩

end CategoryTheory
