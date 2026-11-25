/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationExact
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits

/-!
# Evaluation at affine weakly contractible pro-etale objects

## References

* Stacks Project, Tags 0946 (1), 03DA and 0935 (2)
* Stacks Project, Tags 0946 (1), 03DA, 0935 (2), and 002F
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Functor

namespace AlgebraicGeometry.Scheme.ProEt

/-- A colimit of module sheaves is the sheafification of the presheaf colimit.
The comparison is the sheafification unit followed by an isomorphism, so is locally
surjective on underlying sections. -/
private theorem colimit_comparison_locally_surjective
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {K : Type (u + 1)} [SmallCategory K]
    (D : K ⥤ SheafOfModules.{u + 1} R) (c : Limits.Cocone D) (hc : Limits.IsColimit c) :
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
support fixes the section locally, hence globally by separatedness. -/
private theorem affine_coproduct_section_finite_support
    (X : Scheme.{u}) (R : Sheaf (topology X) RingCat.{u + 1})
    (W : X.ProEt) [IsAffine W.left]
    (K : Type (u + 1)) (H : K → SheafOfModules.{u + 1} R)
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
  have : Presheaf.IsLocallySurjective (topology X) q :=
    colimit_comparison_locally_surjective R D c hc
  obtain ⟨I, hI, V, f, hcover, hf⟩ := finite_cover_refinement X W
    (Presheaf.imageSieve q s) (Presheaf.imageSieve_mem (topology X) q s)
  let := hI
  have hrep (i : I) : ∃ (S : Finset (Discrete K))
      (t : (∐ (fun j : S ↦ H j.val.as)).val.obj (op (V i))),
      (Sigma.desc (fun j : S ↦ Sigma.ι H j.val.as)).val.app (op (V i)) t =
        (∐ H).val.map (f i).op s := by
    obtain ⟨t, ht⟩ := hf i
    let E := PresheafOfModules.evaluation R.obj (op (V i)) ⋙ CategoryTheory.forget _
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
  let G : Sheaf (topology X) (Type (u + 1)) :=
    (sheafCompose (topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
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
whose split inclusion and invertible comparison force the element to vanish. -/
private theorem affine_evaluation_coproduct_isIso
    (X : Scheme.{u}) (R : Sheaf (topology X) RingCat.{u + 1})
    (W : X.ProEt) [IsAffine W.left]
    (K : Type (u + 1)) (H : K → SheafOfModules.{u + 1} R) :
    IsIso (sigmaComparison (SheafOfModules.evaluation.{u + 1} R (op W)) H) := by
  classical
  let ev := SheafOfModules.evaluation.{u + 1} R (op W)
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
      rw [← ModuleCat.comp_apply, ← hh, ModuleCat.comp_apply, ht]
      exact hz
    have hzero : (sigmaComparison ev H') t = 0 := by
      have hh := congrArg (ev.map p) he
      simpa only [← ModuleCat.comp_apply, Category.assoc, hq, map_zero] using hh
    have htzero : t = 0 := (ModuleCat.mono_iff_injective (sigmaComparison ev H')).mp
      (by infer_instance) (hzero.trans (map_zero _).symm)
    rw [← ht, htzero, map_zero]
  · intro s
    obtain ⟨S, t, ht⟩ := affine_coproduct_section_finite_support X R W K H s
    have : IsIso (sigmaComparison ev (fun i : S ↦ H i.val)) := hfinite S
    let a := inv (sigmaComparison ev (fun i : S ↦ H i.val)) t
    refine ⟨(Sigma.desc (fun i : S ↦ Sigma.ι E i.val)) a, ?_⟩
    rw [← ModuleCat.comp_apply, hcomp S, ModuleCat.comp_apply]
    dsimp only [a]
    rw [IsIso.inv_hom_id_apply]
    exact ht

/-- Evaluation on an affine pro-etale object preserves coproducts of section-universe size. -/
private theorem affine_evaluation_preserves_coproducts
    (X : Scheme.{u}) (R : Sheaf (topology X) RingCat.{u + 1})
    (W : X.ProEt) [IsAffine W.left] (K : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete K)
      (SheafOfModules.evaluation.{u + 1} R (op W)) := by
  let ev := SheafOfModules.evaluation.{u + 1} R (op W)
  have (H : K → SheafOfModules.{u + 1} R) : PreservesColimit (Discrete.functor H) ev := by
    have : IsIso (sigmaComparison ev H) := affine_evaluation_coproduct_isIso X R W K H
    exact PreservesCoproduct.of_iso_comparison ev H
  exact preservesColimitsOfShape_of_discrete ev

/-- Evaluation of module sheaves at an affine weakly contractible object is exact
and preserves all small colimits. The filtered-colimit comparison is invertible
and natural in diagrams. Commutativity is forgotten only to use Mathlib's ringed-site
module category. Smallness is relative to the universe of section modules. -/
theorem affine_weaklyContractible_evaluation_colimits
    (X : Scheme.{u}) (R : Sheaf (topology X) CommRingCat.{u + 1})
    (W : X.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (topology X) (Type (u + 1))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op W))) :
    PreservesFiniteLimits (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)) ∧
    PreservesFiniteColimits (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)) ∧
    PreservesColimitsOfSize.{u + 1, u + 1}
      (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)) ∧
    (∀ (K : Type (u + 1)) [SmallCategory K] [IsFiltered K]
      (D : K ⥤ ringedSiteModules.{u + 1} ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)),
      IsIso (colimit.post D (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)))) ∧
    (∀ (K : Type (u + 1)) [SmallCategory K] [IsFiltered K]
      (D D' : K ⥤ ringedSiteModules.{u + 1} ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (α : D ⟶ D'),
      colimit.post D (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)) ≫
          (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W)).map
            (colim.map α) =
        colim.map (whiskerRight α (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W))) ≫
          colimit.post D' (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op W))) := by
  let A := (sheafCompose (topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let ev := SheafOfModules.evaluation.{u + 1} A (op W)
  have : ev.Additive := ⟨by intros; rfl⟩
  let : ev.PreservesHomology :=
    weaklyContractible_evaluation_preservesHomology X R W hW
  have hlim : PreservesFiniteLimits ev :=
    Functor.preservesFiniteLimits_of_preservesHomology ev
  have hcol : PreservesFiniteColimits ev :=
    Functor.preservesFiniteColimits_of_preservesHomology ev
  have (K : Type (u + 1)) : PreservesColimitsOfShape (Discrete K) ev :=
    affine_evaluation_preserves_coproducts X A W K
  have hall : PreservesColimitsOfSize.{u + 1, u + 1} ev :=
    preservesColimits_of_preservesCoequalizers_and_coproducts ev
  have hfiltered : ∀ (K : Type (u + 1)) [SmallCategory K] [IsFiltered K]
      (D : K ⥤ ringedSiteModules.{u + 1} A), IsIso (colimit.post D ev) := by
    intro K _ _ D
    let : PreservesColimitsOfSize.{u + 1, u + 1} ev := hall
    infer_instance
  refine ⟨hlim, hcol, hall, hfiltered, ?_⟩
  intro K _ _ D D' α
  exact colimit.map_post α ev

end AlgebraicGeometry.Scheme.ProEt
