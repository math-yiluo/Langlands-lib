/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.Algebra.Group.Subgroup.Finsupp
import WeilConjectures.CategoryTheory.ColimitSiteFiniteRestrictionFamilyLift

/-! # Equality of Kan units at one stage

Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
independence of presentations in the section construction.
(blueprint: lem-weil-pbc-colimit-site-abelian-kan-unit-relations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
section construction, independence of the presentation and restriction arrows.
(blueprint: lem-weil-pbc-colimit-site-abelian-kan-unit-relations).

Proof: Compute K at V_t(U) by the pointwise abelian left Kan colimit over
costructured arrows. Its presentation is the direct sum of the stage groups,
quotiented by differences of generators along restriction arrows. Equality of
the two unit images means that their difference is a finite sum of these
relations, with additive coefficients absorbed into the sections. Include the
two unit generators and all objects and arrows used by this finite expression.
Lift them to a common later stage using the object and arrow set-colimit
hypotheses. Refine to align the endpoints with their prescribed forward images,
then refine to enforce the finitely many triangles by eventual arrow equality.
Equalize the finitely many competing maps out of i and t.right, giving a single
b : t → r in Under i. The two endpoint arrows are identities after refinement.
For every generator (W, f, s) in the finite expression, restrict theta_b(s)
along its lifted arrow from F(b.right)(U) to F(b.right)(W). This assignment is
additive. Each defining relation vanishes: naturality of theta_b exchanges
restriction along a stage arrow with theta_b, and the lifted triangle identifies
the two restrictions to the image of U. Summing these equalities makes the
two endpoint images equal. Their lifted identity arrows identify them with
theta_b(U)(x) and theta_b(U)(x'). The proof uses only the finitely many relations
in this expression, not a common refinement of the entire Kan indexing category,
and assumes no compatibility between different theta maps.
-/
theorem raw_abelian_section_kan_unit_relations
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (i : J) (t : Under i)
    (A : ∀ r : Under i, (F.obj r.right)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (θ : ∀ (r : Under i) (b : t ⟶ r),
      A t ⟶ (F.map b.right).toFunctor.op ⋙ A r)
    (K : V.ptᵒᵖ ⥤ AddCommGrpCat.{u})
    (β : A t ⟶ (V.ι.app t.right).toFunctor.op ⋙ K)
    (hβ : K.IsLeftKanExtension β)
    (U : F.obj t.right) :
    ∀ (x x' : (A t).obj (op U)), β.app (op U) x = β.app (op U) x' →
      ∃ (r : Under i) (b : t ⟶ r),
        (θ r b).app (op U) x = (θ r b).app (op U) x' := by
  classical
  intro x x' h
  have : K.IsLeftKanExtension β := hβ
  let C := CostructuredArrow (V.ι.app t.right).toFunctor.op
    (op ((V.ι.app t.right).toFunctor.obj U))
  let L : C ⥤ AddCommGrpCat.{u} := CostructuredArrow.proj _ _ ⋙ A t
  let c := (Functor.LeftExtension.mk K β).coconeAt
    (op ((V.ι.app t.right).toFunctor.obj U))
  have hc : IsColimit c := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    K β (op ((V.ι.app t.right).toFunctor.obj U))
  let o : C := CostructuredArrow.mk (𝟙 (op ((V.ι.app t.right).toFunctor.obj U)))
  have hinj : Function.Injective (AddCommGrpCat.Colimits.Quot.desc L c) := by
    apply Function.LeftInverse.injective
      (g := hc.desc (AddCommGrpCat.Colimits.toCocone L
        (AddMonoidHom.id (AddCommGrpCat.Colimits.Quot L))))
    intro z
    exact AddCommGrpCat.Colimits.Quot.desc_toCocone_desc_app L c
      (AddMonoidHom.id _) hc z
  have he : AddCommGrpCat.Colimits.Quot.ι L o x =
      AddCommGrpCat.Colimits.Quot.ι L o x' := by
    apply hinj
    rw [AddCommGrpCat.Colimits.Quot.ι_desc, AddCommGrpCat.Colimits.Quot.ι_desc]
    change (β.app (op U) ≫ K.map (𝟙 _)) x =
      (β.app (op U) ≫ K.map (𝟙 _)) x'
    change K.map (𝟙 _) (β.app (op U) x) = K.map (𝟙 _) (β.app (op U) x')
    exact congrArg (K.map (𝟙 _)) h
  have hm : DFinsupp.single o x - DFinsupp.single o x' ∈
      AddCommGrpCat.Colimits.Relations L := by
    apply (QuotientAddGroup.eq_iff_sub_mem).mp
    exact he
  let R := Σ (j j' : C), (j ⟶ j') × L.obj j
  let rel : R → DFinsupp (fun j ↦ L.obj j) := fun e ↦
    DFinsupp.single e.2.1 (L.map e.2.2.1 e.2.2.2) -
      DFinsupp.single e.1 e.2.2.2
  have hm' : DFinsupp.single o x - DFinsupp.single o x' ∈
      AddSubgroup.closure (Set.range rel) := by
    convert hm using 1
    congr 1
    ext z
    simp only [Set.mem_range, rel, R]
    constructor
    · rintro ⟨⟨j, j', f, s⟩, rfl⟩
      exact ⟨j, j', f, s, rfl⟩
    · rintro ⟨j, j', f, s, rfl⟩
      exact ⟨⟨j, j', f, s⟩, rfl⟩
  obtain ⟨n, hn⟩ := AddSubgroup.exists_finsupp_of_mem_closure_range rel _ hm'
  let objs : Finset C := insert o (n.support.biUnion fun e ↦ {e.1, e.2.1})
  let src (e : n.support) : objs := ⟨e.1.1, by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_biUnion.mpr ⟨e.1, e.2, by simp⟩⟩
  let dst (e : n.support) : objs := ⟨e.1.2.1, by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_biUnion.mpr ⟨e.1, e.2, by simp⟩⟩
  let base : objs := ⟨o, Finset.mem_insert_self _ _⟩
  obtain ⟨r, b, g, hg, hg₀⟩ := colimit_site_finite_restriction_family_lift
    J F V hobjects harrows i t U
    (fun q : objs ↦ q.1.left.unop) (fun q ↦ q.1.hom.unop)
    dst src (fun e : n.support ↦ e.1.2.2.1.left.unop)
    (fun e ↦ by
      exact congrArg Quiver.Hom.unop (CostructuredArrow.w e.1.2.2.1))
    base rfl (by simp [base, o])
  let m (q : C) : (L.obj q) →+ (A r).obj (op ((F.map b.right).toFunctor.obj U)) :=
    if hq : q ∈ objs then
      ((A r).map (g ⟨q, hq⟩).op).hom.comp ((θ r b).app q.left).hom
    else 0
  let φ := DFinsupp.sumAddHom m
  have hφ (e : n.support) : φ (rel e.1) = 0 := by
    have hs : e.1.1 ∈ objs := (src e).2
    have ht : e.1.2.1 ∈ objs := (dst e).2
    simp only [φ, rel, map_sub, DFinsupp.sumAddHom_single, m, dite_eq_left hs, dite_eq_left ht,
      sub_eq_zero]
    have hθ := (θ r b).naturality e.1.2.2.1.left
    have htri := hg e
    have hh := ConcreteCategory.congr_hom hθ e.1.2.2.2
    change (A r).map (g (dst e)).op
        ((θ r b).app e.1.2.1.left (L.map e.1.2.2.1 e.1.2.2.2)) =
      (A r).map (g (src e)).op ((θ r b).app e.1.1.left e.1.2.2.2)
    change (θ r b).app e.1.2.1.left ((A t).map e.1.2.2.1.left e.1.2.2.2) =
      (A r).map ((F.map b.right).toFunctor.map e.1.2.2.1.left.unop).op
        ((θ r b).app e.1.1.left e.1.2.2.2) at hh
    change (A r).map (g (dst e)).op
        ((θ r b).app e.1.2.1.left ((A t).map e.1.2.2.1.left e.1.2.2.2)) =
      (A r).map (g (src e)).op ((θ r b).app e.1.1.left e.1.2.2.2)
    rw [hh]
    change ((A r).map ((F.map b.right).toFunctor.map e.1.2.2.1.left.unop).op ≫
      (A r).map (g (dst e)).op) _ = _
    rw [← (A r).map_comp]
    have ht := congrArg Quiver.Hom.op htri
    simpa only [op_comp] using
      ConcreteCategory.congr_hom (congrArg (A r).map ht) ((θ r b).app e.1.1.left e.1.2.2.2)
  have hz : φ (DFinsupp.single o x - DFinsupp.single o x') = 0 := by
    rw [hn]
    simp only [Finsupp.sum, map_sum, map_zsmul]
    apply Finset.sum_eq_zero
    intro e he
    rw [hφ ⟨e, he⟩, zsmul_zero]
  refine ⟨r, b, ?_⟩
  have hbase : o ∈ objs := Finset.mem_insert_self _ _
  change ((θ r b).app (op U)).hom x = ((θ r b).app (op U)).hom x'
  simp only [φ, map_sub, DFinsupp.sumAddHom_single, m, dite_eq_left hbase] at hz
  change ((A r).map (g base).op).hom (((θ r b).app (op U)).hom x) -
    ((A r).map (g base).op).hom (((θ r b).app (op U)).hom x') = 0 at hz
  have : IsIso (g base) := by rw [hg₀]; infer_instance
  exact (ConcreteCategory.bijective_of_isIso ((A r).map (g base).op)).1
    (sub_eq_zero.mp hz)


end CategoryTheory
