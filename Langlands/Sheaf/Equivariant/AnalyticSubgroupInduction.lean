import Langlands.Sheaf.Equivariant.AnalyticSubgroupRestriction
import Langlands.Sheaf.Equivariant.LocalActionConstant

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v w z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {ρ : G →* Aut X} {H : Subgroup G}
variable {P : MorphismProperty (LocalizedCategory.{u, v, v} (K := K))} [P.RespectsIso]
variable {R : Type w} [CommRing R]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Images of discrete subgroup presheaves lie in the discrete part for the full group.
Translation reduces an arbitrary twisted restriction to one in the subgroup. -/
theorem mem_discreteSubmodule_of_subgroup_hom
    (hH : IsOpen (H : Set G)) (Adm : P.Over ⊤ X → Prop)
    (hAdm : ∀ (t : G) (V : P.Over ⊤ X), Adm V → Adm ((translate P ρ t).obj V))
    {F : (TwistedOver P (ρ.comp H.subtype))ᵒᵖ ⥤ ModuleCat.{w} R}
    (hF : (liftSystem P (ρ.comp H.subtype) Adm).IsDiscrete F)
    {E : (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R}
    (η : F ⟶ (subgroupInclusion ρ H).op ⋙ E)
    (U : TwistedOver P (ρ.comp H.subtype)) (s : F.obj (op U)) :
    η.app (op U) s ∈ discreteSubmodule (liftSystem P ρ Adm) E
      ((subgroupInclusion ρ H).obj U) := by
  rintro V S a ⟨hV, l, hS, rfl⟩ f
  let t := Hom.twist f
  let W : TwistedOver P (ρ.comp H.subtype) := ⟨(translate P ρ t).obj V.obj⟩
  let f₀ : W ⟶ U := subgroupUntwist t f (by
    change Hom.twist f * (Hom.twist f)⁻¹ ∈ H
    simpa only [mul_inv_cancel] using H.one_mem)
  have hf : relabel ρ t V.obj ≫ (subgroupInclusion ρ H).map f₀ = f :=
    relabel_comp_subgroupInclusion_map_subgroupUntwist t f _
  let lH : ActionLift (ρ.comp H.subtype) (TwistedOver.hom W) :=
    liftToSubgroup H (l.translate t)
  obtain ⟨N, hNS, hN⟩ := hF W (liftOpenSubgroup (U := W) lH)
    ((liftAction (U := W) lH).comp (Subgroup.inclusion le_rfl))
    ⟨hAdm t V.obj hV, lH, le_rfl, rfl⟩ (F.map f₀.op s)
  let N' : OpenSubgroup G :=
    ⟨(N : Subgroup H).map H.subtype, isOpen_map_subtype hH N.isOpen⟩
  let M : OpenSubgroup G := N'.comap (MulAut.conj t).toMonoidHom
    ((continuous_const.mul continuous_id).mul continuous_const)
  refine ⟨M ⊓ S, inf_le_right, fun g hg => ?_⟩
  have hconj : t * (g : G) * t⁻¹ ∈ (N : Subgroup H).map H.subtype := by
    exact inf_le_left (a := M) hg
  let k : H := ⟨t * (g : G) * t⁻¹, mem_of_mem_map_subtype hconj⟩
  have hk : k ∈ N := mk_mem_of_mem_map_subtype hconj
  let kS : (liftOpenSubgroup lH : Subgroup H) := ⟨k, hNS hk⟩
  have heq : (⟨t⁻¹ * ((kS : H) : G) * t,
      conj_mem_of_mem_liftToSubgroup_translate H l t kS.2⟩ : l.subgroup) =
      ⟨g, hS g.2⟩ := by
    apply Subtype.ext
    change t⁻¹ * (t * (g : G) * t⁻¹) * t = (g : G)
    group
  have hinter :
      relabel ρ t V.obj ≫ (subgroupInclusion ρ H).map (liftAction lH kS).unop.asHom =
        (liftAction l ⟨g, hS g.2⟩).unop.asHom ≫ relabel ρ t V.obj := by
    rw [subgroupInclusion_map_liftAction_translate H t l kS, heq]
    rw [← Category.assoc, ← Category.assoc]
    have hri : relabel ρ t V.obj ≫ relabelInv ρ t V.obj = 𝟙 _ :=
      hom_ext (inv_mul_cancel t) (Category.id_comp _)
    rw [hri, Category.id_comp]
  have hfixed :
      E.map ((subgroupInclusion ρ H).map (liftAction lH kS).unop.asHom).op
        (η.app (op W) (F.map f₀.op s)) = η.app (op W) (F.map f₀.op s) := by
    exact (η.naturality_apply (liftAction lH kS).unop.asHom.op _).symm.trans
      (congrArg (η.app (op W)) (hN kS hk))
  have hval : E.map f.op (η.app (op U) s) =
      E.map (relabel ρ t V.obj).op (η.app (op W) (F.map f₀.op s)) := by
    rw [← hf, map_comp_op_apply]
    exact congrArg (E.map (relabel ρ t V.obj).op) (η.naturality_apply f₀.op s).symm
  change E.map (liftAction l ⟨g, hS g.2⟩).unop.asHom.op
    (E.map f.op (η.app (op U) s)) = E.map f.op (η.app (op U) s)
  rw [hval]
  rw [← map_comp_op_apply, ← hinter, map_comp_op_apply]
  exact congrArg (E.map (relabel ρ t V.obj).op) hfixed

section Induction

variable [HasColimitsOfShape (Discrete (Quotient (QuotientGroup.rightRel H)))
  (ModuleCat.{w} R)]

/-- Left Kan extension from an open subgroup preserves discreteness for a
translation-invariant admissibility condition. -/
theorem isDiscrete_subgroupLan
    (hH : IsOpen (H : Set G)) (Adm : P.Over ⊤ X → Prop)
    (hAdm : ∀ (t : G) (V : P.Over ⊤ X), Adm V → Adm ((translate P ρ t).obj V))
    {F : (TwistedOver P (ρ.comp H.subtype))ᵒᵖ ⥤ ModuleCat.{w} R}
    (hF : (liftSystem P (ρ.comp H.subtype) Adm).IsDiscrete F) :
    (liftSystem P ρ Adm).IsDiscrete ((subgroupInclusion ρ H).op.lan.obj F) := by
  let E := (subgroupInclusion ρ H).op.lan.obj F
  let η := (subgroupInclusion ρ H).op.lanUnit.app F
  let L := liftSystem P ρ Adm
  let η' : F ⟶ (subgroupInclusion ρ H).op ⋙ discretePresheaf L E :=
    { app U := ModuleCat.ofHom (LinearMap.codRestrict _ (η.app U).hom fun s =>
        mem_discreteSubmodule_of_subgroup_hom hH Adm hAdm hF η U.unop s)
      naturality U V f := by
        ext s
        apply Subtype.ext
        exact congrArg (fun k => k.hom s) (η.naturality f) }
  let ψ : E ⟶ discretePresheaf L E :=
    E.descOfIsLeftKanExtension η _ η'
  have hψ : ψ ≫ discretePresheafι L E = 𝟙 E := by
    apply E.hom_ext_of_isLeftKanExtension η
    rw [Functor.whiskerLeft_comp, ← Category.assoc,
      Functor.descOfIsLeftKanExtension_fac]
    rfl
  rw [isDiscrete_iff_forall_mem]
  intro U s
  have hs := congrArg (fun k => (k.app (op U)).hom s) hψ
  change ((ψ.app (op U)).hom s).1 = s at hs
  rw [← hs]
  exact ((ψ.app (op U)).hom s).2

/-- Sheaf induction from an open subgroup preserves local-action discreteness,
assuming finite equivariant refinements on the group site. -/
theorem isDiscrete_subgroupInduction
    (hH : IsOpen (H : Set G)) (Adm : P.Over ⊤ X → Prop)
    (hAdm : ∀ (t : G) (V : P.Over ⊤ X), Adm V → Adm ((translate P ρ t).obj V))
    (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
    [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
    [(liftSystem P ρ Adm).HasFiniteEquivariantRefinements (twistedTopology ρ J)]
    (F : Sheaf (twistedTopology (ρ.comp H.subtype) J) (ModuleCat.{w} R))
    (hF : (liftSystem P (ρ.comp H.subtype) Adm).IsDiscrete F.obj) :
    (liftSystem P ρ Adm).IsDiscrete ((subgroupInduction ρ H R J).obj F).obj :=
  isDiscrete_sheafify (isDiscrete_subgroupLan hH Adm hAdm hF)

/-- Sheaf induction on the full subcategories discrete for the admissible analytic
local lifts. Only finite equivariant refinements for the target group are required. -/
def discreteSheafSubgroupInduction
    (hH : IsOpen (H : Set G)) (Adm : P.Over ⊤ X → Prop)
    (hAdm : ∀ (t : G) (V : P.Over ⊤ X), Adm V → Adm ((translate P ρ t).obj V))
    (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
    [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
    [(liftSystem P ρ Adm).HasFiniteEquivariantRefinements (twistedTopology ρ J)] :
    (liftSystem P (ρ.comp H.subtype) Adm).DiscreteSheaf (ModuleCat.{w} R)
        (twistedTopology (ρ.comp H.subtype) J) ⥤
      (liftSystem P ρ Adm).DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J) :=
  ((liftSystem P ρ Adm).discreteSheafProperty (ModuleCat.{w} R)
    (twistedTopology ρ J)).lift
    ((liftSystem P (ρ.comp H.subtype) Adm).discreteSheafInclusion (ModuleCat.{w} R)
      (twistedTopology (ρ.comp H.subtype) J) ⋙ subgroupInduction ρ H R J)
    fun F => isDiscrete_subgroupInduction hH Adm hAdm J F.obj F.property

end Induction

end Langlands.Sheaf.Equivariant.Analytic
