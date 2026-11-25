/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProj.RelativeProjTwistChartDescentCompatibility

/-! # Reading sections across relative Proj twist charts

## References

* Stacks Project, Constructions, Tag 01NR
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

attribute [local irreducible] tensorPullback tensorPullbackObj tensorPullbackSection

private theorem chart_unit_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : k = f ≫ g)
    (L : Z.Modules) (M : Y.Modules) (N : X.Modules)
    (e : (tensorPullback g).obj L ≅ M)
    (t : (tensorPullback f).obj M ≅ N)
    (d : (tensorPullback k).obj L ≅ N)
    (hsq : eqToIso (congrArg (fun q ↦ (tensorPullback q).obj L) hk) ≪≫
      (tensorPullbackSectionComp f g).app L ≪≫ (tensorPullback f).mapIso e ≪≫ t = d)
    (W : Z.Opens) (s : Γ(L, W)) :
    t.hom.app (f ⁻¹ᵁ (g ⁻¹ᵁ W))
      (((tensorPullbackSectionAdjunction f).unit.app M).app (g ⁻¹ᵁ W)
        (e.hom.app (g ⁻¹ᵁ W)
          (((tensorPullbackSectionAdjunction g).unit.app L).app W s))) =
      eqToHom (congrArg (fun q ↦ Γ(N, q ⁻¹ᵁ W)) hk)
        (d.hom.app (k ⁻¹ᵁ W)
          (((tensorPullbackSectionAdjunction k).unit.app L).app W s)) := by
  subst k
  have hc := congrArg (fun q ↦ q.app W s)
    (Adjunction.unit_leftAdjointUniq_hom_app
      (tensorPullbackSectionAdjunction (f ≫ g))
      (((tensorPullbackSectionAdjunction g).comp
        (tensorPullbackSectionAdjunction f)).ofNatIsoRight (pushforwardComp f g)) L)
  simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Adjunction.comp_unit_app,
    Functor.whiskerLeft_app, pushforwardComp_hom_app_app] at hc
  change ((tensorPullbackSectionComp f g).hom.app L).app ((f ≫ g) ⁻¹ᵁ W)
    (((tensorPullbackSectionAdjunction (f ≫ g)).unit.app L).app W s) =
    ((tensorPullbackSectionAdjunction f).unit.app ((tensorPullback g).obj L)).app
      (g ⁻¹ᵁ W) (((tensorPullbackSectionAdjunction g).unit.app L).app W s) at hc
  have hn := congrArg (fun q ↦ q.app (g ⁻¹ᵁ W)
      (((tensorPullbackSectionAdjunction g).unit.app L).app W s))
    ((tensorPullbackSectionAdjunction f).unit.naturality e.hom)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply] at hn
  rw [← hsq]
  simp only [Iso.trans_hom, eqToIso_refl, Iso.refl_hom, Category.id_comp,
    Functor.mapIso_hom, Hom.comp_app, ConcreteCategory.comp_apply]
  change _ = t.hom.app _ (((tensorPullback f).map e.hom).app _
    (((tensorPullbackSectionComp f g).hom.app L).app _
      (((tensorPullbackSectionAdjunction (f ≫ g)).unit.app L).app W s)))
  erw [hc]
  exact congrArg (t.hom.app _) hn

private theorem restriction_eq_transport {X : Scheme.{u}} (N : X.Modules)
    {P Q : X.Opens} (h : P = Q) (i : Q ⟶ P) :
    N.presheaf.map i.op = eqToHom (congrArg (fun W ↦ Γ(N, W)) h) := by
  subst Q
  rw [Subsingleton.elim i (𝟙 P), op_id, CategoryTheory.Functor.map_id]
  rfl

private theorem chart_unit_restrict {X Z : Scheme.{u}} (k : X ⟶ Z)
    (L : Z.Modules) (N : X.Modules) (d : (tensorPullback k).obj L ≅ N)
    (V W : Z.Opens) (h : W ≤ V) (he : k ⁻¹ᵁ V = k ⁻¹ᵁ W) (s : Γ(L, V)) :
    eqToHom (congrArg (fun T ↦ Γ(N, T)) he)
        (d.hom.app (k ⁻¹ᵁ V)
          (((tensorPullbackSectionAdjunction k).unit.app L).app V s)) =
      d.hom.app (k ⁻¹ᵁ W)
        (((tensorPullbackSectionAdjunction k).unit.app L).app W
          (L.presheaf.map (homOfLE h).op s)) := by
  let q := (tensorPullbackSectionAdjunction k).unit.app L ≫ (pushforward k).map d.hom
  have hn := PresheafOfModules.naturality_apply q.val (homOfLE h).op s
  change q.app W (L.presheaf.map (homOfLE h).op s) =
    N.presheaf.map ((TopologicalSpace.Opens.map k.base).map (homOfLE h)).op
      (q.app V s) at hn
  rw [restriction_eq_transport N he] at hn
  exact hn.symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.GradedAlgebraData
variable {S : Scheme.{u}} (A : S.GradedAlgebraData)

/-- The normalized transition induced by a compatible chart square intertwines reading maps. -/
theorem twist_chart_transition_read
    (L : A.relProj.Modules)
    (chart : ∀ U : S.affineOpens,
      (Scheme.Modules.tensorPullback (A.relProjι U)).obj L ≅
        Proj.twist (A.grading U) 1)
    (U V : S.affineOpens) (h : U ≤ V)
    (θ : ∀ j : ℤ,
      (Scheme.Modules.tensorPullback (A.relProjFunctor.map (homOfLE h))).obj
          (Proj.twist (A.grading V) j) ≅ Proj.twist (A.grading U) j)
    (hθ : Proj.IsScalarExtensionTwistComparison (A.res h)
      (A.relProjFunctor.map (homOfLE h)) θ)
    (hsq :
      eqToIso (congrArg (fun f ↦
          (Scheme.Modules.tensorPullback f).obj L)
        (A.relProjFunctor_map_relProjι (homOfLE h)).symm) ≪≫
        (Scheme.Modules.tensorPullbackSectionComp
          (A.relProjFunctor.map (homOfLE h)) (A.relProjι V)).app L ≪≫
        (Scheme.Modules.tensorPullback (A.relProjFunctor.map (homOfLE h))).mapIso
          (chart V) ≪≫ θ 1 = chart U)
    (hopen : A.relProjFunctor.map (homOfLE h) ⁻¹ᵁ A.twistChartOpen V =
      A.twistChartOpen U) :
    ∀ s : Γ(L, A.relProjHom ⁻¹ᵁ V.1),
      let t : Γ(Proj.twist (A.grading V) 1, A.twistChartOpen V) →+
          Γ(Proj.twist (A.grading U) 1, A.twistChartOpen U) :=
        ConcreteCategory.hom
          (((Scheme.Modules.tensorPullbackSectionAdjunction
              (A.relProjFunctor.map (homOfLE h))).unit.app
              (Proj.twist (A.grading V) 1)).app (A.twistChartOpen V) ≫
            (θ 1).hom.app
              (A.relProjFunctor.map (homOfLE h) ⁻¹ᵁ A.twistChartOpen V) ≫
            eqToHom (congrArg
              (fun W ↦ Γ(Proj.twist (A.grading U) 1, W)) hopen))
      t (A.twistChartRead L chart V s) =
        A.twistChartRead L chart U
          (L.presheaf.map ((TopologicalSpace.Opens.map A.relProjHom.base).map
            (homOfLE (X := S.Opens) h)).op s) := by
  have _ := hθ
  intro s
  dsimp only
  have hc := Scheme.Modules.chart_unit_comp
    (A.relProjFunctor.map (homOfLE h)) (A.relProjι V) (A.relProjι U)
    (A.relProjFunctor_map_relProjι (homOfLE h)).symm L
    (Proj.twist (A.grading V) 1) (Proj.twist (A.grading U) 1)
    (chart V) (θ 1) (chart U) hsq (A.relProjHom ⁻¹ᵁ V.1) s
  have he : A.relProjι U ⁻¹ᵁ (A.relProjHom ⁻¹ᵁ V.1) =
      A.relProjι U ⁻¹ᵁ (A.relProjHom ⁻¹ᵁ U.1) := by
    have hb : A.relProjFunctor.map (homOfLE h) ⁻¹ᵁ
        (A.relProjι V ⁻¹ᵁ (A.relProjHom ⁻¹ᵁ V.1)) =
        A.relProjι U ⁻¹ᵁ (A.relProjHom ⁻¹ᵁ V.1) := by
      rw [← Scheme.Hom.comp_preimage, A.relProjFunctor_map_relProjι (homOfLE h)]
    exact hb.symm.trans hopen
  have hr := Scheme.Modules.chart_unit_restrict (A.relProjι U) L
    (Proj.twist (A.grading U) 1) (chart U)
    (A.relProjHom ⁻¹ᵁ V.1) (A.relProjHom ⁻¹ᵁ U.1)
    (A.relProjHom.preimage_mono h) he s
  change eqToHom (congrArg (fun W ↦ Γ(Proj.twist (A.grading U) 1, W)) hopen)
    ((θ 1).hom.app _
      (((Scheme.Modules.tensorPullbackSectionAdjunction
        (A.relProjFunctor.map (homOfLE h))).unit.app
          (Proj.twist (A.grading V) 1)).app _
            (A.twistChartRead L chart V s))) = _
  unfold twistChartRead
  change eqToHom (congrArg (fun W ↦ Γ(Proj.twist (A.grading U) 1, W)) hopen)
    ((θ 1).hom.app _
    (((Scheme.Modules.tensorPullbackSectionAdjunction
      (A.relProjFunctor.map (homOfLE h))).unit.app
        (Proj.twist (A.grading V) 1)).app _
          ((chart V).hom.app _
            (((Scheme.Modules.tensorPullbackSectionAdjunction
              (A.relProjι V)).unit.app L).app _ s)))) = _
  erw [hc]
  have ht (P Q R : AddCommGrpCat.{u}) (a : P = Q) (b : Q = R) (x : P) :
      eqToHom b (eqToHom a x) = eqToHom (a.trans b) x := by
    subst Q
    subst R
    rfl
  exact (ht _ _ _ _ _ _).trans hr

end AlgebraicGeometry.Scheme.GradedAlgebraData
