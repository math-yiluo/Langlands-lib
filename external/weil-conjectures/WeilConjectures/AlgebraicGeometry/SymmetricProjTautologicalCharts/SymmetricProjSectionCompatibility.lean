/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjAffineComparisonExistence
import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
import WeilConjectures.AlgebraicGeometry.Modules.HomSection

/-! # Degree-one section compatibility for affine symmetric Proj comparisons

Source: Stacks Project, Constructions, Tags 01NR, 01OB and 01N2.
(blueprint: lem-trf-symmetric-proj-section-compatibility).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomogeneousLocalization
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

open Scheme.Modules

private theorem tensor_unit_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (W : Y.Opens) (m : Γ(M, W)) :
    ((tensorPullbackSectionAdjunction f).unit.app M).app W m =
      tensorPullbackSection f M W m :=
  (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction f)).1 M W m

private theorem normalized_adjunction_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensorPullbackSectionAdjunction f =
      Classical.choose (exists_tensorPullbackAdjunction f) := by
  apply (existsUnique_tensorPullbackSectionAdjunction f).unique
  · exact tensor_unit_section f
  · intro M V m
    exact Classical.choose_spec (exists_tensorPullbackAdjunction f) M (op V) m

attribute [local irreducible] tensorPullback tensorPullbackObj tensorPullbackSectionAdjunction
  tensorPullbackSection tensorPullbackSectionComp boundaryPullbackComparison
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjι

private theorem tensor_section_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (g : M ⟶ N) (W : Y.Opens) (m : Γ(M, W)) :
    ((tensorPullback f).map g).app (f ⁻¹ᵁ W) (tensorPullbackSection f M W m) =
      tensorPullbackSection f N W (g.app W m) := by
  rw [← tensor_unit_section, ← tensor_unit_section]
  exact congrArg (fun k ↦ k.app W m)
    ((tensorPullbackSectionAdjunction f).unit_naturality g)

private theorem tensor_section_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) {W W' : Y.Opens} (i : W' ⟶ W) (m : Γ(M, W)) :
    tensorPullbackSection f M W' (M.presheaf.map i.op m) =
      ((tensorPullback f).obj M).presheaf.map
        ((TopologicalSpace.Opens.map f.base).map i).op
          (tensorPullbackSection f M W m) := by
  rw [← tensor_unit_section, ← tensor_unit_section]
  exact Hom.app_presheaf_map ((tensorPullbackSectionAdjunction f).unit.app M) i m

private theorem tensor_comp_section {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (W : Z.Opens) (m : Γ(M, W)) :
    ((tensorPullbackSectionComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ W)
      (tensorPullbackSection f ((tensorPullback g).obj M) (g ⁻¹ᵁ W)
        (tensorPullbackSection g M W m)) =
      tensorPullbackSection (f ≫ g) M W m := by
  let adj := ((tensorPullbackSectionAdjunction g).comp
    (tensorPullbackSectionAdjunction f)).ofNatIsoRight (pushforwardComp f g)
  have he := adj.unit_leftAdjointUniq_hom_app (tensorPullbackSectionAdjunction (f ≫ g)) M
  have hunit : adj.unit.app M =
      (tensorPullbackSectionAdjunction g).unit.app M ≫
        (pushforward g).map
          ((tensorPullbackSectionAdjunction f).unit.app ((tensorPullback g).obj M)) ≫
        (pushforwardComp f g).hom.app _ := by
    rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.homEquiv_id, Adjunction.comp_unit_app, Category.assoc]
    rfl
  rw [hunit] at he
  have hs := congrArg (fun k ↦ k.app W m) he
  change (((tensorPullbackSectionAdjunction (f ≫ g)).leftAdjointUniq adj).inv.app M).app
      ((f ≫ g) ⁻¹ᵁ W)
      (((tensorPullbackSectionAdjunction f).unit.app ((tensorPullback g).obj M)).app
        (g ⁻¹ᵁ W) (((tensorPullbackSectionAdjunction g).unit.app M).app W m)) =
      ((tensorPullbackSectionAdjunction (f ≫ g)).unit.app M).app W m at hs
  simpa only [tensorPullbackSectionComp, tensor_unit_section] using hs

private theorem tensor_unit_comparison_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W : Y.Opens) (r : Γ(Y, W)) :
    (((boundaryPullbackComparison f).app (unit Y) ≪≫ pullbackObjUnitIso f).hom).app
      (f ⁻¹ᵁ W) (tensorPullbackSection f (unit Y) W r) = f.app W r := by
  have he := (tensorPullbackSectionAdjunction f).unit_leftAdjointUniq_hom_app
    (pullbackPushforwardAdjunction f) (unit Y)
  rw [normalized_adjunction_eq] at he
  have hs := congrArg (fun k ↦ k.app W r) he
  dsimp only [Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app] at hs
  change (((Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (pullbackPushforwardAdjunction f)).hom.app (unit Y)).app (f ⁻¹ᵁ W)
      (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app (unit Y)).app W r) =
      pullbackSection f (M := unit Y) r at hs
  rw [← normalized_adjunction_eq, tensor_unit_section] at hs
  unfold boundaryPullbackComparison
  change (pullbackObjUnitIso f).hom.app (f ⁻¹ᵁ W)
    ((((Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
      (pullbackPushforwardAdjunction f)).hom.app (unit Y)).app (f ⁻¹ᵁ W)
        (tensorPullbackSection f (unit Y) W r)) = _
  rw [← normalized_adjunction_eq] at *
  rw [hs, pullbackObjUnitIso_hom_app_pullbackSection]

private theorem unit_hom_ext_at {X : Scheme.{u}} {N : X.Modules}
    {a b : unit X ⟶ N} (W : X.Opens) (hW : W = ⊤)
    (h : a.app W (1 : Γ(X, W)) = b.app W (1 : Γ(X, W))) : a = b := by
  subst W
  exact unit_hom_ext h

private noncomputable def sectionAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (W : Y.Opens) (O : X.Opens) (hO : O ≤ f ⁻¹ᵁ W)
    (m : Γ(M, W)) : Γ((tensorPullback f).obj M, O) :=
  ((tensorPullback f).obj M).presheaf.map (homOfLE hO).op
    (tensorPullbackSection f M W m)

private theorem sectionAt_self {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (W : Y.Opens) (m : Γ(M, W)) :
    sectionAt f M W (f ⁻¹ᵁ W) le_rfl m = tensorPullbackSection f M W m := by
  unfold sectionAt
  exact congrArg (fun k ↦ k (tensorPullbackSection f M W m))
    (((tensorPullback f).obj M).presheaf.map_id (op (f ⁻¹ᵁ W)))

private theorem sectionAt_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (g : M ⟶ N) (W : Y.Opens)
    (O : X.Opens) (hO : O ≤ f ⁻¹ᵁ W) (m : Γ(M, W)) :
    ((tensorPullback f).map g).app O (sectionAt f M W O hO m) =
      sectionAt f N W O hO (g.app W m) := by
  unfold sectionAt
  rw [Hom.app_presheaf_map, tensor_section_map]

private theorem sectionAt_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) {W W' : Y.Opens} (i : W' ⟶ W)
    (O : X.Opens) (hO : O ≤ f ⁻¹ᵁ W') (m : Γ(M, W)) :
    sectionAt f M W' O hO (M.presheaf.map i.op m) =
      sectionAt f M W O (hO.trans (f.preimage_mono (leOfHom i))) m := by
  unfold sectionAt
  rw [tensor_section_restrict, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private theorem sectionAt_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (j : X ⟶ Z) (e : f ≫ g = j) (M : Z.Modules) (W : Z.Opens)
    (O : X.Opens) (hO : O ≤ (f ≫ g) ⁻¹ᵁ W) (hj : O ≤ j ⁻¹ᵁ W)
    (m : Γ(M, W)) :
    (((tensorPullbackSectionComp f g).inv.app M ≫
      (eqToIso (congrArg (fun t ↦ (tensorPullback t).obj M) e)).hom).app O)
      (sectionAt f ((tensorPullback g).obj M) (g ⁻¹ᵁ W) O hO
        (tensorPullbackSection g M W m)) = sectionAt j M W O hj m := by
  subst j
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]
  unfold sectionAt
  exact (Hom.app_presheaf_map ((tensorPullbackSectionComp f g).inv.app M)
    (homOfLE hO) (tensorPullbackSection f ((tensorPullback g).obj M) (g ⁻¹ᵁ W)
      (tensorPullbackSection g M W m))).trans
        (congrArg (((tensorPullback (f ≫ g)).obj M).presheaf.map (homOfLE hj).op)
          (tensor_comp_section f g M W m))

private theorem sectionAt_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W : Y.Opens) (O : X.Opens) (hO : O ≤ f ⁻¹ᵁ W) :
    (((boundaryPullbackComparison f).app (unit Y) ≪≫ pullbackObjUnitIso f).hom).app O
      (sectionAt f (unit Y) W O hO (1 : Γ(Y, W))) = (1 : Γ(X, O)) := by
  unfold sectionAt
  rw [Hom.app_presheaf_map, tensor_unit_comparison_section]
  change (X.presheaf.map (homOfLE hO).op) (f.app W (1 : Γ(Y, W))) = _
  simp only [map_one]

private theorem tensor_unit_hom_ext_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    {N : X.Modules} {a b : (tensorPullback f).obj (unit Y) ⟶ N}
    (W : Y.Opens) (O : X.Opens) (hO : O ≤ f ⁻¹ᵁ W) (hOt : O = ⊤)
    (h : a.app O (sectionAt f (unit Y) W O hO (1 : Γ(Y, W))) =
      b.app O (sectionAt f (unit Y) W O hO (1 : Γ(Y, W)))) : a = b := by
  let e := (boundaryPullbackComparison f).app (unit Y) ≪≫ pullbackObjUnitIso f
  apply (cancel_epi e.inv).mp
  apply unit_hom_ext_at O hOt
  have he : e.inv.app O (1 : Γ(X, O)) =
      sectionAt f (unit Y) W O hO (1 : Γ(Y, W)) := by
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app O)).injective
    have hi := congrArg (fun k ↦ k.app O (1 : Γ(X, O))) e.inv_hom_id
    change e.hom.app O (e.inv.app O (1 : Γ(X, O))) = (1 : Γ(X, O)) at hi
    rw [hi]
    exact (sectionAt_unit f W O hO).symm
  simpa only [Hom.comp_app, ConcreteCategory.comp_apply, he] using h

private theorem hom_comp_apply {X : Scheme.{u}} {M N K : X.Modules}
    (a : M ⟶ N) (b : N ⟶ K) (O : X.Opens) (x : Γ(M, O)) :
    (a ≫ b).app O x = b.app O (a.app O x) := by
  exact congrArg (fun k ↦ k x) (Hom.comp_app (U := O) a b)

private theorem comparison_of_normalized_sections {P X Y : Scheme.{u}}
    (f : X ⟶ Y) (jV : Y ⟶ P) (jU : X ⟶ P) (e : f ≫ jV = jU)
    (L : P.Modules) (LV : Y.Modules) (LU : X.Modules)
    (qV : (tensorPullback jV).obj L ⟶ LV) (qU : (tensorPullback jU).obj L ⟶ LU)
    (C : (tensorPullback f).obj LV ⟶ LU)
    (hc : (tensorPullback f).map qV ≫ C =
      (tensorPullbackSectionComp f jV).inv.app L ≫
        (eqToIso (congrArg (fun t ↦ (tensorPullback t).obj L) e)).hom ≫ qU)
    (WV WU : P.Opens) (i : WU ⟶ WV) (sV : Γ(L, WV)) (sU : Γ(L, WU))
    (hs : sU = L.presheaf.map i.op sV) (hOt : jU ⁻¹ᵁ WU = ⊤)
    (tV : unit Y ⟶ LV) (tU : unit X ⟶ LU)
    (hgV : qV.app (jV ⁻¹ᵁ WV) (tensorPullbackSection jV L WV sV) =
      tV.app (jV ⁻¹ᵁ WV) (1 : Γ(Y, jV ⁻¹ᵁ WV)))
    (hgU : qU.app (jU ⁻¹ᵁ WU) (tensorPullbackSection jU L WU sU) =
      tU.app (jU ⁻¹ᵁ WU) (1 : Γ(X, jU ⁻¹ᵁ WU))) :
    (tensorPullback f).map tV ≫ C =
      ((boundaryPullbackComparison f).app (unit Y) ≪≫ pullbackObjUnitIso f).hom ≫ tU := by
  subst jU
  let jU := f ≫ jV
  have e : f ≫ jV = jU := rfl
  let O := jU ⁻¹ᵁ WU
  have hOUV : O ≤ (f ≫ jV) ⁻¹ᵁ WV := by
    rw [e]
    exact jU.preimage_mono (leOfHom i)
  have hOf : O ≤ f ⁻¹ᵁ (jV ⁻¹ᵁ WV) := hOUV
  let x := sectionAt f (unit Y) (jV ⁻¹ᵁ WV) O hOf (1 : Γ(Y, jV ⁻¹ᵁ WV))
  let z := sectionAt f ((tensorPullback jV).obj L) (jV ⁻¹ᵁ WV) O hOf
    (tensorPullbackSection jV L WV sV)
  let K := (tensorPullbackSectionComp f jV).inv.app L ≫
    (eqToIso (congrArg (fun t ↦ (tensorPullback t).obj L) e)).hom
  let B := ((boundaryPullbackComparison f).app (unit Y) ≪≫ pullbackObjUnitIso f).hom
  have hk : (tensorPullback f).map qV ≫ C = K ≫ qU :=
    hc.trans (Category.assoc _ _ _).symm
  apply tensor_unit_hom_ext_restrict f (jV ⁻¹ᵁ WV) O hOf hOt
  refine (hom_comp_apply ((tensorPullback f).map tV) C O x).trans ?_
  refine Eq.trans ?_ (hom_comp_apply B tU O x).symm
  refine (congrArg (C.app O)
    (sectionAt_map f tV (jV ⁻¹ᵁ WV) O hOf (1 : Γ(Y, jV ⁻¹ᵁ WV)))).trans ?_
  refine Eq.trans ?_ (congrArg (tU.app O)
    (sectionAt_unit f (jV ⁻¹ᵁ WV) O hOf)).symm
  refine (congrArg (fun t ↦ C.app O (sectionAt f LV (jV ⁻¹ᵁ WV) O hOf t))
    hgV.symm).trans ?_
  refine (congrArg (C.app O)
    (sectionAt_map f qV (jV ⁻¹ᵁ WV) O hOf
      (tensorPullbackSection jV L WV sV)).symm).trans ?_
  refine (hom_comp_apply ((tensorPullback f).map qV) C O z).symm.trans ?_
  refine (congrArg (fun k ↦ k.app O z) hk).trans ?_
  refine (hom_comp_apply K qU O z).trans ?_
  refine (congrArg (qU.app O)
    (sectionAt_comp f jV jU e L WV O hOUV (jU.preimage_mono (leOfHom i)) sV)).trans ?_
  refine (congrArg (qU.app O)
    (sectionAt_restrict jU L i O le_rfl sV).symm).trans ?_
  refine (congrArg (fun s ↦ qU.app O (sectionAt jU L WU O le_rfl s)) hs.symm).trans ?_
  exact (congrArg (qU.app O) (sectionAt_self jU L WU sU)).trans hgU

/-- A normalized generator equation, stated over arbitrary schemes so that specialization
keeps the pushforward section types abstract. -/
private def moduleSectionEquation {S P X : Scheme.{u}} (p : P ⟶ S) (j : X ⟶ P)
    (E : S.Modules) (L : P.Modules) (N : X.Modules)
    (σ : E ⟶ (pushforward p).obj L)
    (q : (tensorPullback j).obj L ⟶ N) (t : unit X ⟶ N)
    (U : S.Opens) (m : Γ(E, U)) : Prop :=
  q.app (j ⁻¹ᵁ (p ⁻¹ᵁ U))
      (tensorPullbackSection j L (p ⁻¹ᵁ U) (σ.app U m)) =
    t.app (j ⁻¹ᵁ (p ⁻¹ᵁ U)) (1 : Γ(X, j ⁻¹ᵁ (p ⁻¹ᵁ U)))

private theorem moduleSectionEquation_intro {S P X : Scheme.{u}} (p : P ⟶ S) (j : X ⟶ P)
    (E : S.Modules) (L : P.Modules) (N : X.Modules)
    (σ : E ⟶ (pushforward p).obj L)
    (q : (tensorPullback j).obj L ⟶ N) (t : unit X ⟶ N)
    (U : S.Opens) (m : Γ(E, U))
    (e : q.app (j ⁻¹ᵁ (p ⁻¹ᵁ U))
      (tensorPullbackSection j L (p ⁻¹ᵁ U) (σ.app U m)) =
    t.app (j ⁻¹ᵁ (p ⁻¹ᵁ U)) (1 : Γ(X, j ⁻¹ᵁ (p ⁻¹ᵁ U)))) :
    moduleSectionEquation p j E L N σ q t U m := e

private theorem comparison_of_module_sections {S P X Y : Scheme.{u}}
    (f : X ⟶ Y) (jV : Y ⟶ P) (jU : X ⟶ P) (e : f ≫ jV = jU)
    (p : P ⟶ S) (E : S.Modules) (L : P.Modules) (LV : Y.Modules) (LU : X.Modules)
    (σ : E ⟶ (pushforward p).obj L)
    (qV : (tensorPullback jV).obj L ⟶ LV) (qU : (tensorPullback jU).obj L ⟶ LU)
    (C : (tensorPullback f).obj LV ⟶ LU)
    (hc : (tensorPullback f).map qV ≫ C =
      (tensorPullbackSectionComp f jV).inv.app L ≫
        (eqToIso (congrArg (fun t ↦ (tensorPullback t).obj L) e)).hom ≫ qU)
    (U V : S.Opens) (i : U ⟶ V) (m : Γ(E, V)) (hOt : jU ⁻¹ᵁ (p ⁻¹ᵁ U) = ⊤)
    (tV : unit Y ⟶ LV) (tU : unit X ⟶ LU)
    (hgV : moduleSectionEquation p jV E L LV σ qV tV V m)
    (hgU : moduleSectionEquation p jU E L LU σ qU tU U (E.presheaf.map i.op m)) :
    (tensorPullback f).map tV ≫ C =
      ((boundaryPullbackComparison f).app (unit Y) ≪≫ pullbackObjUnitIso f).hom ≫ tU := by
  subst jU
  let jU := f ≫ jV
  have e : f ≫ jV = jU := rfl
  have hs := Hom.app_presheaf_map σ i m
  rw [pushforward_obj_presheaf_map] at hs
  exact comparison_of_normalized_sections (P := P) (X := X) (Y := Y)
    f jV jU e L LV LU qV qU C hc (p ⁻¹ᵁ V) (p ⁻¹ᵁ U)
    ((TopologicalSpace.Opens.map p.base).map i)
    (σ.app V m) (σ.app U (E.presheaf.map i.op m)) hs hOt tV tU hgV hgU

attribute [local irreducible] moduleSectionEquation Proj.twist Proj.unitToTwist
  Scheme.GradedAlgebraData.relProjHom pullbackObjUnitIso

private theorem relative_proj_chart_top {S : Scheme.{u}} (A : S.GradedAlgebraData)
    (U : S.affineOpens) : A.relProjι U ⁻¹ᵁ (A.relProjHom ⁻¹ᵁ U.1) = ⊤ :=
  (congrArg (fun W ↦ A.relProjι U ⁻¹ᵁ W) (A.relProjHom_preimage U)).trans
    (Scheme.Hom.preimage_opensRange (A.relProjι U))

private theorem comparison_of_relative_proj_sections {S : Scheme.{u}}
    (A : S.GradedAlgebraData) (E : S.Modules) (L : A.relProj.Modules)
    (U V : S.affineOpens) (h : U ≤ V)
    (LV : (A.relProjFunctor.obj V).Modules) (LU : (A.relProjFunctor.obj U).Modules)
    (σ : E ⟶ (pushforward A.relProjHom).obj L)
    (qV : (@tensorPullback (A.relProjFunctor.obj V) A.relProj (A.relProjι V)).obj L ⟶ LV)
    (qU : (@tensorPullback (A.relProjFunctor.obj U) A.relProj (A.relProjι U)).obj L ⟶ LU)
    (C : (tensorPullback (A.relProjFunctor.map (homOfLE h))).obj LV ⟶ LU)
    (hc : (tensorPullback (A.relProjFunctor.map (homOfLE h))).map qV ≫ C =
      (tensorPullbackSectionComp (A.relProjFunctor.map (homOfLE h))
        (A.relProjι V)).inv.app L ≫
      (eqToIso (congrArg (fun t ↦ (tensorPullback t).obj L)
        (A.relProjFunctor_map_relProjι (homOfLE h)))).hom ≫ qU)
    (m : Γ(E, V.1)) (tV : unit (A.relProjFunctor.obj V) ⟶ LV)
    (tU : unit (A.relProjFunctor.obj U) ⟶ LU)
    (hgV : moduleSectionEquation (X := A.relProjFunctor.obj V)
      A.relProjHom (A.relProjι V) E L LV σ qV tV V.1 m)
    (hgU : moduleSectionEquation (X := A.relProjFunctor.obj U)
      A.relProjHom (A.relProjι U) E L LU σ qU tU U.1
      (E.presheaf.map (homOfLE (X := S.Opens) h).op m)) :
    (tensorPullback (A.relProjFunctor.map (homOfLE h))).map tV ≫ C =
      ((boundaryPullbackComparison (A.relProjFunctor.map (homOfLE h))).app (unit _) ≪≫
        pullbackObjUnitIso (A.relProjFunctor.map (homOfLE h))).hom ≫ tU := by
  exact comparison_of_module_sections (S := S) (P := A.relProj)
    (X := A.relProjFunctor.obj U) (Y := A.relProjFunctor.obj V)
    (A.relProjFunctor.map (homOfLE h)) (A.relProjι V) (A.relProjι U)
    (A.relProjFunctor_map_relProjι (homOfLE h)) A.relProjHom E L LV LU σ qV qU C hc U.1 V.1
        (homOfLE h) m
    (relative_proj_chart_top A U) tV tU hgV hgU

private theorem compatibility_on_generator
    {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
    (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (U V : S.affineOpens) (h : U ≤ V)
    (c : AffineComparison E D U V h) :
    ∀ (m : E.val.obj (op V.1))
      (hm : SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1)) m ∈
        (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V 1),
      (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map (homOfLE h))).map
          (Proj.unitToTwist hm) ≫ c.comparison.hom =
        ((Scheme.Modules.boundaryPullbackComparison
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map
              (homOfLE h))).app (Scheme.Modules.unit _) ≪≫
          Scheme.Modules.pullbackObjUnitIso
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map
              (homOfLE h))).hom ≫
        Proj.unitToTwist
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).res h |>.map_mem hm) := by
  intro m hm
  -- Keep the chart maps and sections explicit here. Local aliases make kernel comparison
  -- with the stated conclusion unfold the large pullback constructions.
  have hm' : SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) (E.presheaf.map (homOfLE (X :=
      S.Opens) h).op m) ∈
      (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 1 := by
    change _ ∈ (SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1))).range ^ 1
    simpa only [pow_one] using LinearMap.mem_range_self
      (SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1))) (E.presheaf.map (homOfLE (X := S.Opens)
          h).op m)
  have hr : (SymmetricAlgebraSheaf.gradedAlgebraData E).res h (SymmetricAlgebra.ι Γ(S, V.1)
      (E.val.obj (op V.1)) m) =
      SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) (E.presheaf.map (homOfLE (X := S.Opens)
          h).op m) :=
    SymmetricAlgebraSheaf.restriction_ι E (homOfLE (X := S.Opens) h).op m
  have hgrade : (⟨SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) (E.presheaf.map (homOfLE (X :=
      S.Opens) h).op m), hm'⟩ :
      (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 1) =
      ⟨(SymmetricAlgebraSheaf.gradedAlgebraData E).res h (SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj
          (op V.1)) m),
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).res h).map_mem hm⟩ := Subtype.ext hr.symm
  have hu := congrArg (fun b : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 1 ↦
    Proj.unitToTwist (𝒜 := (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
      (d := 1) b.property) hgrade
  have H := comparison_of_relative_proj_sections (SymmetricAlgebraSheaf.gradedAlgebraData E) E
      D.line U V h
    (Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) 1) (Proj.twist
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) 1)
    ((tensorPullbackSectionAdjunction (SymmetricAlgebraSheaf.gradedAlgebraData
        E).relProjHom).homEquiv E D.line D.quotient)
    (D.chart V).hom (D.chart U).hom c.comparison.hom c.chart_compatibility m (Proj.unitToTwist (𝒜
        := (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) hm) (Proj.unitToTwist (𝒜 :=
        (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) hm')
    (moduleSectionEquation_intro (X := (SymmetricAlgebraSheaf.gradedAlgebraData
        E).relProjFunctor.obj V)
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι V) E D.line _ _
      (D.chart V).hom (Proj.unitToTwist (𝒜 := (SymmetricAlgebraSheaf.gradedAlgebraData E).grading
          V) hm) V.1 m (D.generator V m hm))
    (moduleSectionEquation_intro (X := (SymmetricAlgebraSheaf.gradedAlgebraData
        E).relProjFunctor.obj U)
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U) E D.line _ _
      (D.chart U).hom (Proj.unitToTwist (𝒜 := (SymmetricAlgebraSheaf.gradedAlgebraData E).grading
          U) hm') U.1 _ (D.generator U (E.presheaf.map (homOfLE (X := S.Opens) h).op m) hm'))
  have hu' := congrArg (fun t ↦
    ((boundaryPullbackComparison ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map
        (homOfLE h))).app (unit _) ≪≫ pullbackObjUnitIso ((SymmetricAlgebraSheaf.gradedAlgebraData
        E).relProjFunctor.map (homOfLE h))).hom ≫ t) hu
  exact H.trans hu'

/-- The affine comparison carries every normalized degree-one section to its
restriction.  Source: Stacks, Tags 01NR, 01OB and 01N2.
(blueprint: lem-trf-symmetric-proj-section-compatibility).

Proof: every degree-one symmetric element is iota(m). Use the chart normalization
of the adjoint of D.quotient on m over V. Pullback naturality and the chart comparison
carry it to the same adjoint section over U, by naturality of that sheaf morphism.
The chart normalization over U identifies this with unitToTwist(iota(res(m))).
The normalized adjunction comparison carries the pulled-back unit to 1, and this
section determines a morphism from the pulled-back structure sheaf. -/
theorem section_compatibility_of_affine_comparison
    {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
    (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (U V : S.affineOpens) (h : U ≤ V)
    (c : AffineComparison E D U V h) :
    ∀ (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).obj V)
      (ha : a ∈ (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V 1),
      (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map (homOfLE h))).map
          (Proj.unitToTwist ha) ≫ c.comparison.hom =
        ((Scheme.Modules.boundaryPullbackComparison
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map
              (homOfLE h))).app (Scheme.Modules.unit _) ≪≫
          Scheme.Modules.pullbackObjUnitIso
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map
              (homOfLE h))).hom ≫
        Proj.unitToTwist
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).res h |>.map_mem ha) := by
  intro a ha
  have hmem : a ∈ (SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1))).range := by
    have hmem := ha
    change a ∈ (SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1))).range ^ 1 at hmem
    simpa only [pow_one] using hmem
  obtain ⟨m, rfl⟩ := hmem
  exact compatibility_on_generator E D U V h c m ha

end AlgebraicGeometry.SymmetricProjTautologicalCharts
