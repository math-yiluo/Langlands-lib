/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientChartInverseData
import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit

/-! # Normalized coefficients on a pulled tautological generator chart

## References

* Stacks Project, Constructions, Tags 01OA and 01O4
* Stacks Project, Constructions, Tags 01OA and 01O4, the normalized tautological quotient on a
  standard affine chart and its compatibility with pullback
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProjectiveBundleQuotientGeometry

open Scheme.Modules

attribute [local irreducible] tensorPullback tensorPullbackObj tensorPullbackSection
  SymmetricAlgebraSheaf.gradedAlgebraData Scheme.GradedAlgebraData.relProj
  Scheme.GradedAlgebraData.relProjHom Scheme.GradedAlgebraData.relProjι Proj.twist

private theorem tensor_unit_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) :
    ((tensorPullbackSectionAdjunction f).unit.app M).app U s =
      tensorPullbackSection f M U s :=
  (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction f)).1 M U s

private theorem tensor_section_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (q : M ⟶ N) (U : Y.Opens) (s : Γ(M, U)) :
    ((tensorPullback f).map q).app (f ⁻¹ᵁ U) (tensorPullbackSection f M U s) =
      tensorPullbackSection f N U (q.app U s) := by
  have H := congrArg (fun t ↦ t.app U s)
    ((tensorPullbackSectionAdjunction f).unit.naturality q).symm
  change ((tensorPullback f).map q).app (f ⁻¹ᵁ U)
    (((tensorPullbackSectionAdjunction f).unit.app M).app U s) =
      ((tensorPullbackSectionAdjunction f).unit.app N).app U (q.app U s) at H
  simpa only [tensor_unit_section] using H

private theorem tensor_section_res {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) {U V : Y.Opens} (h : V ≤ U) (s : Γ(M, U)) :
    tensorPullbackSection f M V (M.presheaf.map (homOfLE h).op s) =
      ((tensorPullback f).obj M).presheaf.map (homOfLE (f.preimage_mono h)).op
        (tensorPullbackSection f M U s) := by
  rw [← tensor_unit_section, ← tensor_unit_section]
  exact Hom.app_presheaf_map ((tensorPullbackSectionAdjunction f).unit.app M)
    (homOfLE h) s

private theorem tensor_section_smul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (r : Γ(Y, U)) (s : Γ(M, U)) :
    tensorPullbackSection f M U (r • s) =
      f.app U r • tensorPullbackSection f M U s := by
  rw [← tensor_unit_section, ← tensor_unit_section]
  exact Hom.app_smul ((tensorPullbackSectionAdjunction f).unit.app M) r s

private noncomputable def sectionComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensorPullback f ≅ pullback f :=
  (tensorPullbackSectionAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)

private theorem sectionComparison_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) :
    ((sectionComparison f).hom.app M).app (f ⁻¹ᵁ U)
      (tensorPullbackSection f M U s) = pullbackSection f s := by
  have H := congrArg (fun t ↦ t.app U s)
    ((tensorPullbackSectionAdjunction f).unit_leftAdjointUniq_hom_app
      (pullbackPushforwardAdjunction f) M)
  change ((sectionComparison f).hom.app M).app (f ⁻¹ᵁ U)
    (((tensorPullbackSectionAdjunction f).unit.app M).app U s) = _ at H
  rw [tensor_unit_section] at H
  exact H

private theorem tensor_section_free {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) (hs : IsFreeGenerator s) :
    IsFreeGenerator (tensorPullbackSection f M U s) := by
  have H := hs.pullback_unit_app f
  have H' := H.app_of_bijective ((sectionComparison f).inv.app M)
    (fun V _ ↦ ConcreteCategory.bijective_of_isIso _)
  have He := sectionComparison_section f M U s
  have Hi := congrArg (((sectionComparison f).inv.app M).app (f ⁻¹ᵁ U)) He
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app] at Hi
  simp only [Iso.hom_inv_id_app, Hom.id_app, ConcreteCategory.id_apply] at Hi
  exact Hi ▸ H'

private theorem tensor_section_injective {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) (U : Y.Opens) (hU : U ≤ j.opensRange) :
    Function.Injective (tensorPullbackSection j M U) := by
  intro s t h
  apply (bijective_pullbackUnit_app_of_isOpenImmersion j M hU).injective
  have H := congrArg (((sectionComparison j).hom.app M).app (j ⁻¹ᵁ U)) h
  rw [sectionComparison_section, sectionComparison_section] at H
  exact H

private theorem tensor_section_free_descent {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) (U : Y.Opens) (hU : U ≤ j.opensRange)
    (s : Γ(M, U)) (hs : IsFreeGenerator (tensorPullbackSection j M U s)) :
    IsFreeGenerator s := by
  intro V hV
  have hVr := hV.trans hU
  have := j.isIso_app V hVr
  have hr := ConcreteCategory.bijective_of_isIso (j.app V)
  have hm : Function.Bijective (tensorPullbackSection j M V) := by
    have hb : Function.Bijective (fun x : Γ(M, V) ↦ pullbackSection j x) :=
      bijective_pullbackUnit_app_of_isOpenImmersion j M hVr
    have hc := ConcreteCategory.bijective_of_isIso
      (((sectionComparison j).hom.app M).app (j ⁻¹ᵁ V))
    have heq : (fun x ↦ pullbackSection j (M := M) (U := V) x) =
        (((sectionComparison j).hom.app M).app (j ⁻¹ᵁ V)) ∘
          tensorPullbackSection j M V := funext (fun x ↦ (sectionComparison_section j M V x).symm)
    rw [heq] at hb
    exact (Function.Bijective.of_comp_iff' hc _).mp hb
  have H (r : Γ(Y, V)) :
      tensorPullbackSection j M V (r • M.presheaf.map (homOfLE hV).op s) =
        j.app V r • ((tensorPullback j).obj M).presheaf.map
          (homOfLE (j.preimage_mono hV)).op (tensorPullbackSection j M U s) := by
    rw [tensor_section_smul]
    congr 1
    exact tensor_section_res j M hV s
  constructor
  · intro r t h
    apply hr.injective
    apply (hs (j ⁻¹ᵁ V) (j.preimage_mono hV)).injective
    exact (H r).symm.trans ((congrArg (tensorPullbackSection j M V) h).trans (H t))
  · intro x
    obtain ⟨r, he⟩ := (hs (j ⁻¹ᵁ V) (j.preimage_mono hV)).surjective
      (tensorPullbackSection j M V x)
    obtain ⟨t, rfl⟩ := hr.surjective r
    exact ⟨t, hm.injective ((H t).trans he)⟩

private theorem tensor_comp_section {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (s : Γ(M, U)) :
    ((tensorPullbackSectionComp g f).hom.app M).app ((g ≫ f) ⁻¹ᵁ U)
      (tensorPullbackSection (g ≫ f) M U s) =
      tensorPullbackSection g ((tensorPullback f).obj M) (f ⁻¹ᵁ U)
        (tensorPullbackSection f M U s) := by
  have H := congrArg (fun t ↦ t.app U s)
    ((tensorPullbackSectionAdjunction (g ≫ f)).unit_leftAdjointUniq_hom_app
      (((tensorPullbackSectionAdjunction f).comp (tensorPullbackSectionAdjunction g)).ofNatIsoRight
        (pushforwardComp g f)) M)
  change ((tensorPullbackSectionComp g f).hom.app M).app ((g ≫ f) ⁻¹ᵁ U)
    (((tensorPullbackSectionAdjunction (g ≫ f)).unit.app M).app U s) =
    ((tensorPullbackSectionAdjunction g).unit.app ((tensorPullback f).obj M)).app (f ⁻¹ᵁ U)
      (((tensorPullbackSectionAdjunction f).unit.app M).app U s) at H
  simpa only [tensor_unit_section] using H

private theorem unit_section_res {X : Scheme.{u}} {M : X.Modules}
    (φ : unit X ⟶ M) {U V : X.Opens} (h : V ≤ U) :
    M.presheaf.map (homOfLE h).op (φ.app U (unitSectionsEquiv U 1)) =
      φ.app V (unitSectionsEquiv V 1) := by
  rw [← Hom.app_presheaf_map]
  apply congrArg (φ.app V)
  exact (presheaf_map_unitSectionsEquiv (homOfLE h) 1).trans
    (congrArg (unitSectionsEquiv V) (_root_.map_one (X.presheaf.map (homOfLE h).op).hom))

private theorem unit_section_relation {X : Scheme.{u}} {M : X.Modules}
    (φ ψ : unit X ⟶ M) {U V W : X.Opens} (h : V ≤ U) (hW : W ≤ V)
    (r : Γ(X, V))
    (H : M.presheaf.map (homOfLE h).op (φ.app U (unitSectionsEquiv U 1)) =
      r • M.presheaf.map (homOfLE h).op (ψ.app U (unitSectionsEquiv U 1))) :
    φ.app W (unitSectionsEquiv W 1) =
      X.presheaf.map (homOfLE hW).op r • ψ.app W (unitSectionsEquiv W 1) := by
  have H' := presheaf_map_homOfLE_eq_smul h hW H
  rw [unit_section_res, unit_section_res] at H'
  exact H'

private theorem tautologicalGenerator_eq {S : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E) (U : S.affineOpens)
    (v : Γ(E, U.1)) :
    tautologicalGenerator D U v = D.quotient.app
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
      (tensorPullbackSection (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
        E U.1 v) := by
  unfold tautologicalGenerator
  rw [Adjunction.homEquiv_unit, Hom.comp_app]
  exact congrArg (D.quotient.app _) (tensor_unit_section _ E U.1 v)

private theorem pulledQuotient_section {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (D : TautologicalQuotient E)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h)
    (U : S.affineOpens) (V : T.Opens) (hVU : V ≤ h ⁻¹ᵁ U.1)
    (hVa : V ≤ a ⁻¹ᵁ
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
    (v : Γ(E, U.1)) :
    (pulledQuotient D h a ha).app V
      (((tensorPullback h).obj E).val.map (homOfLE hVU).op
        (tensorPullbackSection h E U.1 v)) =
      pulledTautologicalGenerator D a U V hVa v := by
  subst h
  erw [Hom.app_presheaf_map]
  unfold pulledTautologicalGenerator
  apply congrArg (((tensorPullback a).obj D.line).presheaf.map (homOfLE hVa).op)
  change ((tensorPullback a).map D.quotient).app
    (a ⁻¹ᵁ ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
    (((tensorPullbackSectionComp a
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E).app _
        (tensorPullbackSection (a ≫
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom) E U.1 v)) = _
  exact (congrArg (((tensorPullback a).map D.quotient).app _)
    (tensor_comp_section a (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
      E U.1 v)).trans ((tensor_section_map a D.quotient _ _).trans
        (congrArg (tensorPullbackSection a D.line _) (tautologicalGenerator_eq D U v).symm))

private theorem chart_section {S : Scheme.{u}} {E : S.Modules} [E.IsQuasicoherent]
    (D : TautologicalQuotient E) (U : S.affineOpens)
    (O : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Opens)
    (hO : O ≤ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
    (v : Γ(E, U.1)) :
    (D.chart U).hom.app ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ O)
      (tensorPullbackSection ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)
        D.line O (D.line.presheaf.map (homOfLE hO).op (tautologicalGenerator D U v))) =
      (Proj.unitToTwist (quotientSymmetricGenerator E U v).property).app
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ O)
        (1 : Γ(Proj ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U),
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ O)) := by
  rw [tensor_section_res, Hom.app_presheaf_map]
  erw [D.generator U v (quotientSymmetricGenerator E U v).property]
  exact unit_section_res (Proj.unitToTwist (quotientSymmetricGenerator E U v).property) _

private theorem chart_section_free {S : Scheme.{u}} {E : S.Modules} [E.IsQuasicoherent]
    (D : TautologicalQuotient E) (U : S.affineOpens) (m : Γ(E, U.1))
    (O : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Opens)
    (hO : O ≤ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
    (hB : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ O ≤
      Proj.basicOpen ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
        (quotientSymmetricGenerator E U m).val) :
    IsFreeGenerator (D.line.presheaf.map (homOfLE hO).op (tautologicalGenerator D U m)) := by
  apply tensor_section_free_descent ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)
    D.line O (by rwa [← Scheme.GradedAlgebraData.relProjHom_preimage])
  have H := (unit_section_res
    (Proj.unitToTwist (quotientSymmetricGenerator E U m).property) hB) ▸
    ((Proj.isFreeGenerator_unitToTwist (quotientSymmetricGenerator E U m).property).map hB)
  erw [← chart_section D U O hO m] at H
  have H' := H.app_of_bijective (D.chart U).inv
    (fun V _ ↦ ConcreteCategory.bijective_of_isIso _)
  simpa only [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id, Hom.id_app,
    ConcreteCategory.id_apply] using H'

private theorem chart_section_relation {S : Scheme.{u}} {E : S.Modules} [E.IsQuasicoherent]
    (D : TautologicalQuotient E) (U : S.affineOpens) (m v : Γ(E, U.1))
    (O : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Opens)
    (hO : O ≤ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
    (hB : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ O ≤
      Proj.basicOpen ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
        (quotientSymmetricGenerator E U m).val)
    (r : Γ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProj, O))
    (hr : ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U).app O r =
      (Proj ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)).presheaf.map
        (homOfLE hB).op
        (Proj.awayToSection ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
          (quotientSymmetricGenerator E U m).val
          (degreeOneQuotientFraction (SymmetricAlgebraSheaf.gradedAlgebraData E) U
            (quotientSymmetricGenerator E U m) 1 (quotientSymmetricGenerator E U v)))) :
    D.line.presheaf.map (homOfLE hO).op (tautologicalGenerator D U v) =
      r • D.line.presheaf.map (homOfLE hO).op (tautologicalGenerator D U m) := by
  apply tensor_section_injective ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)
    D.line O (by rwa [← Scheme.GradedAlgebraData.relProjHom_preimage])
  apply (ConcreteCategory.bijective_of_isIso
    ((D.chart U).hom.app
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ O))).injective
  rw [tensor_section_smul, Hom.app_smul, chart_section, chart_section, hr]
  have H := unit_section_relation
    (Proj.unitToTwist (quotientSymmetricGenerator E U v).property)
    (Proj.unitToTwist (quotientSymmetricGenerator E U m).property) le_top hB _
    (Proj.map_unitToTwist_eq_smul (quotientSymmetricGenerator E U v).property
      (quotientSymmetricGenerator E U m).property (by
        simpa only [one_smul] using (quotientSymmetricGenerator E U v).property))
  exact H

private theorem pulled_generator_restrict {S T : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj) (U : S.affineOpens)
    (O : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Opens)
    (hO : O ≤ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
    (V : T.Opens) (hVO : V ≤ a ⁻¹ᵁ O)
    (hVa : V ≤ a ⁻¹ᵁ
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
    (m : Γ(E, U.1)) :
    pulledTautologicalGenerator D a U V hVa m =
      ((tensorPullback a).obj D.line).presheaf.map (homOfLE hVO).op
        (tensorPullbackSection a D.line O
          (D.line.presheaf.map (homOfLE hO).op (tautologicalGenerator D U m))) := by
  rw [tensor_section_res, presheaf_map_map_apply]
  rfl

private theorem pulled_generator_free {S T : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj) (U : S.affineOpens)
    (m : Γ(E, U.1)) (O : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Opens)
    (hO : O ≤ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
    (hB : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ O ≤
      Proj.basicOpen ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
        (quotientSymmetricGenerator E U m).val)
    (V : T.Opens) (hVO : V ≤ a ⁻¹ᵁ O)
    (hVa : V ≤ a ⁻¹ᵁ
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)) :
    IsFreeGenerator (pulledTautologicalGenerator D a U V hVa m) := by
  rw [pulled_generator_restrict D a U O hO V hVO hVa m]
  exact (tensor_section_free a D.line O _ (chart_section_free D U m O hO hB)).map hVO

private theorem pulled_generator_smul {S T : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj) (U : S.affineOpens)
    (m v : Γ(E, U.1)) (O : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Opens)
    (hO : O ≤ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
    (r : Γ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProj, O))
    (hr : D.line.presheaf.map (homOfLE hO).op (tautologicalGenerator D U v) =
      r • D.line.presheaf.map (homOfLE hO).op (tautologicalGenerator D U m))
    (V : T.Opens) (hVO : V ≤ a ⁻¹ᵁ O)
    (hVa : V ≤ a ⁻¹ᵁ
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)) :
    pulledTautologicalGenerator D a U V hVa v =
      a.appLE O V hVO r • pulledTautologicalGenerator D a U V hVa m := by
  rw [pulled_generator_restrict D a U O hO V hVO hVa v,
    pulled_generator_restrict D a U O hO V hVO hVa m]
  rw [hr, tensor_section_smul, Scheme.Modules.map_smul]
  rfl

private theorem pulled_quotient_of_relation {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (D : TautologicalQuotient E)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h)
    (U : S.affineOpens) (m v : Γ(E, U.1))
    (O : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Opens)
    (hO : O ≤ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
    (r : Γ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProj, O))
    (hr : D.line.presheaf.map (homOfLE hO).op (tautologicalGenerator D U v) =
      r • D.line.presheaf.map (homOfLE hO).op (tautologicalGenerator D U m))
    (V : T.Opens) (hVO : V ≤ a ⁻¹ᵁ O) (hVU : V ≤ h ⁻¹ᵁ U.1)
    (hVa : V ≤ a ⁻¹ᵁ
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
    (c : Γ(T, V)) (hc : a.appLE O V hVO r = c) :
    (pulledQuotient D h a ha).app V
      (((tensorPullback h).obj E).val.map (homOfLE hVU).op
        (tensorPullbackSection h E U.1 v)) =
      c • pulledTautologicalGenerator D a U V hVa m := by
  exact (pulledQuotient_section h E D a ha U V hVU hVa v).trans
    ((pulled_generator_smul D a U m v O hO r hr V hVO hVa).trans
      (congrArg (fun t ↦ t • pulledTautologicalGenerator D a U V hVa m) hc))

private theorem inclusion_appLE {X : Scheme.{u}} (U : X.Opens) :
    U.ι.appLE U ⊤ (by simp) = U.topIso.inv := by
  rw [Scheme.Opens.ι_appLE]
  rfl

private theorem appLE_hom_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V e' := by
  subst g
  rfl

private theorem appLE_factor {X Y Z : Scheme.{u}} (a : X ⟶ Z)
    (W : X.Opens) (j : Y ⟶ Z) [IsOpenImmersion j] (B : Y.Opens)
    (b : W.toScheme ⟶ B.toScheme)
    (h : W.ι ≫ a = b ≫ B.ι ≫ j) (hW : W ≤ a ⁻¹ᵁ (j ''ᵁ B)) :
    a.appLE (j ''ᵁ B) W hW =
      (j.appIso B).hom ≫ B.topIso.inv ≫ b.appTop ≫ W.topIso.hom := by
  apply (cancel_mono W.topIso.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← inclusion_appLE, Scheme.Hom.appLE_comp_appLE]
  trans (b ≫ B.ι ≫ j).appLE (j ''ᵁ B) ⊤ (by
    intro x _
    exact ⟨_, (b x).property, rfl⟩)
  · exact appLE_hom_congr h _ _ _ _
  rw [j.appIso_hom', ← inclusion_appLE]
  rw [Scheme.Hom.appLE_comp_appLE_assoc]
  have he : ⊤ ≤ (B.ι ≫ j) ⁻¹ᵁ (j ''ᵁ B) := by
    intro x _
    exact ⟨_, x.property, rfl⟩
  trans (B.ι ≫ j).appLE (j ''ᵁ B) ⊤ he ≫ b.appLE ⊤ ⊤ (by simp)
  · exact (Scheme.Hom.appLE_comp_appLE b (B.ι ≫ j) (j ''ᵁ B) ⊤ ⊤ _ _).symm
  exact congrArg ((B.ι ≫ j).appLE (j ''ᵁ B) ⊤ he ≫ ·) b.app_eq_appLE.symm

private theorem appIso_inv_apply {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (B : X.Opens) (r : Γ(X, B)) :
    j.app (j ''ᵁ B) ((j.appIso B).inv r) =
      X.presheaf.map (homOfLE (j.preimage_image_eq B).le).op r := by
  exact ConcreteCategory.congr_hom (j.appIso_inv_app B) r

private theorem chart_base_image_le {S : Scheme.{u}} (A : S.GradedAlgebraData)
    (U : S.affineOpens) (e : A.grading U 1) :
    A.relProjι U ''ᵁ Proj.basicOpen (A.grading U) e.val ≤ A.relProjHom ⁻¹ᵁ U.1 := by
  rw [A.relProjHom_preimage]
  exact (A.relProjι U).image_le_opensRange _

private theorem chart_image_le {S T : Scheme.{u}} (A : S.GradedAlgebraData)
    (a : T ⟶ A.relProj) (U : S.affineOpens) (W : T.Opens) (e : A.grading U 1)
    (k : W.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away (A.grading U) e.val)))
    (hk : W.ι ≫ a = k ≫ Proj.awayι (A.grading U) e.val e.property
      (by decide : 0 < (1 : ℕ)) ≫ A.relProjι U) :
    W ≤ a ⁻¹ᵁ (A.relProjι U ''ᵁ Proj.basicOpen (A.grading U) e.val) := by
  intro x hx
  have H := congrArg (fun f ↦ f ⟨x, hx⟩) hk
  change a x = A.relProjι U (Proj.awayι (A.grading U) e.val e.property
    (by decide : 0 < (1 : ℕ)) (k ⟨x, hx⟩)) at H
  change a x ∈ A.relProjι U ''ᵁ Proj.basicOpen (A.grading U) e.val
  rw [H]
  refine ⟨_, ?_, rfl⟩
  exact (le_of_eq (Proj.opensRange_awayι (A.grading U) e.val e.property
    (by decide : 0 < (1 : ℕ)))) ⟨_, rfl⟩

private theorem chart_coefficient {S T : Scheme.{u}} (A : S.GradedAlgebraData)
    (a : T ⟶ A.relProj) (U : S.affineOpens) (W : T.Opens) (e : A.grading U 1)
    (k : W.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away (A.grading U) e.val)))
    (hk : W.ι ≫ a = k ≫ Proj.awayι (A.grading U) e.val e.property
      (by decide : 0 < (1 : ℕ)) ≫ A.relProjι U)
    (hWO : W ≤ a ⁻¹ᵁ (A.relProjι U ''ᵁ Proj.basicOpen (A.grading U) e.val))
    (r : HomogeneousLocalization.Away (A.grading U) e.val) :
    a.appLE (A.relProjι U ''ᵁ Proj.basicOpen (A.grading U) e.val) W hWO
      (((A.relProjι U).appIso (Proj.basicOpen (A.grading U) e.val)).inv
        (Proj.awayToSection (A.grading U) e.val r)) =
      ((Scheme.ΓSpecIso _).inv ≫ k.appTop ≫ W.topIso.hom).hom r := by
  let B := Proj.basicOpen (A.grading U) e.val
  let j := A.relProjι U
  let c := Proj.basicOpenIsoSpec (A.grading U) e.val e.property
    (by decide : 0 < (1 : ℕ))
  have hc : Proj.awayToSection (A.grading U) e.val ≫ B.topIso.inv ≫ c.inv.appTop =
      (Scheme.ΓSpecIso _).inv := by
    have H := Proj.basicOpenToSpec_app_top (A.grading U) e.val
    change c.hom.appTop = _ at H
    apply (cancel_epi (Scheme.ΓSpecIso _).hom).mp
    rw [Iso.hom_inv_id]
    have Hc := congrArg (fun f ↦ f.appTop) c.inv_hom_id
    simpa only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, H, Category.assoc] using Hc
  have hfac : W.ι ≫ a = (k ≫ c.inv) ≫ B.ι ≫ j := by
    have hcι : c.inv ≫ B.ι = Proj.awayι (A.grading U) e.val e.property
        (by decide : 0 < (1 : ℕ)) :=
      Proj.basicOpenIsoSpec_inv_ι (A.grading U) e.val e.property (by decide)
    rw [Category.assoc, ← Category.assoc c.inv, hcι]
    exact hk
  have Hring : Proj.awayToSection (A.grading U) e.val ≫ (j.appIso B).inv ≫
      a.appLE (j ''ᵁ B) W hWO = (Scheme.ΓSpecIso _).inv ≫ k.appTop ≫ W.topIso.hom := by
    rw [appLE_factor a W j B (k ≫ c.inv) hfac hWO]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Scheme.Hom.comp_appTop]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ k.appTop ≫ W.topIso.hom) hc)
  exact ConcreteCategory.congr_hom Hring r

private theorem chart_scalar {S T : Scheme.{u}} (h : T ⟶ S)
    (A : S.GradedAlgebraData) (a : T ⟶ A.relProj) (ha : a ≫ A.relProjHom = h)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (e : A.grading U 1)
    (k : W.1.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away (A.grading U) e.val)))
    (hk : W.1.ι ≫ a = k ≫ Proj.awayι (A.grading U) e.val e.property
      (by decide : 0 < (1 : ℕ)) ≫ A.relProjι U) (r : Γ(S, U.1)) :
    ((Scheme.ΓSpecIso _).inv ≫ k.appTop ≫ W.1.topIso.hom).hom
      (quotientFractionScalar A U e.val r) = h.appLE U.1 W.1 hWU r := by
  have Hπ : W.1.ι ≫ h = k ≫ Spec.map (CommRingCat.ofHom
      (algebraMap Γ(S, U.1) (HomogeneousLocalization.Away (A.grading U) e.val))) ≫
        U.2.isoSpec.inv ≫ U.1.ι := by
    calc
      W.1.ι ≫ h = (W.1.ι ≫ a) ≫ A.relProjHom := by rw [Category.assoc, ha]
      _ = (k ≫ Proj.awayι (A.grading U) e.val e.property
          (by decide : 0 < (1 : ℕ)) ≫ A.relProjι U) ≫ A.relProjHom :=
        congrArg (fun f ↦ f ≫ A.relProjHom) hk
      _ = _ := by
        simp only [Category.assoc, Scheme.GradedAlgebraData.relProjι_relProjHom,
          Scheme.GradedAlgebraData.toOpen_eq, Proj.awayι_toSpecOfAlgebra_assoc]
  have H : k ≫ Spec.map (CommRingCat.ofHom
      (algebraMap Γ(S, U.1) (HomogeneousLocalization.Away (A.grading U) e.val))) =
      h.resLE U.1 W.1 hWU ≫ U.2.isoSpec.hom := by
    apply (cancel_mono U.2.isoSpec.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply (cancel_mono U.1.ι).mp
    rw [Scheme.Hom.resLE_comp_ι]
    simpa only [Category.assoc] using Hπ.symm
  have hi := IsAffineOpen.isoSpec_hom_appTop U.2
  have H' := congrArg (fun f ↦ (Scheme.ΓSpecIso Γ(S, U.1)).inv ≫ f.appTop ≫
    W.1.topIso.hom) H
  simp only [Scheme.Hom.comp_appTop, Category.assoc, ← Scheme.ΓSpecIso_inv_naturality_assoc,
    hi, Scheme.Hom.resLE_app_top,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] at H'
  have H'' := congrArg (fun f ↦ f r) H'
  change W.1.topIso.hom (k.appTop ((Scheme.ΓSpecIso _).inv
    (algebraMap Γ(S, U.1) (HomogeneousLocalization.Away (A.grading U) e.val) r))) =
      h.appLE U.1 W.1 hWU r at H''
  have hr : quotientFractionScalar A U e.val r =
      algebraMap Γ(S, U.1) (HomogeneousLocalization.Away (A.grading U) e.val) r := rfl
  change W.1.topIso.hom (k.appTop ((Scheme.ΓSpecIso _).inv
    (quotientFractionScalar A U e.val r))) = _
  rw [hr]
  exact H''

/-- The tautological generator is a frame on one pulled standard chart, and the
coefficient of a quotient generator v is the pullback of iota(v)/iota(m). -/
theorem lineQuotient_pulled_chart_normalization {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (D : TautologicalQuotient E)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (hWa : W.1 ≤ a ⁻¹ᵁ
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
    (m : Γ(E, U.1))
    (k : W.1.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
      (quotientSymmetricGenerator E U m).val)))
    (hk : W.1.ι ≫ a = k ≫
      Proj.awayι ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
        (quotientSymmetricGenerator E U m).val (quotientSymmetricGenerator E U m).property
        (by decide : 0 < (1 : ℕ)) ≫
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U) :
    let κ := ((Scheme.ΓSpecIso _).inv ≫ k.appTop ≫ W.1.topIso.hom).hom
    IsFreeGenerator (pulledTautologicalGenerator D a U W.1 hWa m) ∧
      (∀ r : Γ(S, U.1),
        κ (quotientFractionScalar (SymmetricAlgebraSheaf.gradedAlgebraData E) U
          (quotientSymmetricGenerator E U m).val r) = h.appLE U.1 W.1 hWU r) ∧
      ∀ v : Γ(E, U.1),
        (pulledQuotient D h a ha).app W.1
          (((tensorPullback h).obj E).val.map (homOfLE hWU).op
            (tensorPullbackSection h E U.1 v)) =
          κ (degreeOneQuotientFraction (SymmetricAlgebraSheaf.gradedAlgebraData E) U
            (quotientSymmetricGenerator E U m) 1 (quotientSymmetricGenerator E U v)) •
              pulledTautologicalGenerator D a U W.1 hWa m := by
  let A := SymmetricAlgebraSheaf.gradedAlgebraData E
  let e := quotientSymmetricGenerator E U m
  let B := Proj.basicOpen (A.grading U) e.val
  let j := A.relProjι U
  let O := j ''ᵁ B
  have hO : O ≤ A.relProjHom ⁻¹ᵁ U.1 := chart_base_image_le A U e
  have hB : j ⁻¹ᵁ O ≤ B := (j.preimage_image_eq B).le
  have hWO : W.1 ≤ a ⁻¹ᵁ O := chart_image_le A a U W.1 e k hk
  refine ⟨?_, ?_, ?_⟩
  · exact pulled_generator_free D a U m O hO hB W.1 hWO hWa
  · intro r
    exact chart_scalar h A a ha U W hWU e k hk r
  · intro v
    have hr := appIso_inv_apply j B
      (Proj.awayToSection (A.grading U) e.val
        (degreeOneQuotientFraction A U e 1 (quotientSymmetricGenerator E U v)))
    have hrel := chart_section_relation D U m v O hO hB
      ((j.appIso B).inv (Proj.awayToSection (A.grading U) e.val
        (degreeOneQuotientFraction A U e 1 (quotientSymmetricGenerator E U v))))
      (by exact hr)
    exact pulled_quotient_of_relation h E D a ha U m v O hO _ hrel W.1 hWO hWU hWa _
      (chart_coefficient A a U W.1 e k hk hWO _)

end AlgebraicGeometry.ProjectiveBundleQuotientGeometry
