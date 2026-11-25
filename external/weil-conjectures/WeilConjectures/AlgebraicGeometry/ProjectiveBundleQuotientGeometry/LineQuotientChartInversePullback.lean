/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientChartInverseData
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientFractionKernel
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientRecoveredCharts
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientIsoCharts
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientPullbackCharts
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Functor.EpiMono

/-! # Inverse quotient charts and arbitrary pullback

## References

* Stacks Project, Constructions, Tags 01OA and 01O4
* Stacks, Constructions, Tags 01OA and 01O4
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

attribute [local instance] instModuleRestrictedSections

attribute [local irreducible] tensorPullback tensorPullbackObj tensorPullbackSection
attribute [local irreducible] pulledQuotient lineQuotientPullback

private theorem sectionAdjunction_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (m : Γ(M, U)) :
    ((tensorPullbackSectionAdjunction f).unit.app M).app U m =
      tensorPullbackSection f M U m :=
  (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction f)).1 M U m

private theorem tensorPullback_epi {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (q : M ⟶ N) [Epi q] : Epi ((tensorPullback f).map q) := by
  let : (tensorPullback f).IsLeftAdjoint := (tensorPullbackSectionAdjunction f).isLeftAdjoint
  infer_instance

private theorem pulledQuotient_epi {S T : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E) (h : T ⟶ S)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h) :
    Epi (pulledQuotient D h a ha) := by
  let : Epi D.quotient := D.surjective
  let := tensorPullback_epi a D.quotient
  unfold pulledQuotient
  infer_instance

private theorem lineQuotientPullback_epi {S T T' : Scheme.{u}} (h : T ⟶ S)
    (u : T' ⟶ T) (E : S.Modules) (L : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L) [Epi q] :
    Epi (lineQuotientPullback h u E L q) := by
  let := tensorPullback_epi u q
  unfold lineQuotientPullback
  infer_instance

private theorem tensorPullbackSection_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (v : M ⟶ N) (U : Y.Opens) (m : Γ(M, U)) :
    ((tensorPullback f).map v).app (f ⁻¹ᵁ U) (tensorPullbackSection f M U m) =
      tensorPullbackSection f N U (v.app U m) := by
  rw [← sectionAdjunction_unit, ← sectionAdjunction_unit]
  exact (congrArg (fun k ↦ k.app U m)
    ((tensorPullbackSectionAdjunction f).unit.naturality v)).symm

private theorem tensorPullbackSection_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (U : Z.Opens) (m : Γ(M, U)) :
    ((tensorPullbackSectionComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U)
        (tensorPullbackSection (f ≫ g) M U m) =
      tensorPullbackSection f ((tensorPullback g).obj M) (g ⁻¹ᵁ U)
        (tensorPullbackSection g M U m) := by
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (tensorPullbackSectionAdjunction (f ≫ g))
    (((tensorPullbackSectionAdjunction g).comp (tensorPullbackSectionAdjunction f)).ofNatIsoRight
      (pushforwardComp f g)) M
  have hv := congrArg (fun k ↦ k.app U m) hu
  simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Adjunction.comp_unit_app,
    Functor.whiskerLeft_app, pushforwardComp_hom_app_app] at hv
  change ((tensorPullbackSectionComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U)
    (((tensorPullbackSectionAdjunction (f ≫ g)).unit.app M).app U m) =
    ((tensorPullbackSectionAdjunction f).unit.app ((tensorPullback g).obj M)).app
      (g ⁻¹ᵁ U) (((tensorPullbackSectionAdjunction g).unit.app M).app U m) at hv
  calc
    _ = ((tensorPullbackSectionComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U)
        (((tensorPullbackSectionAdjunction (f ≫ g)).unit.app M).app U m) :=
      congrArg _ (sectionAdjunction_unit (f ≫ g) M U m).symm
    _ = _ := hv
    _ = _ := (sectionAdjunction_unit f _ _ _).trans
      (congrArg (tensorPullbackSection f _ _) (sectionAdjunction_unit g M U m))

private theorem tautologicalGenerator_eq {S : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E) (U : S.affineOpens)
    (m : Γ(E, U.1)) :
    tautologicalGenerator D U m =
      D.quotient.app ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
        (tensorPullbackSection (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
          E U.1 m) := by
  unfold tautologicalGenerator
  rw [Adjunction.homEquiv_apply]
  exact congrArg (D.quotient.app _)
    (sectionAdjunction_unit _ E U.1 m)

private theorem pulledQuotient_section {S T : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E) (h : T ⟶ S)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h)
    (U : S.affineOpens) (V : T.Opens) (hVU : V ≤ h ⁻¹ᵁ U.1)
    (hVa : V ≤ a ⁻¹ᵁ
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
    (m : Γ(E, U.1)) :
    (pulledQuotient D h a ha).app V
      (((tensorPullback h).obj E).presheaf.map (homOfLE hVU).op
        (tensorPullbackSection h E U.1 m)) =
      pulledTautologicalGenerator D a U V hVa m := by
  subst h
  rw [Hom.app_presheaf_map]
  unfold pulledQuotient
  simp only [eqToIso_refl, Iso.refl_inv, Category.id_comp, Hom.comp_app,
    ConcreteCategory.comp_apply]
  rw [tensorPullbackSection_comp]
  change ((tensorPullback a).obj D.line).presheaf.map (homOfLE hVa).op
    (((tensorPullback a).map D.quotient).app
      (a ⁻¹ᵁ ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1))
      (tensorPullbackSection a _ _ (tensorPullbackSection _ E U.1 m))) = _
  rw [tensorPullbackSection_naturality]
  rw [← tautologicalGenerator_eq]
  rfl

private theorem quotientGeneratorCoefficient_smul {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) (L : T.Modules) (q : (tensorPullback h).obj E ⟶ L)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l) (m : Γ(E, U.1)) :
    quotientGeneratorCoefficient h E L q U W hWU l m • l =
      q.app W.1 (((tensorPullback h).obj E).presheaf.map (homOfLE hWU).op
        (tensorPullbackSection h E U.1 m)) := by
  exact Function.invFun_eq (hl.bijective.2 _)

private theorem compatibleIso_generator {S T : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E) (h : T ⟶ S)
    (L : T.Modules) (q : (tensorPullback h).obj E ⟶ L)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (hF : F ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h)
    (θ : (tensorPullback F).obj D.line ≅ L)
    (hθ : pulledQuotient D h F hF ≫ θ.hom = q)
    (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
    (l : Γ(L, W.1)) (hl : IsFreeGenerator l) (m : Γ(E, U.1))
    (V : T.Opens) (hVW : V ≤ W.1)
    (hVF : V ≤ F ⁻¹ᵁ
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)) :
    θ.hom.app V (pulledTautologicalGenerator D F U V hVF m) =
      T.presheaf.map (homOfLE hVW).op
        (quotientGeneratorCoefficient h E L q U W hWU l m) •
          L.val.map (homOfLE hVW).op l := by
  rw [← pulledQuotient_section D h F hF U V (hVW.trans hWU) hVF m]
  change (pulledQuotient D h F hF ≫ θ.hom).app V _ = _
  rw [hθ]
  change q.app V _ = T.presheaf.map (homOfLE hVW).op
    (quotientGeneratorCoefficient h E L q U W hWU l m) •
      L.presheaf.map (homOfLE hVW).op l
  rw [← map_smul L (homOfLE hVW),
    quotientGeneratorCoefficient_smul h E L q U W hWU l hl m]
  rw [← Hom.app_presheaf_map]
  congr 1
  exact (presheaf_map_map_apply _ _ _).symm

private theorem inverseNormalization_of_compatible {S T : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E) (h : T ⟶ S)
    (L : T.Modules) (q : (tensorPullback h).obj E ⟶ L)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (hF : F ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h)
    (θ : (tensorPullback F).obj D.line ≅ L)
    (hθ : pulledQuotient D h F hF ≫ θ.hom = q) :
    InverseLineChartNormalization D h L q F θ := by
  intro U W hWU l hl m V hVW hVF
  have hs := compatibleIso_generator D h L q F hF θ hθ U W hWU l hl
  refine ⟨hs m V hVW hVF, ?_, ?_⟩
  · intro hm
    have hfree : IsFreeGenerator (T.presheaf.map (homOfLE hVW).op
        (quotientGeneratorCoefficient h E L q U W hWU l m) •
          L.val.map (homOfLE hVW).op l) := by
      obtain ⟨b, hb⟩ := hm
      rw [← hb]
      exact (hl.map hVW).units_smul b
    rw [← hs m V hVW hVF] at hfree
    have hfree' := hfree.app_hom θ.symm
    have hid (x : Γ((tensorPullback F).obj D.line, V)) :
        θ.inv.app V (θ.hom.app V x) = x := by
      exact congrArg (fun k ↦ k.app V x) θ.hom_inv_id
    change IsFreeGenerator (θ.inv.app V (θ.hom.app V
      (pulledTautologicalGenerator D F U V hVF m))) at hfree'
    rw [hid] at hfree'
    refine ⟨hfree', ?_⟩
    intro v
    rw [hs v V hVW hVF, smul_smul]
    congr 1
    rw [mul_assoc, Ring.inverse_mul_cancel _ hm, mul_one]
  · intro n hn
    apply (ConcreteCategory.bijective_of_isIso (θ.hom.app V)).injective
    rw [Hom.app_smul, hs m V hVW hVF, hs n V hVW hVF, smul_smul]
    congr 1
    rw [mul_assoc, Ring.inverse_mul_cancel _ hn, mul_one]

private theorem recoveredQuotientFrame {S T : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E) (h : T ⟶ S)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h) :
    RecoveredQuotientFrame D h a ha := by
  intro U W hWU hWa m l hl hgen
  apply hgen.smul_left_injective
  change quotientGeneratorCoefficient h E _ (pulledQuotient D h a ha) U W hWU l m • l =
    1 • l
  rw [quotientGeneratorCoefficient_smul h E _ (pulledQuotient D h a ha)
    U W hWU l hgen m, one_smul]
  rw [pulledQuotient_section D h a ha U W.1 hWU hWa m]
  exact hl.symm

private theorem commonKernelIso_exists {C : Type*} [Category C]
    [HasZeroMorphisms C] [IsNormalEpiCategory C]
    {M L L' : C} (q : M ⟶ L) (q' : M ⟶ L') [Epi q] [Epi q']
    (h : ∀ (N : C) (r : N ⟶ M), r ≫ q = 0 ↔ r ≫ q' = 0) :
    ∃ v : L ≅ L', q ≫ v.hom = q' := by
  obtain ⟨nq⟩ := IsNormalEpiCategory.normalEpiOfEpi q
  obtain ⟨nq'⟩ := IsNormalEpiCategory.normalEpiOfEpi q'
  obtain ⟨f, hf⟩ := CokernelCofork.IsColimit.desc' nq.isColimit q'
    ((h _ nq.g).mp nq.w)
  obtain ⟨g, hg⟩ := CokernelCofork.IsColimit.desc' nq'.isColimit q
    ((h _ nq'.g).mpr nq'.w)
  change q ≫ f = q' at hf
  change q' ≫ g = q at hg
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply (cancel_epi q).mp
    rw [← Category.assoc, hf, hg, Category.comp_id]
  · apply (cancel_epi q').mp
    rw [← Category.assoc, hg, hf, Category.comp_id]

private theorem modules_normalEpiCategory (T : Scheme.{u}) :
    IsNormalEpiCategory T.Modules := inferInstance

private theorem compatibleIso_of_charts {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (D : TautologicalQuotient E)
    (L : T.Modules) [L.IsInvertible] (q : (tensorPullback h).obj E ⟶ L) [Epi q]
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (hψ : ψ.ExtendsLineQuotient h E L q)
    (hc : ψ.HasQuotientFractionCharts h E L q F) :
    ∃ θ : (tensorPullback F).obj D.line ≅ L,
      pulledQuotient D h F hc.1 ≫ θ.hom = q := by
  have := pulledQuotient_epi D h F hc.1
  have := modules_normalEpiCategory T
  exact commonKernelIso_exists (pulledQuotient D h F hc.1) q
    (lineQuotient_fraction_kernel h E D L q ψ F hψ hc)

private theorem fraction_map_unique {S T : Scheme.{u}} (h : T ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (L : T.Modules) [L.IsInvertible]
    (q : (tensorPullback h).obj E ⟶ L) [Epi q]
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (hψ : ψ.ExtendsLineQuotient h E L q)
    (F G : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (hF : ψ.HasQuotientFractionCharts h E L q F)
    (hG : ψ.HasQuotientFractionCharts h E L q G) : F = G := by
  obtain ⟨ψ₀, _, hψ₀, _, F₀, _, _, _, hF₀⟩ :=
    line_quotient_homogeneous_fraction_map h E L q
  have hh := hψ₀ ψ hψ
  subst ψ₀
  exact (hF₀ F hF).trans (hF₀ G hG).symm

private theorem lineQuotientPullback_section {S T T' : Scheme.{u}}
    (h : T ⟶ S) (u : T' ⟶ T) (E : S.Modules) (L : T.Modules)
    (q : (tensorPullback h).obj E ⟶ L) (U : S.Opens) (m : Γ(E, U)) :
    (lineQuotientPullback h u E L q).app ((u ≫ h) ⁻¹ᵁ U)
      (tensorPullbackSection (u ≫ h) E U m) =
      tensorPullbackSection u L (h ⁻¹ᵁ U)
        (q.app (h ⁻¹ᵁ U) (tensorPullbackSection h E U m)) := by
  unfold lineQuotientPullback
  change ((tensorPullback u).map q).app ((u ≫ h) ⁻¹ᵁ U)
    (((tensorPullbackSectionComp u h).hom.app E).app _
      (tensorPullbackSection (u ≫ h) E U m)) = _
  rw [tensorPullbackSection_comp]
  exact tensorPullbackSection_naturality u q (h ⁻¹ᵁ U)
    (tensorPullbackSection h E U m)

private theorem tensorPullback_hom_ext {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (N : X.Modules) (v w : (tensorPullback f).obj M ⟶ N)
    (h : ∀ (U : Y.Opens) (m : Γ(M, U)),
      v.app (f ⁻¹ᵁ U) (tensorPullbackSection f M U m) =
        w.app (f ⁻¹ᵁ U) (tensorPullbackSection f M U m)) : v = w := by
  apply ((tensorPullbackSectionAdjunction f).homEquiv M N).injective
  apply hom_ext
  intro U
  ext m
  change v.app (f ⁻¹ᵁ U)
      (((tensorPullbackSectionAdjunction f).unit.app M).app U m) =
    w.app (f ⁻¹ᵁ U) (((tensorPullbackSectionAdjunction f).unit.app M).app U m)
  rw [sectionAdjunction_unit]
  exact h U m

private theorem pulledQuotient_unit {S T : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E) (h : T ⟶ S)
    (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h)
    (U : S.Opens) (V : T.Opens) (hVU : V ≤ h ⁻¹ᵁ U)
    (hVa : V ≤ a ⁻¹ᵁ
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U))
    (m : Γ(E, U)) :
    (pulledQuotient D h a ha).app V
      (((tensorPullback h).obj E).presheaf.map (homOfLE hVU).op
        (tensorPullbackSection h E U m)) =
      ((tensorPullback a).obj D.line).presheaf.map (homOfLE hVa).op
        (tensorPullbackSection a D.line
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U)
          (D.quotient.app _ (tensorPullbackSection _ E U m))) := by
  subst h
  rw [Hom.app_presheaf_map]
  unfold pulledQuotient
  simp only [eqToIso_refl, Iso.refl_inv, Category.id_comp, Hom.comp_app,
    ConcreteCategory.comp_apply]
  rw [tensorPullbackSection_comp]
  change ((tensorPullback a).obj D.line).presheaf.map (homOfLE hVa).op
    (((tensorPullback a).map D.quotient).app
      (a ⁻¹ᵁ ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U))
      (tensorPullbackSection a _ _ (tensorPullbackSection _ E U m))) = _
  rw [tensorPullbackSection_naturality]

private theorem compatibleIso_pullback {S T T' : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E) (h : T ⟶ S)
    (L : T.Modules) (q : (tensorPullback h).obj E ⟶ L)
    (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (hF : F ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h)
    (θ : (tensorPullback F).obj D.line ≅ L)
    (hθ : pulledQuotient D h F hF ≫ θ.hom = q) (u : T' ⟶ T)
    (hF' : (u ≫ F) ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = u ≫ h) :
    pulledQuotient D (u ≫ h) (u ≫ F) hF' ≫
        (tensorPullbackSectionComp u F).hom.app D.line ≫ (tensorPullback u).map θ.hom =
      lineQuotientPullback h u E L q := by
  subst h
  apply tensorPullback_hom_ext (u ≫ F ≫ _) E ((tensorPullback u).obj L)
  intro U m
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, Scheme.Hom.comp_preimage]
  have hu := pulledQuotient_unit D (u ≫ F ≫ _) (u ≫ F) hF' U
    ((u ≫ F ≫ _) ⁻¹ᵁ U) le_rfl le_rfl m
  simp only [Scheme.Hom.comp_preimage, presheaf_map_id_apply] at hu
  erw [hu]
  erw [tensorPullbackSection_comp u F D.line
    ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U)]
  erw [tensorPullbackSection_naturality]
  have hh := congrArg (fun k ↦ k.app ((F ≫ _) ⁻¹ᵁ U)
    (tensorPullbackSection (F ≫ _) E U m)) hθ
  simp only [Hom.comp_app, ConcreteCategory.comp_apply] at hh
  have hf := pulledQuotient_unit D (F ≫ _) F rfl U ((F ≫ _) ⁻¹ᵁ U)
    le_rfl le_rfl m
  simp only [Scheme.Hom.comp_preimage, presheaf_map_id_apply] at hf
  simp only [Scheme.Hom.comp_preimage] at hh
  erw [hf] at hh
  erw [hh]
  exact (lineQuotientPullback_section (F ≫ _) u E L q U m).symm

private theorem pulledQuotient_transport {S T : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] (D : TautologicalQuotient E) (h : T ⟶ S)
    (F G : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
    (hFG : F = G) (hF : F ≫ _ = h) (hG : G ≫ _ = h) :
    pulledQuotient D h F hF ≫
      (eqToIso (congrArg (fun f ↦ (tensorPullback f).obj D.line) hFG)).hom =
        pulledQuotient D h G hG := by
  cases hFG
  exact Category.comp_id _

attribute [local irreducible] tensorPullbackSectionComp tensorPullbackSectionAdjunction

private theorem fractionNaturality_of_coefficients {S T T' : Scheme.{u}}
    (h : T ⟶ S) (u : T' ⟶ T) (E : S.Modules) [E.IsQuasicoherent]
    (L : T.Modules) (q : (tensorPullback h).obj E ⟶ L)
    (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
    (ψ' : RelativeGradedLineMap (u ≫ h) (SymmetricAlgebraSheaf.gradedAlgebraData E)
      ((tensorPullback u).obj L))
    (hc : ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
        (l : Γ(L, W.1)), IsFreeGenerator l →
        ∀ (W' : T'.affineOpens) (hWW' : W'.1 ≤ u ⁻¹ᵁ W.1)
          (hW'U : W'.1 ≤ (u ≫ h) ⁻¹ᵁ U.1),
          (∀ (d : ℕ) (z : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d),
            ψ'.quotientCoefficient U W' hW'U
              (((tensorPullback u).obj L).val.map (homOfLE hWW').op
                (tensorPullbackSection u L W.1 l)) d z =
              u.appLE W.1 W'.1 hWW' (ψ.quotientCoefficient U W hWU l d z)) ∧
          ∀ m : Γ(E, U.1),
            quotientGeneratorCoefficient (u ≫ h) E ((tensorPullback u).obj L)
              (lineQuotientPullback h u E L q) U W' hW'U
              (((tensorPullback u).obj L).val.map (homOfLE hWW').op
                (tensorPullbackSection u L W.1 l)) m =
              u.appLE W.1 W'.1 hWW' (quotientGeneratorCoefficient h E L q U W hWU l m)) :
    QuotientFractionNaturality h u E L q ψ ψ' := by
  intro U W hWU l hl W' hWW' hW'U
  obtain ⟨hcoeff, hgen⟩ := hc U W hWU l hl W' hWW' hW'U
  refine ⟨hcoeff, ?_⟩
  intro m
  refine ⟨hgen m, Localization.awayMap (u.appLE W.1 W'.1 hWW').hom
    (quotientGeneratorCoefficient h E L q U W hWU l m), ?_, ?_⟩
  · intro b
    exact IsLocalization.map_eq _ _
  · intro d z
    simp only [Localization.mk_eq_mk', Localization.awayMap,
      IsLocalization.Away.map, IsLocalization.map_mk', map_pow]

/-- Both inverse identities for an arbitrary normalized tautological datum, their chart
normalizations, invariance under quotient isomorphisms, and arbitrary pullback compatibility.
The existing fraction-map theorem provides the maps quantified over below, uniquely. -/
theorem line_quotient_chart_inverse_pullback {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] (D : TautologicalQuotient E) :
    (∀ (T : Scheme.{u}) (h : T ⟶ S)
      (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
      (ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h),
      ((tensorPullback a).obj D.line).IsInvertible ∧
      Epi (pulledQuotient D h a ha) ∧ RecoveredQuotientFrame D h a ha ∧
      ∀ (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E)
          ((tensorPullback a).obj D.line))
        (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj),
        ψ.ExtendsLineQuotient h E _ (pulledQuotient D h a ha) →
        ψ.HasQuotientFractionCharts h E _ (pulledQuotient D h a ha) F →
          F = a ∧ RecoveredFractionCoefficients D h a ψ) ∧
    ∀ (T : Scheme.{u}) (h : T ⟶ S) (L : T.Modules), L.IsInvertible →
      ∀ (q : (tensorPullback h).obj E ⟶ L), Epi q →
      ∀ (ψ : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L)
        (F : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj),
        ψ.ExtendsLineQuotient h E L q → ψ.HasQuotientFractionCharts h E L q F →
        ∃ (hF : F ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h)
          (θ : (tensorPullback F).obj D.line ≅ L),
          pulledQuotient D h F hF ≫ θ.hom = q ∧
          InverseLineChartNormalization D h L q F θ ∧
          (∀ (L' : T.Modules) (v : L ≅ L')
            (q' : (tensorPullback h).obj E ⟶ L'), q ≫ v.hom = q' →
            ∀ (ψ' : RelativeGradedLineMap h (SymmetricAlgebraSheaf.gradedAlgebraData E) L')
              (F' : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj),
              ψ'.ExtendsLineQuotient h E L' q' →
              ψ'.HasQuotientFractionCharts h E L' q' F' →
              F' = F ∧
              ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
                (l : Γ(L, W.1)), IsFreeGenerator l →
                ∀ (d : ℕ) (c : (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U d),
                  ψ'.quotientCoefficient U W hWU (v.hom.app W.1 l) d c =
                    ψ.quotientCoefficient U W hWU l d c) ∧
          ∀ (T' : Scheme.{u}) (u : T' ⟶ T),
            ((tensorPullback u).obj L).IsInvertible ∧ Epi (lineQuotientPullback h u E L q) ∧
            ∀ (ψ' : RelativeGradedLineMap (u ≫ h)
                (SymmetricAlgebraSheaf.gradedAlgebraData E) ((tensorPullback u).obj L))
              (F' : T' ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj),
              ψ'.ExtendsLineQuotient (u ≫ h) E _ (lineQuotientPullback h u E L q) →
              ψ'.HasQuotientFractionCharts (u ≫ h) E _ (lineQuotientPullback h u E L q) F' →
              ∃ hFF : F' = u ≫ F,
                (∀ (hF' : F' ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = u ≫ h)
                  (θ' : (tensorPullback F').obj D.line ≅ (tensorPullback u).obj L),
                  pulledQuotient D (u ≫ h) F' hF' ≫ θ'.hom =
                    lineQuotientPullback h u E L q →
                  θ'.hom =
                    (eqToIso (congrArg (fun f ↦ (tensorPullback f).obj D.line) hFF)).hom ≫
                    (tensorPullbackSectionComp u F).hom.app D.line ≫
                    (tensorPullback u).map θ.hom ∧
                  InverseLineChartNormalization D (u ≫ h) ((tensorPullback u).obj L)
                    (lineQuotientPullback h u E L q) F' θ') ∧
                QuotientFractionNaturality h u E L q ψ ψ'  := by
  constructor
  · intro T h a ha
    have : D.line.IsInvertible := D.invertible
    refine ⟨((invertible_pullback_tensor a).1 D.line).2, pulledQuotient_epi D h a ha, ?_, ?_⟩
    · exact recoveredQuotientFrame D h a ha
    · intro ψ F hψ hcharts
      have := ((invertible_pullback_tensor a).1 D.line).2
      have := pulledQuotient_epi D h a ha
      obtain ⟨hc, hcoeff⟩ := lineQuotient_recovered_charts h E D a ha ψ hψ
      exact ⟨fraction_map_unique h E _ _ ψ hψ F a hcharts hc, hcoeff⟩
  · intro T h L hL q hq ψ F hψ hcharts
    have := hL
    have := hq
    have := pulledQuotient_epi D h F hcharts.1
    let θ := Classical.choose (compatibleIso_of_charts h E D L q ψ F hψ hcharts)
    have hθ := Classical.choose_spec (compatibleIso_of_charts h E D L q ψ F hψ hcharts)
    refine ⟨hcharts.1, θ, hθ,
      inverseNormalization_of_compatible D h L q F hcharts.1 θ hθ, ?_, ?_⟩
    · intro L' v q' hv ψ' F' hψ' hc'
      have : L'.IsInvertible := IsInvertible.of_iso v
      have : Epi q' := by rw [← hv]; infer_instance
      obtain ⟨hcoeff, hc⟩ := lineQuotient_iso_charts h E L q ψ hψ L' v q' hv ψ' hψ'
      exact ⟨fraction_map_unique h E L' q' ψ' hψ' F' F hc' (hc F hcharts), hcoeff⟩
    · intro T' u
      have := ((invertible_pullback_tensor u).1 L).2
      have := lineQuotientPullback_epi h u E L q
      refine ⟨inferInstance, inferInstance, ?_⟩
      intro ψ' F' hψ' hc'
      obtain ⟨hc, hnat⟩ := lineQuotient_pullback_charts h u E L q ψ hψ F hcharts ψ' hψ'
      have hnat := fractionNaturality_of_coefficients h u E L q ψ ψ' hnat
      have hFF := fraction_map_unique (u ≫ h) E _ _ ψ' hψ' F' (u ≫ F) hc' hc
      refine ⟨hFF, ?_, hnat⟩
      intro hF' θ' hθ'
      constructor
      · have := pulledQuotient_epi D (u ≫ h) F' hF'
        apply (cancel_epi (pulledQuotient D (u ≫ h) F' hF')).1
        rw [← Category.assoc, ← Category.assoc, pulledQuotient_transport D (u ≫ h)
          F' (u ≫ F) hFF hF' hc.1, Category.assoc]
        exact hθ'.trans (compatibleIso_pullback D h L q F hcharts.1 θ hθ u hc.1).symm
      · exact inverseNormalization_of_compatible D (u ≫ h) _ _ F' hF' θ' hθ'

end AlgebraicGeometry.ProjectiveBundleQuotientGeometry
