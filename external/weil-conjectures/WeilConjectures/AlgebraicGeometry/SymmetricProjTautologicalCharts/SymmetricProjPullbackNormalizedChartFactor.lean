/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import all WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistExistence
import all WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientPulledChartNormalization
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections

/-! The normalized tautological quotients intertwine on affine-pair Proj charts.

Source: Stacks Project, Constructions, Tags 01MY, 01N2, 01NR and 01OB.
(blueprint: lem-trf-symmetric-proj-pullback-normalized-chart-factor)
-/
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.SymmetricProjTautologicalCharts
attribute [local instance 2000] CategoryTheory.Abelian.hasFiniteLimits
attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionComp Scheme.Modules.tensorPullbackSectionAdjunction
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjι
  Scheme.GradedAlgebraData.relProjHom
  Scheme.GradedAlgebraData.PullbackData.relProjComparison
  Scheme.Modules.tensorPullbackSection

open Scheme.Modules

private theorem tensor_unit_section {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (s : Γ(M, U)) :
    ((tensorPullbackSectionAdjunction f).unit.app M).app U s =
      tensorPullbackSection f M U s := by
  unfold tensorPullbackSectionAdjunction
  exact (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction f)).1 M U s

private theorem tensor_section_map {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    {M N : Z.Modules} (v : M ⟶ N) (U : Z.Opens) (s : Γ(M, U)) :
    ((tensorPullback f).map v).app (f ⁻¹ᵁ U) (tensorPullbackSection f M U s) =
      tensorPullbackSection f N U (v.app U s) := by
  rw [← tensor_unit_section, ← tensor_unit_section]
  exact congrArg (fun k ↦ k.app U s)
    ((tensorPullbackSectionAdjunction f).unit_naturality v)

private theorem tensor_section_res {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (M : Z.Modules) {U V : Z.Opens} (h : V ≤ U) (s : Γ(M, U)) :
    tensorPullbackSection f M V (M.presheaf.map (homOfLE h).op s) =
      ((tensorPullback f).obj M).presheaf.map (homOfLE (f.preimage_mono h)).op
        (tensorPullbackSection f M U s) := by
  rw [← tensor_unit_section, ← tensor_unit_section]
  exact Hom.app_presheaf_map ((tensorPullbackSectionAdjunction f).unit.app M)
    (homOfLE h) s

private noncomputable def sectionOn {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (s : Γ(M, U)) : Γ((tensorPullback f).obj M, V) :=
  ((tensorPullback f).obj M).presheaf.map (homOfLE h).op
    (tensorPullbackSection f M U s)

private theorem sectionOn_self {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (s : Γ(M, U)) :
    sectionOn f M U (f ⁻¹ᵁ U) le_rfl s = tensorPullbackSection f M U s := by
  unfold sectionOn
  simp

private theorem sectionOn_map {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    {M N : Z.Modules} (v : M ⟶ N) (U : Z.Opens) (V : Y.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (s : Γ(M, U)) :
    ((tensorPullback f).map v).app V (sectionOn f M U V h s) =
      sectionOn f N U V h (v.app U s) := by
  unfold sectionOn
  rw [Hom.app_presheaf_map, tensor_section_map]

private theorem comp_preimage_le {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    {U : Z.Opens} {V : X.Opens} (h : V ≤ g ⁻¹ᵁ f ⁻¹ᵁ U) :
    V ≤ (g ≫ f) ⁻¹ᵁ U := by
  rwa [Scheme.Hom.comp_preimage]

private theorem sectionOn_comp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (V : X.Opens) (h : V ≤ g ⁻¹ᵁ f ⁻¹ᵁ U)
    (s : Γ(M, U)) :
    ((tensorPullbackSectionComp g f).hom.app M).app V
      (sectionOn (g ≫ f) M U V (comp_preimage_le g f h) s) =
      sectionOn g ((tensorPullback f).obj M) (f ⁻¹ᵁ U) V h
        (tensorPullbackSection f M U s) := by
  unfold sectionOn
  rw [Hom.app_presheaf_map,
    ProjectiveBundleQuotientGeometry.tensor_comp_section]
  rfl

private theorem sectionOn_comp_inv {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (V : X.Opens) (h : V ≤ g ⁻¹ᵁ f ⁻¹ᵁ U)
    (s : Γ(M, U)) :
    ((tensorPullbackSectionComp g f).inv.app M).app V
      (sectionOn g ((tensorPullback f).obj M) (f ⁻¹ᵁ U) V h
        (tensorPullbackSection f M U s)) =
      sectionOn (g ≫ f) M U V (comp_preimage_le g f h) s := by
  rw [← sectionOn_comp, ← ConcreteCategory.comp_apply, ← Hom.comp_app]
  simp only [Iso.hom_inv_id_app, Hom.id_app, ConcreteCategory.id_apply]

private theorem sectionOn_restrict {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (M : Z.Modules) {U U' : Z.Opens} (hU : U' ≤ U) (V : Y.Opens)
    (h : V ≤ f ⁻¹ᵁ U') (s : Γ(M, U)) :
    sectionOn f M U' V h (M.presheaf.map (homOfLE hU).op s) =
      sectionOn f M U V (h.trans (f.preimage_mono hU)) s := by
  unfold sectionOn
  rw [tensor_section_res, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private theorem comp_map_section {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    (M : Z.Modules) (N : Y.Modules) (q : (tensorPullback f).obj M ⟶ N)
    (U : Z.Opens) (s : Γ(M, U)) :
    (((tensorPullbackSectionComp g f).hom.app M ≫ (tensorPullback g).map q).app
      (g ⁻¹ᵁ f ⁻¹ᵁ U))
      (sectionOn (g ≫ f) M U (g ⁻¹ᵁ f ⁻¹ᵁ U) (comp_preimage_le g f le_rfl) s) =
    tensorPullbackSection g N (f ⁻¹ᵁ U)
      (q.app (f ⁻¹ᵁ U) (tensorPullbackSection f M U s)) := by
  rw [Hom.comp_app, ConcreteCategory.comp_apply,
    sectionOn_comp g f M U (g ⁻¹ᵁ f ⁻¹ᵁ U) le_rfl s,
    sectionOn_self g ((tensorPullback f).obj M) (f ⁻¹ᵁ U)
      (tensorPullbackSection f M U s)]
  exact tensor_section_map g q (f ⁻¹ᵁ U) (tensorPullbackSection f M U s)

private theorem sectionOn_comp_middle {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) (hW : W ≤ g ⁻¹ᵁ V) (s : Γ(M, U)) :
    ((tensorPullbackSectionComp g f).hom.app M).app W
      (sectionOn (g ≫ f) M U W
        (comp_preimage_le g f (hW.trans (g.preimage_mono hV))) s) =
      sectionOn g ((tensorPullback f).obj M) V W hW (sectionOn f M U V hV s) := by
  rw [sectionOn_comp]
  exact (sectionOn_restrict g ((tensorPullback f).obj M) hV W hW
    (tensorPullbackSection f M U s)).symm

private theorem tensor_hom_ext_affine {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (E : Z.Modules) [E.IsQuasicoherent] (U : Z.affineOpens)
    (hU : f ⁻¹ᵁ U.1 = ⊤) (N : Y.Modules)
    (v w : (tensorPullback f).obj E ⟶ N)
    (h : ∀ t : Γ(E, U.1),
      v.app (f ⁻¹ᵁ U.1) (tensorPullbackSection f E U.1 t) =
        w.app (f ⁻¹ᵁ U.1) (tensorPullbackSection f E U.1 t)) : v = w := by
  classical
  apply hom_ext
  intro V
  ext s
  let I := {O : Y.affineOpens // O.1 ≤ V}
  have hcover : V ≤ ⨆ O : I, O.1.1 := by
    intro x hx
    obtain ⟨O, hO, hxO, hOV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      Y.isBasis_affineOpens hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨O, hO⟩, hOV⟩, hxO⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun O : I ↦ O.1.1) V (fun O ↦ homOfLE O.2) hcover
  intro O
  rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map]
  have hOU : O.1.1 ≤ f ⁻¹ᵁ U.1 := by rw [hU]; exact le_top
  let : Algebra Γ(Z, U.1) Γ(Y, O.1.1) := (f.appLE U.1 O.1.1 hOU).hom.toAlgebra
  let : ∀ G : Z.Modules, Module Γ(Z, U.1) Γ((tensorPullback f).obj G, O.1.1) :=
    fun G ↦ Module.compHom _ (f.appLE U.1 O.1.1 hOU).hom
  obtain ⟨c, hc, _, hp, _⟩ := exists_tensorPullback_affine_sections f U O.1 hOU
  obtain ⟨t, ht⟩ := (hc E inferInstance).surjective
    (((tensorPullback f).obj E).presheaf.map (homOfLE O.2).op s)
  rw [← ht]
  clear ht
  induction t using TensorProduct.inductionOn with
  | tmul t r =>
      rw [hp]
      have hs := Classical.choose_spec (exists_tensorPullbackAdjunction f) E (op U.1) t
      have hs' : (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app E).val.app
          (op U.1) t) = tensorPullbackSection f E U.1 t := by
        unfold tensorPullbackSection
        exact hs
      rw [hs', Hom.app_smul, Hom.app_smul]
      apply congrArg (r • ·)
      rw [Hom.app_presheaf_map, Hom.app_presheaf_map, h t]
  | add t t' ht ht' => simp only [map_add, ht, ht']

private theorem tensor_hom_ext_affine_on {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (E : Z.Modules) [E.IsQuasicoherent] (U : Z.affineOpens)
    (hU : f ⁻¹ᵁ U.1 = ⊤) (V : Y.Opens) (hV : V = f ⁻¹ᵁ U.1)
    (N : Y.Modules) (v w : (tensorPullback f).obj E ⟶ N)
    (h : ∀ t : Γ(E, U.1),
      v.app V (sectionOn f E U.1 V hV.le t) =
        w.app V (sectionOn f E U.1 V hV.le t)) : v = w := by
  subst V
  apply tensor_hom_ext_affine f E U hU N v w
  intro t
  simpa only [sectionOn_self] using h t

private theorem transported_quotient_section {X S T : Scheme.{u}}
    (g : X ⟶ S) (p : T ⟶ X) (f : T ⟶ S) (hf : f = p ≫ g)
    (E : S.Modules) (N : T.Modules)
    (q₀ : (tensorPullback p).obj ((tensorPullback g).obj E) ⟶ N)
    (e : (tensorPullback f).obj E = (tensorPullback (p ≫ g)).obj E)
    (q : (tensorPullback f).obj E ⟶ N)
    (hq : q = (eqToIso e).hom ≫ (tensorPullbackSectionComp p g).hom.app E ≫ q₀)
    (U : S.Opens) (V : X.Opens) (hV : V ≤ g ⁻¹ᵁ U)
    (h : p ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (t : Γ(E, U)) :
    q.app (p ⁻¹ᵁ V) (sectionOn f E U (p ⁻¹ᵁ V) h t) =
      q₀.app (p ⁻¹ᵁ V)
        (tensorPullbackSection p ((tensorPullback g).obj E) V
          (sectionOn g E U V hV t)) := by
  subst f
  cases e
  subst q
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp, Hom.comp_app,
    ConcreteCategory.comp_apply]
  rw [sectionOn_comp_middle p g E U V (p ⁻¹ᵁ V) hV le_rfl, sectionOn_self]
  rfl

private noncomputable def line_transport {R Y Z : Scheme.{u}}
    (f : Y ⟶ R) (r : Y ⟶ Z) (i : Z ⟶ R) (hf : f = r ≫ i)
    (L : R.Modules) :
    (tensorPullback f).obj L ⟶ (tensorPullback r).obj ((tensorPullback i).obj L) := by
  subst f
  exact (tensorPullbackSectionComp r i).hom.app L

private theorem line_transport_section {R Y Z : Scheme.{u}}
    (f : Y ⟶ R) (r : Y ⟶ Z) (i : Z ⟶ R) (hf : f = r ≫ i)
    (L : R.Modules) (U : R.Opens) (O : Y.Opens) (h : O ≤ f ⁻¹ᵁ U)
    (h' : O ≤ r ⁻¹ᵁ i ⁻¹ᵁ U) (s : Γ(L, U)) :
    (line_transport f r i hf L).app O (sectionOn f L U O h s) =
      sectionOn r ((tensorPullback i).obj L) (i ⁻¹ᵁ U) O h'
        (tensorPullbackSection i L U s) := by
  subst f
  unfold line_transport
  exact sectionOn_comp r i L U O h' s

private noncomputable def tensor_comp_app {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (f : Y ⟶ Z) (M : Z.Modules) :
    (tensorPullback (g ≫ f)).obj M ≅ (tensorPullback g).obj ((tensorPullback f).obj M) :=
  (tensorPullbackSectionComp g f).app M

attribute [local irreducible] tensor_comp_app

private theorem sectionOn_comp_app_inv {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (V : X.Opens) (h : V ≤ g ⁻¹ᵁ f ⁻¹ᵁ U)
    (s : Γ(M, U)) :
    (tensor_comp_app g f M).inv.app V
      (sectionOn g ((tensorPullback f).obj M) (f ⁻¹ᵁ U) V h
        (tensorPullbackSection f M U s)) =
      sectionOn (g ≫ f) M U V (comp_preimage_le g f h) s := by
  unfold tensor_comp_app
  exact sectionOn_comp_inv g f M U V h s

private theorem comp_app_apply {X : Scheme.{u}} {M N P : X.Modules}
    (v : M ⟶ N) (w : N ⟶ P) (U : X.Opens) (s : Γ(M, U)) :
    (v ≫ w).app U s = w.app U (v.app U s) := by
  rw [Hom.comp_app, ConcreteCategory.comp_apply]

private theorem chain_three_sections {X : Scheme.{u}} {M₀ M₁ M₂ M₃ M₄ M₅ : X.Modules}
    (v₁ : M₀ ⟶ M₁) (v₂ : M₁ ⟶ M₂) (v₃ : M₂ ⟶ M₃)
    (v₄ : M₃ ⟶ M₄) (v₅ : M₄ ⟶ M₅) (U : X.Opens)
    (s₀ : Γ(M₀, U)) (s₁ : Γ(M₁, U)) (s₂ : Γ(M₂, U)) (s₃ : Γ(M₃, U))
    (h₁ : v₁.app U s₀ = s₁) (h₂ : v₂.app U s₁ = s₂)
    (h₃ : v₃.app U s₂ = s₃) :
    (v₁ ≫ v₂ ≫ v₃ ≫ v₄ ≫ v₅).app U s₀ = v₅.app U (v₄.app U s₃) := by
  have heval : (v₁ ≫ v₂ ≫ v₃ ≫ v₄ ≫ v₅).app U s₀ =
      v₅.app U (v₄.app U (v₃.app U (v₂.app U (v₁.app U s₀)))) :=
    (comp_app_apply v₁ (v₂ ≫ v₃ ≫ v₄ ≫ v₅) U s₀).trans
      ((comp_app_apply v₂ (v₃ ≫ v₄ ≫ v₅) U (v₁.app U s₀)).trans
        ((comp_app_apply v₃ (v₄ ≫ v₅) U (v₂.app U (v₁.app U s₀))).trans
          (comp_app_apply v₄ v₅ U (v₃.app U (v₂.app U (v₁.app U s₀))))))
  exact heval.trans
    ((congrArg (fun z ↦ v₅.app U (v₄.app U (v₃.app U (v₂.app U z)))) h₁).trans
      ((congrArg (fun z ↦ v₅.app U (v₄.app U (v₃.app U z))) h₂).trans
        (congrArg (fun z ↦ v₅.app U (v₄.app U z)) h₃)))

private theorem chart_transport_section {R T Y Z : Scheme.{u}}
    (k : T ⟶ R) (i : Z ⟶ R) (j : Y ⟶ T) (r : Y ⟶ Z)
    (hr : j ≫ k = r ≫ i) (L : R.Modules) (N : T.Modules)
    {F : Z.Modules} {F' : Y.Modules}
    (χ : (tensorPullback i).obj L ≅ F) (χ' : (tensorPullback j).obj N ≅ F')
    (θ : (tensorPullback r).obj F ⟶ F')
    (U : R.Opens) (O : Y.Opens) (hj : O ≤ j ⁻¹ᵁ k ⁻¹ᵁ U)
    (hOr : O ≤ r ⁻¹ᵁ i ⁻¹ᵁ U) (s : Γ(L, U)) :
    ((tensor_comp_app j k L).inv ≫ line_transport (j ≫ k) r i hr L ≫
      (tensorPullback r).map χ.hom ≫ θ ≫ χ'.inv).app O
      (sectionOn j ((tensorPullback k).obj L) (k ⁻¹ᵁ U) O hj
      (tensorPullbackSection k L U s)) =
    χ'.inv.app O (θ.app O
      (sectionOn r F (i ⁻¹ᵁ U) O hOr
        (χ.hom.app (i ⁻¹ᵁ U) (tensorPullbackSection i L U s)))) := by
  exact chain_three_sections (tensor_comp_app j k L).inv
    (line_transport (j ≫ k) r i hr L) ((tensorPullback r).map χ.hom) θ χ'.inv O
    (sectionOn j ((tensorPullback k).obj L) (k ⁻¹ᵁ U) O hj
      (tensorPullbackSection k L U s))
    (sectionOn (j ≫ k) L U O (comp_preimage_le j k hj) s)
    (sectionOn r ((tensorPullback i).obj L) (i ⁻¹ᵁ U) O hOr
      (tensorPullbackSection i L U s))
    (sectionOn r F (i ⁻¹ᵁ U) O hOr
      (χ.hom.app (i ⁻¹ᵁ U) (tensorPullbackSection i L U s)))
    (sectionOn_comp_app_inv j k L U O hj s)
    (line_transport_section (j ≫ k) r i hr L U O (comp_preimage_le j k hj) hOr s)
    (sectionOn_map r χ.hom (i ⁻¹ᵁ U) O hOr (tensorPullbackSection i L U s))

private theorem local_factor_of_chart_equations
    {X S R T Y Z : Scheme.{u}} (g : X ⟶ S) (p : R ⟶ S) (p' : T ⟶ X)
    (k : T ⟶ R) (i : Z ⟶ R) (j : Y ⟶ T) (r : Y ⟶ Z)
    (hr : j ≫ k = r ≫ i) (hw : k ≫ p = p' ≫ g)
    (E : S.Modules) [E.IsQuasicoherent] (L : R.Modules) (N : T.Modules)
    {F : Z.Modules} {F' : Y.Modules}
    (q₀ : (tensorPullback p).obj E ⟶ L)
    (q₁ : (tensorPullback p').obj ((tensorPullback g).obj E) ⟶ N)
    (χ : (tensorPullback i).obj L ≅ F) (χ' : (tensorPullback j).obj N ≅ F')
    (θ : (tensorPullback r).obj F ⟶ F')
    (e : (tensorPullback (k ≫ p)).obj E = (tensorPullback (p' ≫ g)).obj E)
    (U : S.affineOpens) (V : X.Opens) (hV : V ≤ g ⁻¹ᵁ U.1)
    (htop : (j ≫ (k ≫ p)) ⁻¹ᵁ U.1 = ⊤)
    (hOV : j ⁻¹ᵁ k ⁻¹ᵁ p ⁻¹ᵁ U.1 ≤ j ⁻¹ᵁ p' ⁻¹ᵁ V)
    (hOr : j ⁻¹ᵁ k ⁻¹ᵁ p ⁻¹ᵁ U.1 ≤ r ⁻¹ᵁ i ⁻¹ᵁ p ⁻¹ᵁ U.1)
    (hcompat : ∀ t : Γ(E, U.1),
      θ.app (j ⁻¹ᵁ k ⁻¹ᵁ p ⁻¹ᵁ U.1)
        (sectionOn r F (i ⁻¹ᵁ p ⁻¹ᵁ U.1) (j ⁻¹ᵁ k ⁻¹ᵁ p ⁻¹ᵁ U.1) hOr
          (χ.hom.app (i ⁻¹ᵁ p ⁻¹ᵁ U.1)
            (tensorPullbackSection i L (p ⁻¹ᵁ U.1)
              (q₀.app (p ⁻¹ᵁ U.1) (tensorPullbackSection p E U.1 t))))) =
      χ'.hom.app (j ⁻¹ᵁ k ⁻¹ᵁ p ⁻¹ᵁ U.1)
        (sectionOn j N (p' ⁻¹ᵁ V) (j ⁻¹ᵁ k ⁻¹ᵁ p ⁻¹ᵁ U.1) hOV
          (q₁.app (p' ⁻¹ᵁ V)
            (tensorPullbackSection p' ((tensorPullback g).obj E) V
              (sectionOn g E U.1 V hV t))))) :
    let P := (tensorPullback k).obj L
    let q := (tensorPullbackSectionComp k p).hom.app E ≫ (tensorPullback k).map q₀
    let q' := (eqToIso e).hom ≫ (tensorPullbackSectionComp p' g).hom.app E ≫ q₁
    ∃ v : (tensorPullback j).obj P ⟶ (tensorPullback j).obj N,
      (tensorPullback j).map q ≫ v = (tensorPullback j).map q' := by
  classical
  intro P q q'
  let v : (tensorPullback j).obj P ⟶ (tensorPullback j).obj N :=
    (tensor_comp_app j k L).inv ≫ line_transport (j ≫ k) r i hr L ≫
      (tensorPullback r).map χ.hom ≫ θ ≫ χ'.inv
  refine ⟨v, ?_⟩
  apply (cancel_epi ((tensorPullbackSectionComp j (k ≫ p)).hom.app E)).mp
  let O := j ⁻¹ᵁ k ⁻¹ᵁ p ⁻¹ᵁ U.1
  have hO : O = (j ≫ (k ≫ p)) ⁻¹ᵁ U.1 := by
    simp only [Scheme.Hom.comp_preimage]
    rfl
  apply tensor_hom_ext_affine_on (j ≫ (k ≫ p)) E U htop O hO
  intro t
  have hM : k ⁻¹ᵁ p ⁻¹ᵁ U.1 ≤ (k ≫ p) ⁻¹ᵁ U.1 := comp_preimage_le k p le_rfl
  have hVG : p' ⁻¹ᵁ V ≤ (k ≫ p) ⁻¹ᵁ U.1 := by
    rw [hw]
    exact p'.preimage_mono hV
  have hq : q.app (k ⁻¹ᵁ p ⁻¹ᵁ U.1)
      (sectionOn (k ≫ p) E U.1 (k ⁻¹ᵁ p ⁻¹ᵁ U.1) hM t) =
      tensorPullbackSection k L (p ⁻¹ᵁ U.1)
        (q₀.app (p ⁻¹ᵁ U.1) (tensorPullbackSection p E U.1 t)) :=
    comp_map_section k p E L q₀ U.1 t
  have hq' : q'.app (p' ⁻¹ᵁ V)
      (sectionOn (k ≫ p) E U.1 (p' ⁻¹ᵁ V) hVG t) =
      q₁.app (p' ⁻¹ᵁ V)
        (tensorPullbackSection p' ((tensorPullback g).obj E) V
          (sectionOn g E U.1 V hV t)) := by
    exact transported_quotient_section g p' (k ≫ p) hw E N q₁ e q' rfl
      U.1 V hV hVG t
  let s := sectionOn (j ≫ (k ≫ p)) E U.1 O hO.le t
  let s' := sectionOn (k ≫ p) E U.1 (k ⁻¹ᵁ p ⁻¹ᵁ U.1) hM t
  have hright :
      (((tensorPullbackSectionComp j (k ≫ p)).hom.app E ≫
        (tensorPullback j).map q').app O) s =
      sectionOn j N (p' ⁻¹ᵁ V) O hOV
        (q₁.app (p' ⁻¹ᵁ V)
          (tensorPullbackSection p' ((tensorPullback g).obj E) V
            (sectionOn g E U.1 V hV t))) := by
    refine (comp_app_apply ((tensorPullbackSectionComp j (k ≫ p)).hom.app E)
      ((tensorPullback j).map q') O s).trans ?_
    refine (congrArg (((tensorPullback j).map q').app O)
      (sectionOn_comp_middle j (k ≫ p) E U.1 (p' ⁻¹ᵁ V) O hVG hOV t)).trans ?_
    exact (sectionOn_map j q' (p' ⁻¹ᵁ V) O hOV
      (sectionOn (k ≫ p) E U.1 (p' ⁻¹ᵁ V) hVG t)).trans
        (congrArg (sectionOn j N (p' ⁻¹ᵁ V) O hOV) hq')
  have hmap := (sectionOn_map j q (k ⁻¹ᵁ p ⁻¹ᵁ U.1) O le_rfl s').trans
      (congrArg (sectionOn j P (k ⁻¹ᵁ p ⁻¹ᵁ U.1) O le_rfl) hq)
  refine ((comp_app_apply ((tensorPullbackSectionComp j (k ≫ p)).hom.app E)
    ((tensorPullback j).map q ≫ v) O s).trans ?_).trans hright.symm
  refine (comp_app_apply ((tensorPullback j).map q) v O
    (((tensorPullbackSectionComp j (k ≫ p)).hom.app E).app O s)).trans ?_
  refine (congrArg (fun z ↦ v.app O (((tensorPullback j).map q).app O z))
    (sectionOn_comp_middle j (k ≫ p) E U.1 (k ⁻¹ᵁ p ⁻¹ᵁ U.1) O hM le_rfl t)).trans ?_
  refine (congrArg (v.app O) hmap).trans ?_
  refine (chart_transport_section k i j r hr L N χ χ' θ (p ⁻¹ᵁ U.1) O le_rfl hOr
    (q₀.app (p ⁻¹ᵁ U.1) (tensorPullbackSection p E U.1 t))).trans ?_
  refine (congrArg (χ'.inv.app O) (hcompat t)).trans ?_
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id,
    Hom.id_app, ConcreteCategory.id_apply]

private theorem twist_map_generator
    {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (a : A) (ha : a ∈ 𝒜 1) (U : (Proj 𝒜).Opens) :
    (Proj.twistPullbackMap ψ hψ 1).app (Proj.map ψ hψ ⁻¹ᵁ U)
      (tensorPullbackSection (Proj.map ψ hψ) (Proj.twist 𝒜 1) U
        ((Proj.unitToTwist ha).app U (1 : Γ(Proj 𝒜, U)))) =
      (Proj.unitToTwist (ψ.map_mem ha)).app (Proj.map ψ hψ ⁻¹ᵁ U)
        (1 : Γ(Proj ℬ, Proj.map ψ hψ ⁻¹ᵁ U)) := by
  apply Subtype.ext
  funext x
  apply Subtype.ext
  rw [Proj.twistPullbackMap_section]
  change Localization.localRingHom _ _ ψ.toRingHom rfl _ = _
  rw [Proj.val_unitToTwist_app_apply, Proj.val_unitToTwist_app_apply]
  simp only [Proj.one_apply, HomogeneousLocalization.val_one, one_mul,
    Localization.localRingHom_mk, GradedRingHom.coe_toRingHom,
    OneMemClass.coe_one, map_one]
  congr 1

private theorem twist_map_generator_on
    {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (a : A) (ha : a ∈ 𝒜 1) (U : (Proj 𝒜).Opens)
    (V : (Proj ℬ).Opens) (hV : V ≤ Proj.map ψ hψ ⁻¹ᵁ U) :
    (Proj.twistPullbackMap ψ hψ 1).app V
      (sectionOn (Proj.map ψ hψ) (Proj.twist 𝒜 1) U V hV
        ((Proj.unitToTwist ha).app U (unitSectionsEquiv U 1))) =
      (Proj.unitToTwist (ψ.map_mem ha)).app V (unitSectionsEquiv V 1) := by
  change (Proj.twistPullbackMap ψ hψ 1).app V
    (sectionOn (Proj.map ψ hψ) (Proj.twist 𝒜 1) U V hV
      ((Proj.unitToTwist ha).app U (1 : Γ(Proj 𝒜, U)))) =
    (Proj.unitToTwist (ψ.map_mem ha)).app V (1 : Γ(Proj ℬ, V))
  unfold sectionOn
  rw [Hom.app_presheaf_map, twist_map_generator]
  exact ProjectiveBundleQuotientGeometry.unit_section_res _ hV

private theorem normalized_chart_restrict {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (U : S.affineOpens) (t : Γ(E, U.1))
    (O : (Proj ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)).Opens)
    (hO : O ≤ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U ⁻¹ᵁ
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1) :
    (D.chart U).hom.app O
      (sectionOn ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U) D.line
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1) O hO
        (D.quotient.app ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
          (tensorPullbackSection (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
            E U.1 t))) =
    (Proj.unitToTwist (quotientSymmetricGenerator E U t).property).app O
      (unitSectionsEquiv O 1) := by
  have hg := D.generator U t (quotientSymmetricGenerator E U t).property
  rw [Adjunction.homEquiv_unit, Hom.comp_app] at hg
  change (D.chart U).hom.app _
    (tensorPullbackSection _ D.line _
      (D.quotient.app _ (((tensorPullbackSectionAdjunction
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).unit.app E).app U.1 t))) = _ at hg
  rw [tensor_unit_section] at hg
  unfold sectionOn
  rw [Hom.app_presheaf_map, hg]
  exact ProjectiveBundleQuotientGeometry.unit_section_res _ hO

private theorem normalized_chart_full {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (U : S.affineOpens) (t : Γ(E, U.1)) :
    (D.chart U).hom.app _
      (tensorPullbackSection ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)
        D.line ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U.1)
        (D.quotient.app _ (tensorPullbackSection
          (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom E U.1 t))) =
      (Proj.unitToTwist (quotientSymmetricGenerator E U t).property).app _
        (unitSectionsEquiv _ 1) := by
  have h := normalized_chart_restrict E D U t _ le_rfl
  rw [sectionOn_self] at h
  exact h

attribute [local irreducible] Proj.twist
  Proj.unitToTwist sectionOn quotientSymmetricGenerator Proj.map
  Proj Proj.twistPullbackMap unitSectionsEquiv

/-- On an affine pair, the normalized pulled quotients admit an intertwining morphism.

Source: Stacks Project, Constructions, Tags 01MY, 01N2, 01NR and 01OB.
Proof: conjugate the explicit homogeneous-localization map on degree-one twists by
both normalized chart isomorphisms and the normalized pullback-composition maps.
The localization map takes the section iota(t)/1 to b(iota(t))/1, which `hb`
identifies with the corresponding pulled generator. Naturality and the quotient
normalizations give the intertwining equation on these pulled sections. Since
sections over an affine base generate the pulled quasi-coherent module locally,
the affine tensor-section comparison extends this equation to module morphisms.
This works for empty charts and zero rings as well.
(blueprint: lem-trf-symmetric-proj-pullback-normalized-chart-factor)
-/
theorem normalized_pullback_quotient_chart_factor
    {X S : Scheme.{u}} (g : X ⟶ S) (E : S.Modules) [E.IsQuasicoherent]
    [((Scheme.Modules.tensorPullback g).obj E).IsQuasicoherent]
    (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (D' : ProjectiveBundleQuotientGeometry.TautologicalQuotient
      ((Scheme.Modules.tensorPullback g).obj E))
    (b : Scheme.GradedAlgebraData.PullbackData g (SymmetricAlgebraSheaf.gradedAlgebraData E)
      (SymmetricAlgebraSheaf.gradedAlgebraData ((Scheme.Modules.tensorPullback g).obj E)))
    (hb : ∀ (U : S.affineOpens) (W : X.affineOpens) (h : W.1 ≤ g ⁻¹ᵁ U.1)
      (m : E.val.obj (op U.1)),
      b.map h (SymmetricAlgebra.ι Γ(S, U.1) _ m) =
        SymmetricAlgebra.ι Γ(X, W.1) _
          (((Scheme.Modules.tensorPullback g).obj E).presheaf.map (homOfLE h).op
            (Scheme.Modules.tensorPullbackSection g E U.1 m)))
    (e : (Scheme.Modules.tensorPullback
        (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)).obj E =
      (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData
          ((Scheme.Modules.tensorPullback g).obj E)).relProjHom ≫ g)).obj E)
    (U₀ : S.affineOpens) (V : X.affineOpens) (hV : V.1 ≤ g ⁻¹ᵁ U₀.1) :
    let P := (tensorPullback b.relProjComparison).obj D.line
    let q := (tensorPullbackSectionComp b.relProjComparison
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
      (tensorPullback b.relProjComparison).map D.quotient
    let q' := (eqToIso e).hom ≫
      (tensorPullbackSectionComp
        (SymmetricAlgebraSheaf.gradedAlgebraData
          ((tensorPullback g).obj E)).relProjHom g).hom.app E ≫
          D'.quotient
    ∃ v : (tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData ((tensorPullback g).obj E)).relProjι V)).obj P ⟶
        (tensorPullback
          ((SymmetricAlgebraSheaf.gradedAlgebraData
            ((tensorPullback g).obj E)).relProjι V)).obj D'.line,
      (tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData
          ((tensorPullback g).obj E)).relProjι V)).map q ≫ v =
      (tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData
          ((tensorPullback g).obj E)).relProjι V)).map q' := by
  classical
  let A := SymmetricAlgebraSheaf.gradedAlgebraData E
  let E' := (tensorPullback g).obj E
  let A' := SymmetricAlgebraSheaf.gradedAlgebraData E'
  let k := b.relProjComparison
  let p := A.relProjHom
  let p' := A'.relProjHom
  let i := A.relProjι U₀
  let j := A'.relProjι V
  let r := Proj.map (b.map hV) (b.irrelevant_le_map hV)
  have hr : j ≫ k = r ≫ i := b.relProjι_relProjComparison hV
  have htop : (j ≫ (k ≫ p)) ⁻¹ᵁ U₀.1 = ⊤ := by
    rw [← Category.assoc, hr, Category.assoc]
    dsimp only [i, p]
    simp only [Scheme.Hom.comp_preimage, A.relProjHom_preimage,
      Scheme.Hom.preimage_opensRange, Scheme.Hom.preimage_top]
  let O := j ⁻¹ᵁ k ⁻¹ᵁ p ⁻¹ᵁ U₀.1
  have hOV : O ≤ j ⁻¹ᵁ p' ⁻¹ᵁ V.1 := by
    dsimp only [j, p']
    rw [A'.relProjHom_preimage, Scheme.Hom.preimage_opensRange]
    exact le_top
  have hOr : O ≤ r ⁻¹ᵁ i ⁻¹ᵁ p ⁻¹ᵁ U₀.1 := by
    have hh := congrArg (fun f : Proj (A'.grading V) ⟶ A.relProj ↦
      f ⁻¹ᵁ (p ⁻¹ᵁ U₀.1)) hr
    simpa only [Scheme.Hom.comp_preimage] using hh.le
  refine local_factor_of_chart_equations g p p' k i j r hr b.isPullback.w
    E D.line D'.line D.quotient D'.quotient (D.chart U₀) (D'.chart V)
    (Proj.twistPullbackMap (b.map hV) (b.irrelevant_le_map hV) 1)
    e U₀ V.1 hV htop hOV hOr ?_
  intro t
  have hgen := normalized_chart_full E D U₀ t
  have hgen' := normalized_chart_restrict E' D' V
    (sectionOn g E U₀.1 V.1 hV t) O hOV
  have htw := twist_map_generator_on (b.map hV) (b.irrelevant_le_map hV)
    (quotientSymmetricGenerator E U₀ t).val
    (quotientSymmetricGenerator E U₀ t).property (i ⁻¹ᵁ p ⁻¹ᵁ U₀.1) O hOr
  have hg :
      (⟨b.map hV (quotientSymmetricGenerator E U₀ t).val,
        (b.map hV).map_mem (quotientSymmetricGenerator E U₀ t).property⟩ :
          A'.grading V 1) =
        quotientSymmetricGenerator E' V (sectionOn g E U₀.1 V.1 hV t) := by
    apply Subtype.ext
    unfold quotientSymmetricGenerator sectionOn
    dsimp only
    exact hb U₀ V hV t
  have htw' := htw.trans (congrArg (fun m : A'.grading V 1 ↦
    (Proj.unitToTwist m.property).app O (unitSectionsEquiv O 1)) hg)
  exact (congrArg (fun z : Γ(Proj.twist (A.grading U₀) 1, i ⁻¹ᵁ p ⁻¹ᵁ U₀.1) ↦
    (Proj.twistPullbackMap (b.map hV) (b.irrelevant_le_map hV) 1).app O
      (sectionOn r (Proj.twist (A.grading U₀) 1) (i ⁻¹ᵁ p ⁻¹ᵁ U₀.1) O hOr z))
    hgen).trans (htw'.trans hgen'.symm)

end AlgebraicGeometry.SymmetricProjTautologicalCharts
