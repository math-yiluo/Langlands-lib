/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine

/-! # Tensor presentation of associated-module coefficient sections

Source: Stacks Project, Tags 01I9 and 01IA.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 4096 in
private theorem exists_spectral_tensor_equiv {A R : CommRingCat.{u}} (φ : A ⟶ R)
    (N : ModuleCat.{u} A) :
    let : Algebra A R := φ.hom.toAlgebra
    ∃ e : (R ⊗[A] N) ≃ₗ[R] Γ((pullback (Spec.map φ)).obj (tilde N), ⊤),
      ∀ s : N, e ((1 : R) ⊗ₜ[A] s) =
        pullbackΓ (Spec.map φ) (tilde N) (tilde.toOpen N ⊤ s) := by
  let : Algebra A R := φ.hom.toAlgebra
  refine ⟨(ModuleCat.tensorEquivExtendScalars A R N).trans
    (tildePullbackΓEquiv φ N), ?_⟩
  intro s
  rw [LinearEquiv.trans_apply, pullbackΓ_def]
  exact tildePullbackΓEquiv_one_tmul φ N s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 4096 in
private theorem exists_sections_equiv {R : CommRingCat.{u}}
    {M M' : (Spec R).Modules} (e : M ≅ M') :
    ∃ f : Γ(M, ⊤) ≃ₗ[R] Γ(M', ⊤), ∀ x : Γ(M, ⊤), f x = e.hom.app ⊤ x := by
  refine ⟨LinearEquiv.ofBijective (Hom.appSpecₗ e.hom ⊤)
    (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)), ?_⟩
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 4096 in
private theorem affine_restriction_unit {X : Scheme.{u}} (M : X.Modules)
    {B : X.Opens} (hB : IsAffineOpen B) (x : Γ(M, ⊤)) :
    ((restrictFunctorIsoPullback hB.fromSpec).hom.app M).app ⊤
      ((sectionsRestrictFromSpecLinearEquiv M hB).symm
        (M.presheaf.map (homOfLE le_top).op x)) = pullbackΓ hB.fromSpec M x := by
  rw [pullbackΓ_def, pullbackUnit_eq_of_isOpenImmersion, Hom.comp_app,
    pushforward_map_app, ConcreteCategory.comp_apply]
  congr 1
  change M.presheaf.map (homOfLE (hB.fromSpec_image_le ⊤)).op
      (M.presheaf.map (homOfLE le_top).op x) =
    M.presheaf.map (homOfLE (hB.fromSpec.image_preimage_le ⊤)).op x
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 4096 in
private theorem exists_affine_restriction_equiv {X : Scheme.{u}} (M : X.Modules)
    {B : X.Opens} (hB : IsAffineOpen B) :
    ∃ e : Γ(M.restrict hB.fromSpec, ⊤) ≃ₗ[Γ(X, B)] Γ(M, B),
      ∀ x : Γ(M, ⊤), ((restrictFunctorIsoPullback hB.fromSpec).app M).hom.app ⊤
        (e.symm (M.presheaf.map (homOfLE le_top).op x)) = pullbackΓ hB.fromSpec M x := by
  refine ⟨sectionsRestrictFromSpecLinearEquiv M hB, ?_⟩
  intro x
  exact affine_restriction_unit M hB x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 4096 in
private theorem coefficientGenerator_eq_pullbackΓ {S S' : Scheme.{u}} (g : S' ⟶ S)
    (N : ModuleCat.{u} Γ(S, ⊤)) (s : N) :
    coefficientGenerator g N s = pullbackΓ g ((pullback S.toSpecΓ).obj (tilde N))
      (pullbackΓ S.toSpecΓ (tilde N) (tilde.toOpen N ⊤ s)) := by
  rw [pullbackΓ_def, pullbackΓ_def]
  unfold coefficientGenerator
  let Q := (pullback S.toSpecΓ).obj (tilde N)
  let P := (pullback g).obj Q
  change P.presheaf.map (𝟙 (op ⊤))
    ((pullbackUnit g Q).app ⊤
      (Q.presheaf.map (𝟙 (op ⊤))
        ((pullbackUnit S.toSpecΓ (tilde N)).app ⊤ (tilde.toOpen N ⊤ s)))) = _
  erw [P.presheaf.map_id, Q.presheaf.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 4096 in
private theorem triple_pullback_unit {W X Y Z : Scheme.{u}}
    (j : W ⟶ Z) (g : Z ⟶ Y) (f : Y ⟶ X) (fg : W ⟶ X)
    (h : (j ≫ g) ≫ f = fg) (M : X.Modules) (s : Γ(M, ⊤)) :
    ((pullbackCompOfEq (j ≫ g) f fg h M).hom).app ⊤
      (((pullbackCompOfEq j g (j ≫ g) rfl ((pullback f).obj M)).hom).app ⊤
        (pullbackΓ j ((pullback g).obj ((pullback f).obj M))
          (pullbackΓ g ((pullback f).obj M) (pullbackΓ f M s)))) =
      pullbackΓ fg M s := by
  have h₁ := pullbackCompOfEq_hom_app_pullbackΓ j g (j ≫ g) rfl
    ((pullback f).obj M) (pullbackΓ f M s)
  have h₂ := pullbackCompOfEq_hom_app_pullbackΓ (j ≫ g) f fg h M s
  exact (congrArg (fun (x : Γ((pullback (j ≫ g)).obj ((pullback f).obj M), ⊤)) ↦
    ((pullbackCompOfEq (j ≫ g) f fg h M).hom).app ⊤ x) h₁).trans h₂

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 4096 in
private theorem exists_chart_iso {W X Y Z : Scheme.{u}}
    (j : W ⟶ Z) [IsOpenImmersion j] (g : Z ⟶ Y) (f : Y ⟶ X) (fg : W ⟶ X)
    (h : (j ≫ g) ≫ f = fg) (M : X.Modules) :
    let Q := (pullback f).obj M
    let P := (pullback g).obj Q
    ∃ e : P.restrict j ≅ (pullback fg).obj M,
      ∀ (s : Γ(M, ⊤)) (z : Γ(P.restrict j, ⊤)),
        ((restrictFunctorIsoPullback j).app P).hom.app ⊤ z =
          pullbackΓ j P (pullbackΓ g Q (pullbackΓ f M s)) →
        e.hom.app ⊤ z = pullbackΓ fg M s := by
  let Q := (pullback f).obj M
  let P := (pullback g).obj Q
  let a := (restrictFunctorIsoPullback j).app P
  let b := pullbackCompOfEq j g (j ≫ g) rfl Q
  let c := pullbackCompOfEq (j ≫ g) f fg h M
  refine ⟨a ≪≫ b ≪≫ c, ?_⟩
  intro s z hz
  simp only [Iso.trans_hom, Hom.comp_app, ConcreteCategory.comp_apply]
  change c.hom.app ⊤ (b.hom.app ⊤ (a.hom.app ⊤ z)) = _
  rw [hz]
  exact triple_pullback_unit j g f fg h M s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 4096 in
-- Transport between native tensors and module-category sections.
/-- Sections on an affine open of the pullback of an associated module have a
unit-compatible tensor presentation. This assertion involves no comparison morphism.
Source: Stacks Project, Tags 01I9 and 01IA, affine pullback of modules.
(blueprint: lem-pc-coefficient-source-affine-tensor-presentation).

Proof: Compose g with S.toSpecGamma and restrict to the affine scheme B. Pullback
composition is the unique isomorphism of left adjoints compatible with their units.
The affine pullback section formula for this composite identifies the sections with
R tensor_A N, where A = Gamma(S,O) and R = Gamma(B,O). The ring map A -> R is
g.appLE top B: the canonical GammaSpecIso cancels the chart's scalar map. The unit
of the tilde/Gamma adjunction sends s to tilde.toOpen N top s. Compatibility of
composite pullback units therefore sends the displayed coefficientGenerator,
restricted to B, to 1 tensor s. Swap tensor factors if the section formula is
written N tensor_A R. The formula and equivalence are also valid for B empty
or N zero, since both sides then have the corresponding zero module. -/
theorem exists_coefficientSource_affine_tensor_presentation
    {S S' : Scheme.{u}} (g : S' ⟶ S) (N : ModuleCat.{u} Γ(S, ⊤))
    (B : S'.Opens) (hB : IsAffineOpen B) :
    letI : Algebra Γ(S, ⊤) Γ(S', B) := (g.appLE ⊤ B (by simp)).hom.toAlgebra
    let P := (pullback g).obj ((pullback S.toSpecΓ).obj (tilde N))
    ∃ e : Γ(P, B) ≃ₗ[Γ(S', B)] (Γ(S', B) ⊗[Γ(S, ⊤)] N),
      ∀ s : N, e (P.presheaf.map (homOfLE le_top).op
        (coefficientGenerator g N s)) = (1 : Γ(S', B)) ⊗ₜ[Γ(S, ⊤)] s := by
  classical
  let : Algebra Γ(S, ⊤) Γ(S', B) := (g.appLE ⊤ B (by simp)).hom.toAlgebra
  let Q := (pullback S.toSpecΓ).obj (tilde N)
  let P := (pullback g).obj Q
  let j := hB.fromSpec
  let φ := g.appLE ⊤ B (by simp)
  have h : (j ≫ g) ≫ S.toSpecΓ = Spec.map φ := by
    rw [Category.assoc, Scheme.toSpecΓ_naturality, ← Category.assoc,
      hB.fromSpec_toSpecΓ, ← Spec.map_comp]
    congr 1
  obtain ⟨e, he⟩ := exists_chart_iso j g S.toSpecΓ (Spec.map φ) h (tilde N)
  obtain ⟨eΓ, heΓ⟩ := exists_sections_equiv e
  obtain ⟨eT, ht⟩ := exists_spectral_tensor_equiv φ N
  obtain ⟨e₂, hr⟩ := exists_affine_restriction_equiv P hB
  have hu (s : N) :
      eΓ (e₂.symm (P.presheaf.map (homOfLE le_top).op (coefficientGenerator g N s))) =
      pullbackΓ (Spec.map φ) (tilde N) (tilde.toOpen N ⊤ s) := by
    rw [heΓ]
    apply he (tilde.toOpen N ⊤ s)
    exact (hr (coefficientGenerator g N s)).trans
      (congrArg (fun (x : Γ(P, ⊤)) ↦ pullbackΓ j P x)
        (coefficientGenerator_eq_pullbackΓ g N s))
  let E := e₂.symm.trans (eΓ.trans eT.symm)
  refine ⟨E, ?_⟩
  intro s
  change eT.symm (eΓ (e₂.symm
    (P.presheaf.map (homOfLE le_top).op (coefficientGenerator g N s)))) = _
  rw [hu s, ← ht s]
  exact eT.symm_apply_apply _

end
end AlgebraicGeometry.Scheme.Modules
