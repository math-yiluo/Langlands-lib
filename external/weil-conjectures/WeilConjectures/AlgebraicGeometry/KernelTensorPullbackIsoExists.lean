/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFunctorial

/-!
# Comparison of pulled back kernel ideals under an ambient isomorphism

Source: Stacks Project, Morphisms, Section 01R1, Lemmas 29.32.2 and 29.32.3;
Sheaves, Definition 0095 and Lemma 0096.
(blueprint: lem-weil-pbc-kernel-tensor-pullback-iso-exists).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

private theorem exists_kernelPushforwardMap {Z Z₁ Z₂ : Scheme.{u}}
    (i₁ : Z ⟶ Z₁) (i₂ : Z ⟶ Z₂) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (φ : Z₁ ⟶ Z₂) (hc : i₁ ≫ φ = i₂) :
    ∃ β : i₂.ker.toModules ⟶ (Scheme.Modules.pushforward φ).obj i₁.ker.toModules,
      ∀ (U : Z₂.Opens) (s : Γ(i₂.ker.toModules, U)),
        i₁.ker.toModulesι.app (φ ⁻¹ᵁ U) (β.app U s) =
          φ.app U (i₂.ker.toModulesι.app U s) := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      classical
      -- Use only the ideal-section clause of conormal functoriality.
      obtain ⟨_, γ, hγ, _⟩ := Scheme.Modules.closedImmersion_conormal_functorial
        i₁ i₂ φ (𝟙 Z) (by simpa using hc)
      let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction φ)
      refine ⟨adj.homEquiv _ _ γ, ?_⟩
      intro U s
      rw [Adjunction.homEquiv_unit]
      exact hγ U s

private def KernelTensorPullbackMapProperty {Z Z₁ Z₂ : Scheme.{u}}
    (i₁ : Z ⟶ Z₁) (i₂ : Z ⟶ Z₂) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (φ : Z₁ ⟶ Z₂)
    (f : (Scheme.Modules.tensorPullback i₂).obj i₂.ker.toModules ⟶
      (Scheme.Modules.tensorPullback i₁).obj i₁.ker.toModules) : Prop :=
      ∀ (U : Z₂.Opens) (s₂ : Γ(i₂.ker.toModules, U))
      (s₁ : Γ(i₁.ker.toModules, φ ⁻¹ᵁ U)),
      i₁.ker.toModulesι.app (φ ⁻¹ᵁ U) s₁ =
        φ.app U (i₂.ker.toModulesι.app U s₂) →
      ∀ (W : Z.Opens) (a : W ≤ i₂ ⁻¹ᵁ U) (b : W ≤ i₁ ⁻¹ᵁ (φ ⁻¹ᵁ U)),
        f.app W
            (((Scheme.Modules.tensorPullback i₂).obj i₂.ker.toModules).val.map (homOfLE a).op
              (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
                i₂)).unit.app i₂.ker.toModules).app U s₂)) =
          ((Scheme.Modules.tensorPullback i₁).obj i₁.ker.toModules).val.map (homOfLE b).op
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
              i₁)).unit.app i₁.ker.toModules).app (φ ⁻¹ᵁ U) s₁)

private theorem exists_kernelTensorPullbackMap {Z Z₁ Z₂ : Scheme.{u}}
    (i₁ : Z ⟶ Z₁) (i₂ : Z ⟶ Z₂) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (φ : Z₁ ⟶ Z₂) (hc : i₁ ≫ φ = i₂) :
    ∃ f : (Scheme.Modules.tensorPullback i₂).obj i₂.ker.toModules ⟶
        (Scheme.Modules.tensorPullback i₁).obj i₁.ker.toModules,
      KernelTensorPullbackMapProperty i₁ i₂ φ f := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      classical
      subst i₂
      obtain ⟨β, hβ⟩ := exists_kernelPushforwardMap i₁ (i₁ ≫ φ) φ rfl
      let M := (Scheme.Modules.tensorPullback i₁).obj i₁.ker.toModules
      let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (i₁ ≫ φ))
      let t : (i₁ ≫ φ).ker.toModules ⟶ (Scheme.Modules.pushforward (i₁ ≫ φ)).obj M :=
        β ≫ (Scheme.Modules.pushforward φ).map
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i₁)).unit.app
            i₁.ker.toModules) ≫ (Scheme.Modules.pushforwardComp i₁ φ).hom.app M
      -- The adjoint of the transported ideal map is the desired conormal map.
      let f := (adj.homEquiv _ _).symm t
      have hf : adj.unit.app (i₁ ≫ φ).ker.toModules ≫
          (Scheme.Modules.pushforward (i₁ ≫ φ)).map f = t := by
        have h := (adj.homEquiv _ _).apply_symm_apply t
        rw [Adjunction.homEquiv_unit] at h
        exact h
      refine ⟨f, ?_⟩
      intro U s₂ s₁ hs W a b
      have hs' : β.app U s₂ = s₁ :=
        i₁.ker.injective_toModulesι_app _ ((hβ U s₂).trans hs.symm)
      have hfs := congrArg (fun q ↦ q.app U s₂) hf
      change f.app ((i₁ ≫ φ) ⁻¹ᵁ U)
        ((adj.unit.app (i₁ ≫ φ).ker.toModules).app U s₂) =
          (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i₁)).unit.app
            i₁.ker.toModules).app (φ ⁻¹ᵁ U) (β.app U s₂)) at hfs
      rw [hs'] at hfs
      have hn := f.val.naturality (homOfLE a).op
      have hns := congrArg (fun q ↦ q ((adj.unit.app (i₁ ≫ φ).ker.toModules).app U s₂)) hn
      change f.app W
        (((Scheme.Modules.tensorPullback (i₁ ≫ φ)).obj (i₁ ≫ φ).ker.toModules).val.map
          (homOfLE a).op ((adj.unit.app (i₁ ≫ φ).ker.toModules).app U s₂)) =
        M.val.map (homOfLE a).op
          (f.app ((i₁ ≫ φ) ⁻¹ᵁ U)
            ((adj.unit.app (i₁ ≫ φ).ker.toModules).app U s₂)) at hns
      exact hns.trans (congrArg (fun x ↦ M.val.map (homOfLE a).op x) hfs)

private theorem kernelTensorPullbackMap_comp_id {Z Z₁ Z₂ : Scheme.{u}}
    (i₁ : Z ⟶ Z₁) (i₂ : Z ⟶ Z₂) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (φ : Z₁ ⟶ Z₂) (ψ : Z₂ ⟶ Z₁) (hc₂ : i₂ ≫ ψ = i₁)
    (hcomp : φ ≫ ψ = 𝟙 Z₁)
    (f : (Scheme.Modules.tensorPullback i₂).obj i₂.ker.toModules ⟶
      (Scheme.Modules.tensorPullback i₁).obj i₁.ker.toModules)
    (g : (Scheme.Modules.tensorPullback i₁).obj i₁.ker.toModules ⟶
      (Scheme.Modules.tensorPullback i₂).obj i₂.ker.toModules)
    (hf : KernelTensorPullbackMapProperty i₁ i₂ φ f)
    (hg : KernelTensorPullbackMapProperty i₂ i₁ ψ g) : g ≫ f = 𝟙 _ := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      classical
      let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i₁)
      -- Equality on the unit sections suffices by the adjunction Hom bijection.
      apply (adj.homEquiv _ _).injective
      simp only [Adjunction.homEquiv_unit]
      apply Scheme.Modules.hom_ext
      intro U
      ext s₁
      obtain ⟨β, hβ⟩ := exists_kernelPushforwardMap i₂ i₁ ψ hc₂
      let s₂ := β.app U s₁
      let V := φ ⁻¹ᵁ (ψ ⁻¹ᵁ U)
      have hv : V = U := by
        change (φ ≫ ψ) ⁻¹ᵁ U = U
        rw [hcomp]
        rfl
      let s₁' : Γ(i₁.ker.toModules, V) :=
        i₁.ker.toModules.presheaf.map (eqToHom hv).op s₁
      have hs : i₁.ker.toModulesι.app V s₁' =
          φ.app (ψ ⁻¹ᵁ U) (i₂.ker.toModulesι.app (ψ ⁻¹ᵁ U) s₂) := by
        have hn := i₁.ker.toModulesι.val.naturality (eqToHom hv).op
        have hns := congrArg (fun q ↦ q s₁) hn
        change i₁.ker.toModulesι.app V s₁' =
          Z₁.presheaf.map (eqToHom hv).op (i₁.ker.toModulesι.app U s₁) at hns
        rw [hns, hβ]
        have hring := Scheme.Hom.congr_app hcomp U
        have hr := congrArg (fun q ↦ q (i₁.ker.toModulesι.app U s₁)) hring
        change φ.app (ψ ⁻¹ᵁ U) (ψ.app U (i₁.ker.toModulesι.app U s₁)) =
          Z₁.presheaf.map (eqToHom hv).op (i₁.ker.toModulesι.app U s₁) at hr
        exact hr.symm
      have hb : i₁ ⁻¹ᵁ U ≤ i₂ ⁻¹ᵁ (ψ ⁻¹ᵁ U) := by
        change i₁ ⁻¹ᵁ U ≤ (i₂ ≫ ψ) ⁻¹ᵁ U
        rw [hc₂]
      have ha : i₁ ⁻¹ᵁ U ≤ i₁ ⁻¹ᵁ V := by rw [hv]
      have hg' := hg U s₁ s₂ (hβ U s₁) (i₁ ⁻¹ᵁ U) le_rfl hb
      have hf' := hf (ψ ⁻¹ᵁ U) s₂ s₁' hs (i₁ ⁻¹ᵁ U) hb ha
      have hunit := (adj.unit.app i₁.ker.toModules).val.naturality (eqToHom hv).op
      have hu := congrArg (fun q ↦ q s₁) hunit
      change (adj.unit.app i₁.ker.toModules).app V s₁' =
        ((Scheme.Modules.tensorPullback i₁).obj i₁.ker.toModules).presheaf.map
          ((Opens.map i₁.base).map (eqToHom hv)).op
          ((adj.unit.app i₁.ker.toModules).app U s₁) at hu
      change f.app (i₁ ⁻¹ᵁ U) (g.app (i₁ ⁻¹ᵁ U)
        ((adj.unit.app i₁.ker.toModules).app U s₁)) =
          (adj.unit.app i₁.ker.toModules).app U s₁
      have hg'' : g.app (i₁ ⁻¹ᵁ U) ((adj.unit.app i₁.ker.toModules).app U s₁) =
          ((Scheme.Modules.tensorPullback i₂).obj i₂.ker.toModules).val.map (homOfLE hb).op
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i₂)).unit.app
              i₂.ker.toModules).app (ψ ⁻¹ᵁ U) s₂) := by
        change g.app (i₁ ⁻¹ᵁ U)
          (((Scheme.Modules.tensorPullback i₁).obj i₁.ker.toModules).presheaf.map
            (𝟙 _) ((adj.unit.app i₁.ker.toModules).app U s₁)) = _ at hg'
        simpa only [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using hg'
      rw [hg'', hf']
      change ((Scheme.Modules.tensorPullback i₁).obj i₁.ker.toModules).presheaf.map
        (homOfLE ha).op ((adj.unit.app i₁.ker.toModules).app V s₁') = _
      rw [hu, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      have hid : ((Opens.map i₁.base).map (eqToHom hv)).op ≫ (homOfLE ha).op = 𝟙 _ :=
        Subsingleton.elim _ _
      rw [hid, CategoryTheory.Functor.map_id]
      rfl

/-- An isomorphism between ambient schemes fixing a common closed subscheme induces
an isomorphism of the pulled back kernel ideals, with the canonical section formula.
No square-zero or universal property assumption is needed, and uniqueness is not
asserted here.
Source: Stacks Project, Section 01R1, Lemmas 29.32.2 and 29.32.3, and Tags 0095, 0096.
(blueprint: lem-weil-pbc-kernel-tensor-pullback-iso-exists).
Proof: Write Iⱼ = iⱼ.ker.toModules and Mⱼ = iⱼ* Iⱼ. For every open U of Z₂,
φ.app U maps the structure-sheaf image of s₂ in I₂(U) into the kernel of
 i₁.app (φ⁻¹ U), by the equation i₁ ≫ φ = i₂. The kernel inclusion is
injective, so there is a unique section β_U(s₂) of I₁(φ⁻¹ U) with that image.
The maps β_U are additive, φ.app U-linear, and commute with restrictions:
apply the injective kernel inclusion to check each identity in the structure
sheaf. They define an O_Z₂-linear map β : I₂ → φ_* I₁.
Compose β with φ_* of the normalized pullback unit I₁ → i₁_* M₁.
The pushforward composition comparison and hc identify its target with
 i₂_* M₁. Take its adjoint under the normalized i₂ pullback adjunction,
obtaining e_hom : M₂ → M₁. The unit/Hom-equivalence identity says on U that
 e_hom sends the i₂ unit of s₂ to the i₁ unit of β_U(s₂), transported
along the equality i₂⁻¹ U = i₁⁻¹(φ⁻¹ U). Thus if s₁ satisfies the displayed
kernel equation it equals β_U(s₂). Naturality of e_hom and the units gives
the required equation on every smaller W; the transports commute with both
restriction maps because the category of opens is a preorder.
Repeat this construction with inv φ, using i₂ ≫ inv φ = i₁. Applying the
kernel inclusions shows that the two β maps compose to the identity after
inverse-image transports. Consequently each composite of the two adjoint
module maps agrees with the identity on all pullback-unit sections. The
adjunction Hom bijection is injective, so both composites are identities.
These maps define the desired module isomorphism with the section formula.
Edge cases: identity φ gives the identity map; zero ideals and the empty closed
subscheme give zero modules. General closed immersions are allowed since
pullback of I is the conormal module I/I² (Lemma 29.32.2). -/
theorem exists_kernelTensorPullbackIso {Z Z₁ Z₂ : Scheme.{u}}
    (i₁ : Z ⟶ Z₁) (i₂ : Z ⟶ Z₂) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (φ : Z₁ ⟶ Z₂) [IsIso φ] (hc : i₁ ≫ φ = i₂) :
    ∃ e : (Scheme.Modules.tensorPullback i₂).obj i₂.ker.toModules ≅
        (Scheme.Modules.tensorPullback i₁).obj i₁.ker.toModules,
          ∀ (U : Z₂.Opens) (s₂ : Γ(i₂.ker.toModules, U))
            (s₁ : Γ(i₁.ker.toModules, φ ⁻¹ᵁ U)),
            i₁.ker.toModulesι.app (φ ⁻¹ᵁ U) s₁ =
              φ.app U (i₂.ker.toModulesι.app U s₂) →
            ∀ (W : Z.Opens) (a : W ≤ i₂ ⁻¹ᵁ U) (b : W ≤ i₁ ⁻¹ᵁ (φ ⁻¹ᵁ U)),
              e.hom.app W
                  (((Scheme.Modules.tensorPullback i₂).obj i₂.ker.toModules).val.map (homOfLE a).op
                    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
                      i₂)).unit.app i₂.ker.toModules).app U s₂)) =
                ((Scheme.Modules.tensorPullback i₁).obj i₁.ker.toModules).val.map (homOfLE b).op
                  (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
                    i₁)).unit.app i₁.ker.toModules).app (φ ⁻¹ᵁ U) s₁) := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      classical
      have hc' : i₂ ≫ inv φ = i₁ := by
        rw [← hc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      obtain ⟨f, hf⟩ := exists_kernelTensorPullbackMap i₁ i₂ φ hc
      obtain ⟨g, hg⟩ := exists_kernelTensorPullbackMap i₂ i₁ (inv φ) hc'
      have hgf : g ≫ f = 𝟙 _ :=
        kernelTensorPullbackMap_comp_id i₁ i₂ φ (inv φ) hc' (IsIso.hom_inv_id φ)
          f g hf hg
      have hfg : f ≫ g = 𝟙 _ :=
        kernelTensorPullbackMap_comp_id i₂ i₁ (inv φ) φ hc (IsIso.inv_hom_id φ)
          g f hg hf
      exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

end AlgebraicGeometry
