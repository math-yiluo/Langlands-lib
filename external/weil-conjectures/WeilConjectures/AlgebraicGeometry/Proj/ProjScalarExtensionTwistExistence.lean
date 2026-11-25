/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistData
import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistChart
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

/-! # ProjScalarExtensionTwistExistence

## References

* Stacks Project, Constructions, Tags 01N2, 01MY and 01MZ
* Stacks Project, Constructions, Tags 01N2 and 01MY
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

section GradedMap

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

open HomogeneousLocalization ProjectiveSpectrum.Twist

/-- The ordinary localization map preserves each homogeneous degree. -/
private noncomputable def twistFiberMap
    (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map ψ (HomogeneousIdeal.irrelevant 𝒜))
    (j : ℤ) (x : Proj ℬ) :
    fiber 𝒜 j (ProjectiveSpectrum.comap ψ hψ x) →+ fiber ℬ j x where
  toFun s := ⟨Localization.localRingHom _ _ ψ.toRingHom rfl s.1, by
    rcases s.2 with h | ⟨i, k, a, b, hb, ha, hb', hik, hs⟩
    · exact Or.inl (by rw [h, map_zero])
    · refine Or.inr ⟨i, k, ψ a, ψ b, hb, ψ.map_mem ha, ψ.map_mem hb', hik, ?_⟩
      rw [hs, Localization.localRingHom_mk]
      rfl⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' s t := Subtype.ext (map_add _ _ _)

/-- The homogeneous fibre map sends a/b to psi(a)/psi(b). -/
private theorem twistFiberMap_mk
    (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map ψ (HomogeneousIdeal.irrelevant 𝒜))
    (j : ℤ) (x : Proj ℬ) {i k : ℕ}
    (a : 𝒜 i) (b : 𝒜 k)
    (hb : (b : A) ∉ (ProjectiveSpectrum.comap ψ hψ x).asHomogeneousIdeal.toIdeal)
    (hik : (i : ℤ) = k + j) :
    twistFiberMap ψ hψ j x (degreePart.mk a b hb hik) =
      degreePart.mk (ψ.gradedAddHom i a) (ψ.gradedAddHom k b) hb hik := by
  apply Subtype.ext
  exact Localization.localRingHom_mk _ _ _ _ _ _

/-- Apply the homogeneous localization map pointwise to locally-fraction sections. -/
private noncomputable def twistSectionMap
    (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map ψ (HomogeneousIdeal.irrelevant 𝒜))
    (j : ℤ) (U : (Proj 𝒜).Opens)
    (s : Γ(twist 𝒜 j, U)) : Γ(twist ℬ j, map ψ hψ ⁻¹ᵁ U) :=
  ⟨fun x ↦ twistFiberMap ψ hψ j x.1 (s.1 ⟨_, x.2⟩), by
    rintro ⟨x, hx⟩
    obtain ⟨W, hxW, e, i, k, hik, a, b, hb, hw⟩ := s.2 ⟨_, hx⟩
    refine ⟨(map ψ hψ ⁻¹ᵁ W) ⊓ (map ψ hψ ⁻¹ᵁ U), ⟨hxW, hx⟩,
      Opens.infLERight _ _, i, k, hik, ψ.gradedAddHom i a, ψ.gradedAddHom k b,
      fun y ↦ hb ⟨_, y.2.1⟩, fun y ↦ ?_⟩
    change twistFiberMap ψ hψ j y.1 (s.1 (e ⟨_, y.2.1⟩)) = _
    exact (congrArg (twistFiberMap ψ hψ j y.1) (hw ⟨_, y.2.1⟩)).trans
      (twistFiberMap_mk ψ hψ j y.1 a b _ hik)⟩

/-- The pointwise fraction map is semilinear over the Proj structure-sheaf map. -/
private theorem twistSectionMap_smul
    (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map ψ (HomogeneousIdeal.irrelevant 𝒜))
    (j : ℤ) (U : (Proj 𝒜).Opens) (c : Γ(Proj 𝒜, U)) (s : Γ(twist 𝒜 j, U)) :
    twistSectionMap ψ hψ j U (c • s) =
      (map ψ hψ).app U c • twistSectionMap ψ hψ j U s := by
  apply Subtype.ext
  funext x
  apply Subtype.ext
  exact (map_mul (Localization.localRingHom _ _ ψ.toRingHom rfl)
    (c.1 ⟨_, x.2⟩).val (s.1 ⟨_, x.2⟩).val).trans
      (congrArg (fun z ↦ z * (twistFiberMap ψ hψ j x.1 (s.1 ⟨_, x.2⟩)).val)
        (HomogeneousLocalization.val_localRingHom
          (f := ψ) (hIJ := rfl) (c.1 ⟨_, x.2⟩)).symm)

/-- The pointwise fraction maps form a morphism to the pushforward twist. -/
private noncomputable def twistPushforwardMap
    (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map ψ (HomogeneousIdeal.irrelevant 𝒜))
    (j : ℤ) :
    twist 𝒜 j ⟶ (pushforward (map ψ hψ)).obj (twist ℬ j) :=
  ⟨PresheafOfModules.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := twistSectionMap ψ hψ j U.unop
          map_zero' := by
            apply Subtype.ext
            funext x
            exact map_zero _
          map_add' := by
            intro s t
            apply Subtype.ext
            funext x
            exact map_add _ _ _ }
      naturality := fun _ _ _ ↦ rfl }
    (fun U c s ↦ twistSectionMap_smul ψ hψ j U.unop c s)⟩

/-- Transpose the concrete fraction map by the section-normalized tensor adjunction. -/
private noncomputable def twistPullbackMap
    (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map ψ (HomogeneousIdeal.irrelevant 𝒜))
    (j : ℤ) :
    (tensorPullback (map ψ hψ)).obj (twist 𝒜 j) ⟶ twist ℬ j :=
  ((tensorPullbackSectionAdjunction (map ψ hψ)).homEquiv _ _).symm
    (twistPushforwardMap ψ hψ j)

/-- The adjoint comparison on the actual section 1 tensor s is the pointwise fraction map. -/
private theorem twistPullbackMap_section
    (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map ψ (HomogeneousIdeal.irrelevant 𝒜))
    (j : ℤ) (U : (Proj 𝒜).Opens)
    (s : Γ(twist 𝒜 j, U)) (x : map ψ hψ ⁻¹ᵁ U) :
    ((twistPullbackMap ψ hψ j).app (map ψ hψ ⁻¹ᵁ U)
      (tensorPullbackSection (map ψ hψ) (twist 𝒜 j) U s)).1 x =
        twistFiberMap ψ hψ j x.1 (s.1 ⟨_, x.2⟩) := by
  have h := ((tensorPullbackSectionAdjunction (map ψ hψ)).homEquiv _ _).apply_symm_apply
    (twistPushforwardMap ψ hψ j)
  rw [Adjunction.homEquiv_unit] at h
  have hn : ((tensorPullbackSectionAdjunction (map ψ hψ)).unit.app
      (twist 𝒜 j)).app U s =
        tensorPullbackSection (map ψ hψ) (twist 𝒜 j) U s :=
    (Classical.choose_spec
      (existsUnique_tensorPullbackSectionAdjunction (map ψ hψ))).1 (twist 𝒜 j) U s
  have he := congrArg (fun f ↦ (f.app U s).1 x) h
  change (((twistPullbackMap ψ hψ j).app _)
    (((tensorPullbackSectionAdjunction (map ψ hψ)).unit.app _).app U s)).1 x = _ at he
  exact (congrArg (fun t ↦ ((twistPullbackMap ψ hψ j).app _ t).1 x) hn.symm).trans he

end GradedMap

/-- The normalized twist comparison exists, independently of its uniqueness and coherence. -/
theorem scalarExtension_twist_exists
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedRing 𝒜] [GradedRing ℬ]
    (β : TensorProduct R S A ≃ₐ[S] B) (ψ : 𝒜 →+*ᵍ ℬ)
    (hβψ : ∀ a : A, β (TensorProduct.tmul R (1 : S) a) = ψ a)
    (hgraded : ∀ n : ℕ, ℬ n = Submodule.span S (ψ '' (𝒜 n : Set A)))
    (r : Proj ℬ ⟶ Proj 𝒜)
    (hchart : ∀ (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n),
      awayι ℬ (ψ f) (ψ.map_mem hf) hn ≫ r =
        Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f)) ≫
          awayι 𝒜 f hf hn):
    ∃ θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j,
      IsScalarExtensionTwistComparison ψ r θ := by
  classical
  have hψ : HomogeneousIdeal.irrelevant ℬ ≤
      HomogeneousIdeal.map ψ (HomogeneousIdeal.irrelevant 𝒜) := by
    change (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤ _
    apply (HomogeneousIdeal.toIdeal_irrelevant_le ℬ).mpr
    intro n hn b hb
    rw [hgraded n] at hb
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact Ideal.mem_map_of_mem ψ (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn ha)
    | zero => exact Ideal.zero_mem _
    | add x y hx hy hx' hy' => exact Ideal.add_mem _ hx' hy'
    | smul s x hx hx' =>
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ hx'
  have hr : r = map ψ hψ := by
    apply (mapAffineOpenCover ψ hψ).openCover.hom_ext
    intro i
    exact (hchart i.1 i.2 i.2.2 i.1.2).trans
      (awayι_comp_map ψ hψ i.1.2 i.2 i.2.2).symm
  subst r
  have hIso (j : ℤ) : IsIso (twistPullbackMap ψ hψ j) := by
    apply Hom.isIso_of_forall_bijective_app
    intro x
    let C := (mapAffineOpenCover ψ hψ).openCover
    let i := C.idx x
    have hx : x ∈ (C.f i).opensRange := C.covers x
    refine ⟨basicOpen ℬ (ψ i.2), ?_, ?_⟩
    · simpa only [C, Scheme.AffineOpenCover.openCover_f, mapAffineOpenCover_f,
        opensRange_awayι] using hx
    · intro W hW
      apply scalarExtension_twistMap_basicOpen_bijective 𝒜 ℬ β ψ hβψ hgraded hψ j
        (twistPullbackMap ψ hψ j) ?_ i.1 i.2 i.2.2 i.1.2 W hW
      intro U s x
      exact congrArg Subtype.val (twistPullbackMap_section ψ hψ j U s x)
  let θ (j : ℤ) := @asIso _ _ _ _ (twistPullbackMap ψ hψ j) (hIso j)
  refine ⟨θ, ?_⟩
  intro j i k a b ha hb hik U hU s hs c x
  have he := congrArg Subtype.val (twistPullbackMap_section ψ hψ j U s x)
  have h := congrArg (Localization.localRingHom
    (ProjectiveSpectrum.comap ψ hψ x.1).asHomogeneousIdeal.toIdeal
    x.1.asHomogeneousIdeal.toIdeal ψ.toRingHom rfl) (hs ⟨_, x.2⟩)
  simp only [map_mul, Localization.localRingHom_mk,
    GradedRingHom.coe_toRingHom, OneMemClass.coe_one, map_one] at h
  change (c.1 x).val *
    (((twistPullbackMap ψ hψ j).app _
      (tensorPullbackSection (map ψ hψ) (twist 𝒜 j) U s)).1 x).val *
        Localization.mk (ψ b) 1 = (c.1 x).val * Localization.mk (ψ a) 1
  rw [he, mul_assoc]
  exact congrArg (fun z ↦ (c.1 x).val * z) h

end AlgebraicGeometry.Proj
