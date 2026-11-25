/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

/-! # Cover refinements along a stage map -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

/-- Pullback of a cover along any stage map covers both that stage and the limit.
Source: Stacks Project, Tag 03Q6, base-change stability of coverings.
(blueprint: lem-weil-pbc-affine-open-inverse-image-compatible-refinement-data).

Proof: Set V'_b to the categorical pullback of v_b and D(f) in X.Etale, with
projections v'_b to D(k) and γ_b to V_b. Their equation is the pullback equation,
and the stage covering follows by stability under base change. Define π'_b as
p*(γ_b) followed by π_b. Since D(j) and D(k) embed openly into X and p factors
through each, their base changes to c.pt are terminal. Consequently p*(D(f)) is
an isomorphism. Base change preserves pullbacks, so each p*(γ_b) is an isomorphism.
The composite family π' therefore generates the same covering sieve as π.
This proof also handles empty covering families and uses neither sections nor
any equality-locus argument. -/
theorem affineOpenSections_refinement_data
    {X : Scheme.{u + 1}} {J : Type (u + 1)} [SmallCategory J]
    (D : J ⥤ X.Etale) [∀ j, IsOpenImmersion (D.obj j).hom]
    (c : Cone (D ⋙ Scheme.Etale.forget X ⋙ Over.forget X))
    (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ (D.obj j).hom = p)
    (j k : J) (f : k ⟶ j) (B : Type (u + 1))
    (V : B → X.Etale) (v : ∀ b, V b ⟶ D.obj j)
    (π : ∀ b, p.Etale.obj (V b) ⟶ Scheme.Etale.mk (𝟙 c.pt))
    (hv : Sieve.ofArrows V v ∈ X.smallEtaleTopology (D.obj j))
    (hπ : Sieve.ofArrows (fun b ↦ p.Etale.obj (V b)) π ∈
      c.pt.smallEtaleTopology (Scheme.Etale.mk (𝟙 c.pt))) :
    ∃ (V' : B → X.Etale) (v' : ∀ b, V' b ⟶ D.obj k) (γ : ∀ b, V' b ⟶ V b)
      (π' : ∀ b, p.Etale.obj (V' b) ⟶ Scheme.Etale.mk (𝟙 c.pt)),
      (∀ b, v' b ≫ D.map f = γ b ≫ v b) ∧
      Sieve.ofArrows V' v' ∈ X.smallEtaleTopology (D.obj k) ∧
      Sieve.ofArrows (fun b ↦ p.Etale.obj (V' b)) π' ∈
        c.pt.smallEtaleTopology (Scheme.Etale.mk (𝟙 c.pt)) ∧
      (∀ b, p.Etale.map (γ b) ≫ π b = π' b) := by
  classical
  have hsnd (i : J) : IsIso (pullback.snd (D.obj i).hom p) := by
    let σ := pullback.lift (c.π.app i) (𝟙 c.pt) (by simpa using hp i)
    let : IsSplitEpi (pullback.snd (D.obj i).hom p) :=
      IsSplitEpi.mk' ⟨σ, by simp [σ]⟩
    exact isIso_of_mono_of_isSplitEpi _
  let (i : J) : IsIso (pullback.snd (D.obj i).hom p) := hsnd i
  have : IsIso (p.Etale.map (D.map f)).left :=
    IsIso.of_isIso_fac_right (p.etale_map_left_comp_snd (D.map f))
  have : IsIso ((Scheme.Etale.forget c.pt ⋙ Over.forget c.pt).map
      (p.Etale.map (D.map f))) := by
    change IsIso (p.Etale.map (D.map f)).left
    infer_instance
  have : IsIso (p.Etale.map (D.map f)) :=
    isIso_of_reflects_iso (p.Etale.map (D.map f))
      (Scheme.Etale.forget c.pt ⋙ Over.forget c.pt)
  let V' (b : B) := pullback (v b) (D.map f)
  let v' (b : B) : V' b ⟶ D.obj k := pullback.snd _ _
  let γ (b : B) : V' b ⟶ V b := pullback.fst _ _
  let π' (b : B) := p.Etale.map (γ b) ≫ π b
  have hsq (b : B) : v' b ≫ D.map f = γ b ≫ v b := pullback.condition.symm
  have (b : B) : IsIso (p.Etale.map (γ b)) :=
    ((IsPullback.of_hasPullback (v b) (D.map f)).map p.Etale).isIso_fst_of_isIso
  refine ⟨V', v', γ, π', hsq, ?_, ?_, fun _ ↦ rfl⟩
  · rw [Sieve.ofArrows_eq_pullback_of_isPullback v
      (fun b ↦ (IsPullback.of_hasPullback (v b) (D.map f)).flip)]
    exact X.smallEtaleTopology.pullback_stable (D.map f) hv
  · apply c.pt.smallEtaleTopology.superset_covering (S := Sieve.ofArrows _ π) _ hπ
    intro W a ha
    rw [Sieve.mem_ofArrows_iff] at ha ⊢
    obtain ⟨b, q, rfl⟩ := ha
    exact ⟨b, q ≫ inv (p.Etale.map (γ b)), by simp [π']⟩

