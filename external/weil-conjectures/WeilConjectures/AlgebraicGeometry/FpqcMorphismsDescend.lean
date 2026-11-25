/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic

/-!
# Descent of morphisms along an fpqc covering

Source: Stacks Project, Descent, Lemma Tag 02W0 (blueprint: lem-galois-fpqc-morphisms-descend).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

namespace Scheme

variable {S X U W : Scheme.{u}}

/-- The canonical comparison isomorphism `pr₀^*(U ×ₛ X) ≅ pr₁^*(U ×ₛ X)` over `X ×ₛ X`:
the composite of the canonical isomorphisms of both sides with `U ×ₛ (X ×ₛ X)`, which exist
since `pr₀ ≫ f = pr₁ ≫ f`.
Source: Stacks Project, Descent, Definition Tag 023V
(blueprint: lem-galois-fpqc-morphisms-descend). -/
noncomputable def canonicalDescentIso (pU : U ⟶ S) (f : X ⟶ S) :
    pullback (pullback.snd pU f) (pullback.fst f f) ≅
      pullback (pullback.snd pU f) (pullback.snd f f) :=
  pullbackLeftPullbackSndIso pU f (pullback.fst f f) ≪≫
    pullback.congrHom rfl pullback.condition ≪≫
    (pullbackLeftPullbackSndIso pU f (pullback.snd f f)).symm

/-- The morphism induced on fibre products by a morphism over `S`.
Source: Stacks Project, Descent, Definition Tag 023V
(blueprint: lem-galois-fpqc-morphisms-descend). -/
noncomputable def baseChangeMap (pU : U ⟶ S) (pW : W ⟶ S) (f : X ⟶ S)
    (α : U ⟶ W) (hα : pU = α ≫ pW) :
    pullback pU f ⟶ pullback pW f :=
  pullback.map pU f pW f α (𝟙 X) (𝟙 S) hα (by simp)

/-- The base change of an `S`-morphism is a morphism of descent data.
Source: Stacks Project, Descent, Definition Tag 023V
(blueprint: lem-galois-fpqc-morphisms-descend). -/
theorem baseChangeMap_compatible (pU : U ⟶ S) (pW : W ⟶ S) (f : X ⟶ S)
    (α : U ⟶ W) (hα : pU = α ≫ pW) :
    ∃ hβ : (baseChangeMap pU pW f α hα) ≫ pullback.snd pW f = pullback.snd pU f,
      pullback.map (pullback.snd pU f) (pullback.fst f f)
            (pullback.snd pW f) (pullback.fst f f)
            (baseChangeMap pU pW f α hα) (𝟙 _) (𝟙 _) (by simp [baseChangeMap]) (by simp) ≫
          (canonicalDescentIso pW f).hom =
        (canonicalDescentIso pU f).hom ≫
        pullback.map (pullback.snd pU f) (pullback.snd f f)
            (pullback.snd pW f) (pullback.snd f f)
            (baseChangeMap pU pW f α hα) (𝟙 _) (𝟙 _) (by simpa using hβ.symm) (by simp) := by
  refine ⟨by simp [baseChangeMap], ?_⟩
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [canonicalDescentIso, baseChangeMap]
    · simp [canonicalDescentIso, baseChangeMap]
  · simp [canonicalDescentIso, baseChangeMap]

private theorem effectiveEpi_of_fpqc_singleton {A B : Scheme.{u}} (q : A ⟶ B)
    (hq : Presieve.singleton q ∈ fpqcPrecoverage B) : EffectiveEpi q := by
  rw [← Sieve.effectiveEpimorphic_singleton,
    Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  intro Z
  exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
    (Precoverage.generate_mem_toGrothendieck hq)

/-- Morphisms of schemes over `S` descend uniquely along an fpqc singleton.
Source: Stacks Project, Descent, Lemma Tag 02W0 (blueprint: lem-galois-fpqc-morphisms-descend).

The proof pulls back the fpqc covering to `U`, translates the compatibility equation to
equality on the double overlap, applies fpqc representable descent, verifies the descended
morphism is over `S`, and proves reconstruction and uniqueness by the pullback universal
property. -/
theorem fpqc_morphisms_descend (f : X ⟶ S)
    (hfpqc : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    (pU : U ⟶ S) (pW : W ⟶ S) :
    Function.Bijective
      (fun (α : {α : U ⟶ W // α ≫ pW = pU}) =>
        ⟨baseChangeMap pU pW f α α.property.symm,
          baseChangeMap_compatible pU pW f α α.property.symm⟩ :
        {α : U ⟶ W // α ≫ pW = pU} →
          {β : pullback pU f ⟶ pullback pW f //
            ∃ hβ : β ≫ pullback.snd pW f = pullback.snd pU f,
              pullback.map (pullback.snd pU f) (pullback.fst f f)
                    (pullback.snd pW f) (pullback.fst f f) β (𝟙 _) (𝟙 _)
                    (by simpa using hβ.symm) (by simp) ≫
                  (canonicalDescentIso pW f).hom =
                (canonicalDescentIso pU f).hom ≫
                pullback.map (pullback.snd pU f) (pullback.snd f f)
                    (pullback.snd pW f) (pullback.snd f f) β (𝟙 _) (𝟙 _)
                    (by simpa using hβ.symm) (by simp)}) := by
  have hq : Presieve.singleton (pullback.fst pU f) ∈ fpqcPrecoverage U := by
    rw [← Presieve.ofArrows_pUnit.{0}] at hfpqc ⊢
    exact Precoverage.mem_coverings_of_isPullback (fun _ : PUnit.{1} ↦ f) hfpqc pU
      (fun _ ↦ pullback.fst pU f) (fun _ ↦ pullback.snd pU f)
      (fun _ ↦ IsPullback.of_hasPullback pU f)
  let : EffectiveEpi (pullback.fst pU f) := effectiveEpi_of_fpqc_singleton _ hq
  constructor
  · intro α α' h
    apply Subtype.ext
    apply (cancel_epi (pullback.fst pU f)).mp
    have hh := congrArg (fun β ↦ β.val ≫ pullback.fst pW f) h
    simpa [baseChangeMap] using hh
  · intro β
    obtain ⟨hβ, hc⟩ := β.property
    have he : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ pullback pU f),
        g₁ ≫ pullback.fst pU f = g₂ ≫ pullback.fst pU f →
        g₁ ≫ β.val ≫ pullback.fst pW f = g₂ ≫ β.val ≫ pullback.fst pW f := by
      intro Z g₁ g₂ hg
      let t : Z ⟶ pullback f f := pullback.lift
        (g₁ ≫ pullback.snd pU f) (g₂ ≫ pullback.snd pU f) (by
          simp only [Category.assoc, ← pullback.condition]
          simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ pU) hg)
      let l : Z ⟶ pullback (pullback.snd pU f) (pullback.fst f f) :=
        pullback.lift g₁ t (by simp [t])
      have hl : l ≫ (canonicalDescentIso pU f).hom ≫
          pullback.fst (pullback.snd pU f) (pullback.snd f f) = g₂ := by
        apply pullback.hom_ext
        · simpa [l, canonicalDescentIso] using hg
        · simp [l, t, canonicalDescentIso]
      have hh := congrArg (fun k ↦ l ≫ k ≫
        pullback.fst (pullback.snd pW f) (pullback.snd f f) ≫ pullback.fst pW f) hc
      have hcW : (canonicalDescentIso pW f).hom ≫
          pullback.fst (pullback.snd pW f) (pullback.snd f f) ≫ pullback.fst pW f =
          pullback.fst (pullback.snd pW f) (pullback.fst f f) ≫ pullback.fst pW f := by
        simp [canonicalDescentIso]
      simp only [Category.assoc, hcW] at hh
      simp only [pullback.map, pullback.lift_fst_assoc, Category.assoc] at hh
      have hl' := congrArg (fun k ↦ k ≫ β.val ≫ pullback.fst pW f) hl
      simp only [Category.assoc] at hl'
      rw [hl'] at hh
      simpa [l] using hh
    let α : U ⟶ W := EffectiveEpi.desc (pullback.fst pU f)
      (β.val ≫ pullback.fst pW f) he
    have hα : pullback.fst pU f ≫ α = β.val ≫ pullback.fst pW f :=
      EffectiveEpi.fac _ _ he
    have hαS : α ≫ pW = pU := by
      apply (cancel_epi (pullback.fst pU f)).mp
      rw [← Category.assoc, hα, Category.assoc, pullback.condition,
        ← Category.assoc, hβ, ← pullback.condition]
    refine ⟨⟨α, hαS⟩, ?_⟩
    apply Subtype.ext
    apply pullback.hom_ext
    · simpa [baseChangeMap] using hα
    · simpa [baseChangeMap] using hβ.symm

end Scheme

end AlgebraicGeometry
