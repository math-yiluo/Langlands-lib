/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Pushout of a short exact sequence

Source: Stacks Project, Homology, Tags 010I (extensions, item (2)), 05PJ (pushout as
cokernel), 08N4 (monomorphisms in pushouts), and 08N3 (cokernels in pushouts)
(blueprint: lem-weil-pbc-pushout-short-exact-sequence).
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] Abelian.hasFiniteBiproducts

/-- Pushing out a short exact sequence along any map from its first object yields a short
exact sequence with the same last object. The pushout is the cokernel of `(u, -f)`, compatibly
with its two inclusions (whose square `u ≫ inl = f ≫ inr` is `pushout.condition`), and the
induced projection is unique. The vertical maps are
`(u, v, id)`.
Source: Stacks Project, Homology, Tags 010I, item (2), 05PJ (2), 08N4 (2), and 08N3 (2).
(blueprint: lem-weil-pbc-pushout-short-exact-sequence)

Proof: (1) Finite colimits give the pushout of `u` and `f`
(`lem-weil-pbc-abelian-exact-epi-cokernel` (d), `def-weil-pbc-category-colimit`).
(2) Biproducts and cokernels exist by `def-sp-abelian`. Maps from `I ⊞ B` are pairs `(j, k)`.
Such a map kills `(u, -f)` exactly when
`u ≫ j = f ≫ k`. The cokernel therefore has the pushout universal property, giving the
isomorphism compatible with both inclusions (`def-weil-pbc-category-colimit`).
(3) Since `f ≫ g = 0`, the maps `0 : I ⟶ C` and `g : B ⟶ C` induce a unique map `p` from
the pushout with the two stated composites (`def-weil-pbc-category-colimit`).
(4) A pushout of the monomorphism `f` is a monomorphism, so its opposite side `iota` is monic
(`lem-weil-pbc-abelian-pushout-mono`).
(5) The map `g` is a cokernel of `f` (`lem-weil-pbc-abelian-exact-epi-cokernel` (a)).
The pushout square identifies this cokernel with the cokernel of `iota`
(`lem-weil-pbc-pushout-cokernel-iso`, 08N3). Compose the latter cokernel map with the inverse
of this identification. It satisfies the same composites as `p`, so uniqueness makes it
`p`. Thus `p` is a cokernel of `iota`.
(6) A monomorphism followed by its cokernel is short exact
(`lem-weil-pbc-abelian-exact-epi-cokernel` (c)). The pushout relation and
`v ≫ p = g` give the two commuting squares of the morphism `(u, v, id)`. -/
theorem pushout_short_exact_sequence {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    (S : ShortComplex 𝒜) (hS : S.ShortExact) {I : 𝒜} (u : S.X₁ ⟶ I) :
    (∃ e : pushout u S.f ≅ cokernel (biprod.lift u (-S.f)),
      pushout.inl u S.f ≫ e.hom = biprod.inl ≫ cokernel.π (biprod.lift u (-S.f)) ∧
      pushout.inr u S.f ≫ e.hom = biprod.inr ≫ cokernel.π (biprod.lift u (-S.f))) ∧
    ∃ p : pushout u S.f ⟶ S.X₃, ∃ hz : pushout.inl u S.f ≫ p = 0,
      pushout.inr u S.f ≫ p = S.g ∧
      (∀ q : pushout u S.f ⟶ S.X₃,
        pushout.inr u S.f ≫ q = S.g → pushout.inl u S.f ≫ q = 0 → q = p) ∧
      (ShortComplex.mk (pushout.inl u S.f) p hz).ShortExact ∧
      ∃ m : S ⟶ ShortComplex.mk (pushout.inl u S.f) p hz,
        m.τ₁ = u ∧ m.τ₂ = pushout.inr u S.f ∧ m.τ₃ = 𝟙 S.X₃ := by
  have := hS.mono_f
  have := hS.epi_g
  -- Both objects are cokernels of the same biproduct lift.
  let h := Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout u S.f
  let e := h.coconePointUniqueUpToIso (cokernelIsCokernel (biprod.lift u (-S.f)))
  have he : biprod.desc (pushout.inl u S.f) (pushout.inr u S.f) ≫ e.hom =
      cokernel.π (biprod.lift u (-S.f)) := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom h
      (cokernelIsCokernel (biprod.lift u (-S.f))) WalkingParallelPair.one
  refine ⟨⟨e, ?_, ?_⟩, ?_⟩
  · simpa using congrArg (fun k ↦ biprod.inl ≫ k) he
  · simpa using congrArg (fun k ↦ biprod.inr ≫ k) he
  · let p : pushout u S.f ⟶ S.X₃ := pushout.desc 0 S.g (by simp)
    have hz : pushout.inl u S.f ≫ p = 0 := by simp [p]
    have hp : pushout.inr u S.f ≫ p = S.g := by simp [p]
    have hep : Epi p := epi_of_epi_fac hp
    let T := ShortComplex.mk (pushout.inl u S.f) p hz
    -- A map killing inl descends through S.g, then agrees on both pushout inclusions.
    have hc : IsColimit (CokernelCofork.ofπ p hz) := by
      apply CokernelCofork.IsColimit.ofπ'
      intro W k hk
      have hf : S.f ≫ (pushout.inr u S.f ≫ k) = 0 := by
        rw [← Category.assoc, ← pushout.condition, Category.assoc, hk, comp_zero]
      obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel
        (pushout.inr u S.f ≫ k) hf
      refine ⟨l, ?_⟩
      apply pushout.hom_ext
      · simp [← Category.assoc, hz, hk]
      · simpa [← Category.assoc, hp] using hl
    refine ⟨p, hz, hp, ?_, ?_, ?_⟩
    · intro q hq₁ hq₂
      exact pushout.hom_ext (hq₂.trans hz.symm) (hq₁.trans hp.symm)
    · exact ShortComplex.ShortExact.mk' (T.exact_of_g_is_cokernel hc)
        inferInstance hep
    · refine ⟨{ τ₁ := u, τ₂ := pushout.inr u S.f, τ₃ := 𝟙 S.X₃,
                comm₁₂ := pushout.condition,
                comm₂₃ := by simpa using hp }, rfl, rfl, rfl⟩

end CategoryTheory
