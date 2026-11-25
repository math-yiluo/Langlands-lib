/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.AlgebraicGeometry.AlgebraizeFiniteStructureAlgebra
import WeilConjectures.AlgebraicGeometry.CoherentAlgebraAffineFiniteProper
import WeilConjectures.AlgebraicGeometry.AffineAlgebraReductionsCartesian
import WeilConjectures.AlgebraicGeometry.RelativeSpectrumAffineRealization

/-!
# Algebraization of finite schemes over thickenings of a proper scheme

Source: Cohomology of Schemes, Stacks Project, Lemma 09ZT (the proof via
Grothendieck existence, Theorem 088C and Remark 088F)
(blueprint: lem-weil-pbc-algebraize-finite-over-proper).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- (blueprint: lem-weil-pbc-algebraize-finite-over-proper) Let `A` be a
Noetherian `I`-adically complete ring, `S = Spec A`, `Sₙ = Spec (A/I^(n+1))`
(with `sn n : Sₙ ⟶ S` and transition maps `Sₙ ⟶ Sₙ₊₁` induced by the quotient maps),
and `f : X ⟶ S` separated and of finite type (`IsSeparated`, `LocallyOfFiniteType`,
`QuasiCompact`). Put `Xₙ = X ×_S Sₙ = pullback f (sn n)`, with the induced closed
immersions `ιn n : Xₙ ⟶ Xₙ₊₁` (`pullback.map`). Given finite `fnY n : Yₙ ⟶ Xₙ` and
`gn n : Yₙ ⟶ Yₙ₊₁` making every square cartesian, with `Yₙ₀ → S₀` proper, there is a
finite `g : Y ⟶ X` with `Y → S` proper, and isomorphisms `Y ×_X Xₙ ≅ Yₙ` over `Xₙ`
compatible with the maps `Yₙ ⟶ Yₙ₊₁` (through the induced map
`Y ×_X Xₙ ⟶ Y ×_X Xₙ₊₁`, characterized by its two projections).

Proof: by Grothendieck's existence theorem (Stacks 088C, in the form of Remark 088F)
the compatible system of coherent `𝒪_{Xₙ}`-algebras `fnY n _* 𝒪_{Yₙ}` is the system
of reductions of a coherent `𝒪_X`-algebra `𝒜`, whose support is proper over `S` since
the support of `Y₀` is; put `Y = Spec_X 𝒜`, finite over `X`, and the isomorphisms
come from `𝒜 ⊗ 𝒪_{Xₙ} ≅ fnY n _* 𝒪_{Yₙ}`. `Y` is proper over `S` because it is
finite over the proper (on the support) part of `X` (Lemma finite-pushforward-coherent). -/
theorem algebraize_finite_over_proper
    (A : Type u) [CommRing A] (I : Ideal A)
    [IsNoetherianRing A] [IsAdicComplete I A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Yn : ℕ → Scheme.{u})
    (fnY : ∀ n, Yn n ⟶ pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    [∀ n, IsFinite (fnY n)]
    (gn : ∀ n, Yn n ⟶ Yn (n + 1))
    (hcart : ∀ n, IsPullback (fnY n) (gn n)
      (pullback.map f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
        f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) (𝟙 X)
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))))
        (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
              Ideal.Quotient.factor_comp_mk]))
      (fnY (n + 1)))
    [IsProper (fnY 0 ≫ pullback.snd _ _)] :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X),
      IsFinite g ∧ IsProper (g ≫ f) ∧
      ∃ e : ∀ n, pullback g (pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) ⟶ Yn n,
        (∀ n, IsIso (e n) ∧ e n ≫ fnY n = pullback.snd _ _) ∧
        (∀ n, ∃ q : pullback g (pullback.fst f
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) ⟶
            pullback g (pullback.fst f
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))),
          q ≫ pullback.fst _ _ = pullback.fst _ _ ∧
          q ≫ pullback.snd _ _ = pullback.snd g _ ≫
            pullback.map f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
              f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) (𝟙 X)
              (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))))
              (𝟙 _) (by simp)
              (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                    Ideal.Quotient.factor_comp_mk]) ∧
          e n ≫ gn n = q ≫ e (n + 1)) := by
  classical
  let j (n : ℕ) := pullback.fst f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  let i (n : ℕ) := pullback.map f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
        f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) (𝟙 X)
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))))
        (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
              Ideal.Quotient.factor_comp_mk])
  have hi (n : ℕ) : i n ≫ j (n + 1) = j n := by
    simp [i, j]
  have hw (n : ℕ) : gn n ≫ (fnY (n + 1) ≫ j (n + 1)) = fnY n ≫ j n := by
    rw [← Category.assoc, ← (hcart n).w, Category.assoc]
    exact congrArg (fun k ↦ fnY n ≫ k) (hi n)
  obtain ⟨B, hqc, hcoh, hproper, b, hb, hcompat⟩ :=
    algebraize_finite_structure_algebra A I X f Yn fnY gn hcart hw
  obtain ⟨Y, g, hg, ⟨α⟩⟩ := exists_affine_structure_algebra X B hqc
  let : IsAffineHom g := hg
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : ∀ n, IsClosedImmersion (j n) := fun n ↦ by
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1))))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    exact MorphismProperty.pullback_fst f _ this
  have : ∀ n, IsAffineHom (fnY n) := fun n ↦ inferInstance
  obtain ⟨hfinite, hYproper⟩ := coherent_algebra_affine_finite_proper f g B α hcoh hproper
  obtain ⟨v, hv, hvg⟩ := affine_algebra_reductions_cartesian
    (fun n ↦ pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    Yn j fnY gn hw g B α b hb hcompat
  let e (n : ℕ) := (hv n).isoPullback.inv
  refine ⟨Y, g, hfinite, hYproper, e, ?_, ?_⟩
  · intro n
    exact ⟨inferInstanceAs (IsIso ((hv n).isoPullback.inv)),
      (hv n).isoPullback_inv_snd⟩
  · intro n
    let q : pullback g (j n) ⟶ pullback g (j (n + 1)) :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ i n) (by
        rw [Category.assoc, hi n, pullback.condition])
    refine ⟨q, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
    apply (hv (n + 1)).hom_ext
    · dsimp only [e]
      rw [Category.assoc, hvg n, (hv n).isoPullback_inv_fst,
        Category.assoc, (hv (n + 1)).isoPullback_inv_fst]
      exact (pullback.lift_fst _ _ _).symm
    · dsimp only [e]
      rw [Category.assoc, ← (hcart n).w, ← Category.assoc,
        (hv n).isoPullback_inv_snd, Category.assoc,
        (hv (n + 1)).isoPullback_inv_snd]
      exact (pullback.lift_snd _ _ _).symm

end AlgebraicGeometry
