/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Hilbert.Curve

/-!
# The iterated addition morphism `X^d ⟶ Hilb^d_{X/k}`

For a morphism `f : X ⟶ S` let `X^d = X ×_S ⋯ ×_S X` be its `d`-fold fibre power
(`AlgebraicGeometry.fiberPower`). A `T`-point `p = (p₁, …, p_d)` of `X^d` defines the divisor
`Γ_{p₁} + ⋯ + Γ_{p_d}` on `X_T`, the sum of the graphs of its coordinates
(`AlgebraicGeometry.fiberPowerGraphSum`).

For a geometrically integral smooth proper curve `X` over a field `k`, this is a point of
`Hilb^d_{X/k}(T)`, and the morphism `X^d ⟶ Hilb^d_{X/k}` classifying it, the iterated addition
morphism, is finite locally free of degree `d!` and surjective
(`AlgebraicGeometry.exists_iteratedAddition_hilbertPresheaf_curve`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

section FiberPower

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The `d`-fold fibre power `X^d = X ×_S ⋯ ×_S X` of `f : X ⟶ S`, as an `S`-scheme:
`X^0 = S` and `X^{d + 1} = X^d ×_S X`. -/
noncomputable def fiberPower : ℕ → Over S
  | 0 => Over.mk (𝟙 S)
  | d + 1 => Over.mk (pullback.snd (fiberPower d).hom f ≫ f)

/-- The projection `X^{d + 1} ⟶ X^d` forgetting the last coordinate. -/
noncomputable def fiberPowerFst (d : ℕ) : fiberPower f (d + 1) ⟶ fiberPower f d :=
  Over.homMk (pullback.fst (fiberPower f d).hom f) pullback.condition

/-- The last coordinate `X^{d + 1} ⟶ X`. -/
noncomputable def fiberPowerSnd (d : ℕ) : (fiberPower f (d + 1)).left ⟶ X :=
  pullback.snd (fiberPower f d).hom f

lemma fiberPowerSnd_comp (d : ℕ) : fiberPowerSnd f d ≫ f = (fiberPower f (d + 1)).hom :=
  rfl

/-- The divisor `Γ_{p₁} + ⋯ + Γ_{p_d}` on `X_T` of a `T`-point `p = (p₁, …, p_d)` of the fibre
power `X^d`: the product of the ideals of the graphs `Γ_{pᵢ} ⊆ X_T` of the coordinates
`pᵢ : T ⟶ X` of `p`. -/
noncomputable def fiberPowerGraphSum :
    ∀ {d : ℕ} {T : Over S}, (T ⟶ fiberPower f d) → (Limits.pullback f T.hom).IdealSheafData
  | 0, _, _ => ⊤
  | d + 1, T, p => fiberPowerGraphSum (p ≫ fiberPowerFst f d) *
      (pullback.lift (p.left ≫ fiberPowerSnd f d) (𝟙 T.left)
        (by rw [Category.id_comp, Category.assoc, fiberPowerSnd_comp]; exact Over.w p) :
          T.left ⟶ Limits.pullback f T.hom).ker

end FiberPower

section Curve

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The iterated addition morphism.** Let `X` be a geometrically integral smooth proper curve
over `k`, and `H` a `k`-scheme representing `Hilb^d_{X/k}`. The morphism `π : X^d ⟶ H` sending a
point `(x₁, …, x_d)` of the fibre power to the divisor `x₁ + ⋯ + x_d` (the product of the ideals
of the graphs, `AlgebraicGeometry.fiberPowerGraphSum`) is finite locally free of degree `d!` and
surjective.

By induction on `d`: `π_{d + 1}` is `π_d × 𝟙 : X^d ×_k X ⟶ H_d ×_k X`, a base change of `π_d`,
followed by the addition morphism `H_d ×_k X ⟶ H_{d + 1}`
(`AlgebraicGeometry.exists_addition_hilbertPresheaf`), which is finite locally free of degree
`d + 1`.

(blueprint: `theorem-hilbert-schemes-points-smooth-curve--1`, complements) -/
theorem exists_iteratedAddition_hilbertPresheaf_curve [SmoothOfRelativeDimension 1 f]
    [IsProper f] [GeometricallyIntegral f] (d : ℕ) (H : Over (Spec (.of k)))
    (e : (hilbertPresheaf f d).RepresentableBy H) :
    ∃ π : fiberPower f d ⟶ H, IsFinite π.left ∧ Flat π.left ∧
      LocallyOfFinitePresentation π.left ∧ Surjective π.left ∧
      (∀ t, π.left.finrank t = d.factorial) ∧
      ∀ (T : Over (Spec (.of k))) (p : T ⟶ fiberPower f d),
        (e.homEquiv (p ≫ π)).1 = fiberPowerGraphSum f p := by
  induction d generalizing H with
  | zero =>
    have := isIso_of_representableBy_hilbertPresheaf_zero f e
    let π : fiberPower f 0 ⟶ H := Over.homMk (inv H.hom) (IsIso.inv_hom_id _)
    have : IsIso π.left := inferInstanceAs (IsIso (inv H.hom))
    refine ⟨π, inferInstance, inferInstance, inferInstance, inferInstance, fun t ↦ ?_,
      fun T p ↦ (e.homEquiv (p ≫ π)).2.eq_top_of_zero⟩
    rw [Scheme.Hom.finrank_eq_one_of_isIso]
    rfl
  | succ d ih =>
    obtain ⟨Hd, ⟨ed⟩⟩ := isRepresentable_hilbertPresheaf_curve f d
    obtain ⟨πd, hfin, hflat, hlfp, hsurj, hrank, hpts⟩ := ih Hd ed
    obtain ⟨a, ha, hafin, haflat, halfp, harank, haeq⟩ :=
      exists_addition_hilbertPresheaf f d Hd H ed e
    -- `m = π_d × 𝟙 : X^d ×_k X ⟶ H_d ×_k X`, a base change of `π_d`
    let m : (fiberPower f (d + 1)).left ⟶ Limits.pullback Hd.hom f :=
      pullback.map (fiberPower f d).hom f Hd.hom f πd.left (𝟙 X) (𝟙 _) (by simp [Over.w πd])
        (by simp)
    have hm₁ : m ≫ pullback.fst Hd.hom f = pullback.fst _ _ ≫ πd.left := pullback.lift_fst _ _ _
    have hm₂ : m ≫ pullback.snd Hd.hom f = fiberPowerSnd f d := by
      simp [m, fiberPowerSnd]
    have pbm : IsPullback (pullback.fst (fiberPower f d).hom f) m πd.left
        (pullback.fst Hd.hom f) := by
      refine IsPullback.of_bot ?_ hm₁.symm (IsPullback.of_hasPullback Hd.hom f)
      rw [hm₂, Over.w πd]
      exact IsPullback.of_hasPullback _ _
    have : IsFinite m := MorphismProperty.of_isPullback (P := @IsFinite) pbm hfin
    have : Flat m := MorphismProperty.of_isPullback (P := @Flat) pbm hflat
    have : LocallyOfFinitePresentation m :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) pbm hlfp
    have : Surjective m := MorphismProperty.of_isPullback (P := @Surjective) pbm hsurj
    have hmrank (y : _) : m.finrank y = d.factorial := by
      rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ pbm, hrank]
    have : IsFinite a := hafin
    have : Flat a := haflat
    have : LocallyOfFinitePresentation a := halfp
    have : Surjective a := (Scheme.Hom.one_le_finrank_iff_surjective a).mp fun y ↦ by
      simp [harank y]
    let π : fiberPower f (d + 1) ⟶ H := Over.homMk (m ≫ a) (by
      rw [Category.assoc, ha, ← Category.assoc, hm₂, fiberPowerSnd_comp])
    refine ⟨π, inferInstanceAs (IsFinite (m ≫ a)), inferInstanceAs (Flat (m ≫ a)),
      inferInstanceAs (LocallyOfFinitePresentation (m ≫ a)), inferInstanceAs (Surjective (m ≫ a)),
      fun t ↦ ?_, fun T p ↦ ?_⟩
    · change (m ≫ a).finrank t = _
      rw [Scheme.Hom.finrank_comp_of_forall_finrank_eq m a hmrank t, harank,
        Nat.factorial_succ, mul_comm]
    · -- the point `p ≫ π` is the sum of the point `p ≫ π_d` and the graph of the last coordinate
      have hx : (p.left ≫ fiberPowerSnd f d) ≫ f = T.hom := by
        rw [Category.assoc, fiberPowerSnd_comp]
        exact Over.w p
      have h := haeq T ((p ≫ fiberPowerFst f d) ≫ πd) (p.left ≫ fiberPowerSnd f d) hx (p ≫ π)
        (by
          change p.left ≫ m ≫ a = _
          rw [← Category.assoc]
          congr 1
          apply pullback.hom_ext
          · simp [hm₁, fiberPowerFst]
          · simp [hm₂])
      rw [h, hpts]
      rfl

end Curve

end AlgebraicGeometry
