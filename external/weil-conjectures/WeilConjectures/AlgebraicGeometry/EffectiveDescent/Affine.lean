/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.AffineCoaction
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Invariant

/-!
# Affine faithfully flat descent of schemes

Let `p : X ⟶ Y` be a faithfully flat morphism of affine schemes and `V` an affine scheme over
`X` with a descent datum `D` relative to `p` (in the transport form
`CategoryTheory.Over.DescentDatum`). We show that `D` is effective.

The transport of the universal point `pr₁ : V ×_Y X ⟶ V` (lying over `pr₁ ≫ V.hom`) to the
second projection `pr₂ : V ×_Y X ⟶ X` is a morphism `γ : V ×_Y X ⟶ V` over `pr₂`, the
*universal transport* `CategoryTheory.Over.DescentDatum.univ`. By naturality every
transport is a pullback of `γ`, and the axioms of a descent datum say that `γ` is a counital and
coassociative coaction. Affine flat descent in coaction form
(`AlgebraicGeometry.exists_isPullback_of_coaction`) then descends `V`.

## Main statements

- `CategoryTheory.Over.DescentDatum.isEffective_of_isAffine`: descent data on affine schemes
  along a faithfully flat morphism of affine schemes are effective.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X}

/-- Any transport pulled back from the universal one is the composite with the universal
transport. -/
lemma transport_left_eq_comp_univ (D : DescentDatum p V) {T : Scheme.{u}}
    (g : T ⟶ Limits.pullback (V.hom ≫ p) p) {f₁ f₂ : T ⟶ X} (h : f₁ ≫ p = f₂ ≫ p)
    (hf₁ : f₁ = g ≫ Limits.pullback.fst _ _ ≫ V.hom) (hf₂ : f₂ = g ≫ Limits.pullback.snd _ _)
    (a : Over.mk f₁ ⟶ V) (ha : a.left = g ≫ Limits.pullback.fst _ _) :
    (D.transport f₁ f₂ h a).left = g ≫ D.univ :=
  D.transport_left_eq_comp g _ _ _ _ h hf₁ hf₂ a ha

/-- The counit identity for the universal transport. -/
lemma coactionUnit_univ (D : DescentDatum p V) :
    coactionUnit p V.hom ≫ D.univ = 𝟙 V.left := by
  rw [← D.transport_left_eq_comp_univ (coactionUnit p V.hom) (f₁ := V.hom)
    (f₂ := V.hom) rfl (by rw [Limits.pullback.lift_fst_assoc, Category.id_comp]) (by simp)
    (Over.homMk (𝟙 V.left)) (by simp), D.transport_self]
  rfl

/-- The coassociativity identity for the universal transport. -/
lemma coactionMap_univ (D : DescentDatum p V) :
    coactionMap p V.hom D.univ D.univ_hom ≫ D.univ =
      coactionForget p V.hom ≫ D.univ := by
  have h₁ : (Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _ ≫ V.hom) ≫ p =
      (Limits.pullback.fst (Limits.pullback.snd (V.hom ≫ p) p ≫ p) p ≫
        Limits.pullback.snd _ _) ≫ p := by
    simp [Limits.pullback.condition]
  have h₂ : (Limits.pullback.fst (Limits.pullback.snd (V.hom ≫ p) p ≫ p) p ≫
      Limits.pullback.snd _ _) ≫ p =
      Limits.pullback.snd (Limits.pullback.snd (V.hom ≫ p) p ≫ p) p ≫ p := by
    simp [Limits.pullback.condition]
  have e : D.transport _ _ h₁
      (Over.homMk (Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _) rfl) =
      Over.homMk (Limits.pullback.fst _ _ ≫ D.univ) (by simp) := by
    ext
    exact D.transport_left_eq_comp_univ _ h₁ (by simp) (by simp) _ (by simp)
  rw [← D.transport_left_eq_comp_univ _ h₂ (by simp) (by simp)
    (Over.homMk (Limits.pullback.fst _ _ ≫ D.univ) (by simp)) (by simp), ← e,
    D.transport_transport, ← D.transport_left_eq_comp_univ _ (h₁.trans h₂)
    (by simp) (by simp) (Over.homMk (Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _) rfl)
    (by simp)]

/-- **Affine faithfully flat descent**: descent data on affine schemes along a faithfully flat
morphism of affine schemes are effective.

The descended scheme is `Spec` of the ring of elements of `Γ(V)` invariant under the descent
datum, see `AlgebraicGeometry.exists_isPullback_of_coaction`. -/
theorem isEffective_of_isAffine {X Y : Scheme.{u}} {p : X ⟶ Y} [IsAffine X] [IsAffine Y]
    [Flat p] [Surjective p] {V : Over X} [IsAffine V.left] (D : DescentDatum p V) :
    D.IsEffective := by
  obtain ⟨N, -, nY, q, hq, hγq⟩ := exists_isPullback_of_coaction p V.hom D.univ
    D.univ_hom D.coactionUnit_univ D.coactionMap_univ
  refine ⟨Over.mk nY, q, hq, fun f₁ f₂ h a ↦ ?_⟩
  rw [D.transport_left_eq, Category.assoc, hγq, Limits.pullback.lift_fst_assoc]

end CategoryTheory.Over.DescentDatum
