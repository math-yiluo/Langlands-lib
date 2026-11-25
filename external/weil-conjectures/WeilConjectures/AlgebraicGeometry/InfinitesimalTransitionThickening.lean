/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.Thickening
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Successive infinitesimal fibres are related by a finite order thickening and
universal homeomorphism.
Source: Stacks Project, Tag 0GS2, construction of the infinitesimal fibres; Tags 04EX,
09ZU, and 04DF.
(blueprint: lem-weil-pbc-infinitesimal-transition-thickening).

Proof: the map A/I^(n+2) → A/I^(n+1) is surjective, with kernel the image of I^(n+1).
Its kernel has square zero: I^(2*(n+1)) is contained in I^(n+2), since n+2 ≤ 2*(n+1).
Consequently its spectrum map is a closed immersion defined by a square-zero ideal.
Every prime contains this nilpotent ideal, so the spectrum map is surjective. The
map displayed below is its base change along X_(n+1) → Spec(A/I^(n+2)), by pullback
pasting. Closed immersions, square-zero defining ideals, and surjectivity persist
under base change. Thus it is a first order, hence finite order, thickening and a
surjective closed immersion. The latter is a universal homeomorphism by Tag 04DF. -/
theorem infinitesimal_transition_thickening
    {A : Type u} [CommRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (n : ℕ) :
    let j := (pullback.map f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
        f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) (𝟙 X)
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))))
        (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
              Ideal.Quotient.factor_comp_mk]))
    IsFiniteOrderThickening j ∧ IsUniversalHomeomorphism j := by
  dsimp only
  let J := I ^ (n + 1 + 1)
  let J' := I ^ (n + 1)
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let q' := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))
  let p := pullback.fst f q
  let E := fun K : Ideal A ↦ Scheme.IdealSheafData.ofIdealTop
    (K.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
  obtain ⟨i, ⟨hi, huniq, hci, hker, _⟩⟩ :=
    quotientBaseChange_nestedIdeals f J J' (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
  let j := pullback.map f q' f q (𝟙 X)
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))))
    (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Ideal.Quotient.factor_comp_mk])
  have hji : j = i := huniq j (by simp [j, q, q']) (by simp [j, q, q'])
  change IsFiniteOrderThickening j ∧ IsUniversalHomeomorphism j
  rw [hji]
  have : IsClosedImmersion i := hci
  have hp := quotientBaseChange_closedImmersion_ideal f J
  have hzero : (E J).comap (p ≫ f) = ⊥ := by
    rw [Scheme.IdealSheafData.comap_comp, ← hp.2.1]
    exact bot_unique (by
      simpa only [Scheme.IdealSheafData.map_bot] using
        (Scheme.IdealSheafData.comap_map_le (I := ⊥) p))
  have hpow : i.ker ^ 2 = (E (J' ^ 2)).comap (p ≫ f) := by
    rw [hker]
    exact (quotientBaseChange_extendedIdeal_mul_pow (p ≫ f)).2 J' 2 (by decide)
  have hle : J' ^ 2 ≤ J := by
    dsimp [J', J]
    rw [← pow_mul]
    exact Ideal.pow_le_pow_right (by omega)
  have hE : E (J' ^ 2) ≤ E J := by
    intro U
    exact Ideal.map_mono (Ideal.map_mono hle)
  have hsquare : i.ker ^ 2 = ⊥ := by
    apply bot_unique
    rw [hpow, ← hzero]
    exact Scheme.IdealSheafData.comap_mono (p ≫ f) hE
  have hs : i.ker.support = ⊤ := by
    rw [← Scheme.IdealSheafData.support_pow_succ i.ker 1, hsquare]
    exact Scheme.IdealSheafData.support_bot
  have : Surjective i := ⟨by
    apply Set.range_eq_univ.mp
    rw [← i.isClosedEmbedding.isClosed_range.closure_eq, ← i.support_ker, hs]
    rfl⟩
  exact ⟨⟨1, hci, hsquare⟩, inferInstance⟩

end AlgebraicGeometry
