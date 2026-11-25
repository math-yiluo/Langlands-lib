/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.CategoryTheory.ExactCouple
@[expose] public section
universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple
/-- (blueprint: lem-sp-derived-couple-map-uniqueness)
The three induced maps are uniquely determined by their descent equations.
This is the universal-property portion of Stacks Tag 011R.

Choose the existing derived maps. For alpha, cancel the monic image inclusion
in its descent equation. For f, cancel the epimorphic cokernel projection and
then the monic image inclusion. For g, cancel the epimorphic factorization
through the image of alpha. In each case the defining equation of the chosen
map supplies the same composite. -/
theorem derived_couple_map_uniqueness {C : Type u} [Category.{v} C] [Abelian C]
    {s : ℕ} (X : BigradedExactCouple C s) :
    ∃ M : DerivedMaps X,
      (∀ (p q : ℤ) (a : X.derivedD p q ⟶ X.derivedD (p - 1) (q + 1)),
        a ≫ X.derivedDInclusion (p - 1) (q + 1) = X.derivedDInclusion p q ≫ X.alpha p q →
          a = M.alpha p q) ∧
      (∀ (p q : ℤ) (b : X.derivedE p q ⟶ X.derivedD (p + 2) (q - 1)),
        X.derivedEProjection p q ≫ b ≫ X.derivedDInclusion (p + 2) (q - 1) =
            kernel.ι (X.d p q) ≫ X.f p q → b = M.f p q) ∧
      (∀ (p q : ℤ) (c : X.derivedD p q ⟶ X.derivedE (p + (s + 1)) (q - (s + 1))),
        factorThruImage (X.alpha (p + 1) (q - 1)) ≫ c =
            X.gToCycles (p + 1) (q - 1) ≫ X.derivedEProjection ((p + 1) + s) ((q - 1) - s) ≫
              eqToHom (by congr 1 <;> omega) → c = M.g p q) := by
  obtain ⟨M⟩ := X.derivedMaps_exists
  refine ⟨M, ?_, ?_, ?_⟩
  · intro p q a ha
    have : Mono (X.derivedDInclusion (p - 1) (q + 1)) := by
      dsimp [derivedDInclusion]
      infer_instance
    apply (cancel_mono (X.derivedDInclusion (p - 1) (q + 1))).mp
    exact ha.trans (M.alpha_comm p q).symm
  · intro p q b hb
    have : Mono (X.derivedDInclusion (p + 2) (q - 1)) := by
      dsimp [derivedDInclusion]
      infer_instance
    have : Epi (X.derivedEProjection p q) := by
      dsimp [derivedEProjection]
      infer_instance
    apply (cancel_epi (X.derivedEProjection p q)).mp
    apply (cancel_mono (X.derivedDInclusion (p + 2) (q - 1))).mp
    simpa only [Category.assoc] using hb.trans (M.f_comm p q).symm
  · intro p q c hc
    apply (cancel_epi (factorThruImage (X.alpha (p + 1) (q - 1)))).mp
    exact hc.trans (M.g_comm p q).symm
end CategoryTheory.BigradedExactCouple
