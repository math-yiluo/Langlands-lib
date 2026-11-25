/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement

/-! # Compatibility of normalized root inclusions. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.ProEtale
private theorem compatible_inclusions_transition
    {C : Type*} [Category C] [Preadditive C]
    {M N R₁ R₂ P₁ P₂ : C} (q : M ≅ N)
    (r₁ : R₁ ≅ P₁) (r₂ : R₂ ≅ P₂) (i₁ : P₁ ⟶ M) (i₂ : P₂ ⟶ M)
    (j₁ : R₁ ⟶ N) (j₂ : R₂ ⟶ N) (t : R₂ ⟶ R₁) (k : ℕ)
    (h₁ : r₁.hom ≫ i₁ ≫ q.hom = j₁) (h₂ : r₂.hom ≫ i₂ ≫ q.hom = j₂)
    (ht : t ≫ j₁ = j₂ ≫ (k • 𝟙 N)) :
    t ≫ r₁.hom ≫ i₁ = r₂.hom ≫ i₂ ≫ (k • 𝟙 M) := by
  apply (cancel_mono q.hom).1
  have hc : q.hom ≫ (k • 𝟙 N) = (k • 𝟙 M) ≫ q.hom := by
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
      Category.comp_id, Category.id_comp]
  simp only [Category.assoc]
  rw [h₁, ht, ← h₂]
  simp only [Category.assoc]
  exact congrArg (fun f ↦ r₂.hom ≫ i₂ ≫ f) hc

/-- Normalized root inclusions carry the actual tower transition to multiplication. -/
theorem kummer_kernel_transition (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (M : DiagonalAb W) (P : ℕ → DiagonalAb W)
    (q : M ≅ Scheme.proEtaleUnitsSheaf W)
    (r : ∀ n, Scheme.proEtaleRootsOfUnitySheaf W (ℓ ^ (n + 1)) ≅ P n)
    (i : ∀ n, P n ⟶ M)
    (hin : ∀ n, (r n).hom ≫ i n ≫ q.hom =
      Scheme.proEtaleRootsOfUnityInclusion W (ℓ ^ (n + 1))) :
    ∀ n, (Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime)).map
      (homOfLE (Nat.le_succ n)).op ≫ (r n).hom ≫ i n =
      (r (n + 1)).hom ≫ i (n + 1) ≫ (ℓ • 𝟙 M) := by
  intro n
  let tR : Scheme.proEtaleRootsOfUnitySheaf W (ℓ ^ (n + 1 + 1)) ⟶
      Scheme.proEtaleRootsOfUnitySheaf W (ℓ ^ (n + 1)) :=
    (Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime)).map
      (homOfLE (Nat.le_succ n)).op
  have hpow : tR ≫ Scheme.proEtaleRootsOfUnityInclusion W (ℓ ^ (n + 1)) =
      Scheme.proEtaleRootsOfUnityInclusion W (ℓ ^ (n + 1 + 1)) ≫
        (ℓ • 𝟙 (Scheme.proEtaleUnitsSheaf W)) := by
    dsimp only [tR, Scheme.proEtaleRootsOfUnityTower]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    ext X x
    exact Scheme.proEtaleRootsOfUnityTransition_prime W ℓ (Fact.out : ℓ.Prime) n X x
  exact compatible_inclusions_transition q (r n) (r (n + 1)) (i n) (i (n + 1))
    _ _ tR ℓ (hin n) (hin (n + 1)) hpow

end AlgebraicGeometry.ProEtale
