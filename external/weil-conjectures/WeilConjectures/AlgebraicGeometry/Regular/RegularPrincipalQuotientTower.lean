/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.AdicTower

/-! # Regular principal quotient towers

## References

* Stacks Project, Tag 099M, using the free two-term resolution of the principal coefficients
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.ProEtale

private theorem quotient_tower_from_cones
    {B : Type v} [Category.{w} B] [Abelian B] [HasDerivedCategory.{u + 1} B]
    {Λ : Type*} [CommRing Λ] [Linear Λ B] (r : Λ)
    (R : CochainComplex B ℤ) (Y : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (p : ∀ n : ℕ, R ⟶ Y.obj (op n))
    (hz : ∀ n : ℕ, (r ^ (n + 1) • 𝟙 R) ≫ p n = 0)
    (hT : ∀ n : ℕ, (ShortComplex.mk _ _ (hz n)).ShortExact)
    (hp : ∀ n : ℕ, p (n + 1) ≫ Y.map (homOfLE (Nat.le_succ n)).op = p n)
    (K : DerivedCategory B) (G : ℕᵒᵖ ⥤ DerivedCategory B)
    (g : K ⟶ DerivedCategory.Q.obj R)
    (d : ∀ n : ℕ, G.obj (op (n + 1)) ≅
      DerivedCategory.Q.obj (CochainComplex.mappingCone (r ^ (n + 1) • 𝟙 R)))
    (hd : ∀ n : ℕ, G.map (homOfLE (Nat.add_le_add_right (Nat.le_succ n) 1)).op ≫
      (d n).hom = (d (n + 1)).hom ≫ DerivedCategory.Q.map
        (CochainComplex.mappingCone.map (r ^ (n + 1 + 1) • 𝟙 R)
          (r ^ (n + 1) • 𝟙 R) (r • 𝟙 R) (𝟙 R)
          (by
            rw [Category.comp_id, Linear.smul_comp, Linear.comp_smul,
              Category.id_comp, smul_smul]
            exact congrArg (fun t : Λ ↦ t • 𝟙 R) (pow_succ' r (n + 1)))))
    (a : ∀ n : ℕ, K ⟶ G.obj (op (n + 1)))
    (ha : ∀ n : ℕ, a n ≫ (d n).hom =
      g ≫ DerivedCategory.Q.map (CochainComplex.mappingCone.inr (r ^ (n + 1) • 𝟙 R))) :
    ∃ β : addOpFunctor 1 ⋙ G ≅ Y ⋙ DerivedCategory.Q,
      ∀ n : ℕ, a n ≫ β.hom.app (op n) = g ≫ DerivedCategory.Q.map (p n) := by
  let T (n : ℕ) := ShortComplex.mk _ _ (hz n)
  let q (n : ℕ) := CochainComplex.mappingCone.descShortComplex (T n)
  have hq (n : ℕ) : QuasiIso (q n) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex (hT n)
  let b (n : ℕ) := (d n).hom ≫ DerivedCategory.Q.map (q n)
  have hb (n : ℕ) : IsIso (b n) := by
    have := hq n
    dsimp only [b]
    infer_instance
  have hn (n : ℕ) : G.map (homOfLE (Nat.add_le_add_right (Nat.le_succ n) 1)).op ≫
      b n = b (n + 1) ≫ (Y ⋙ DerivedCategory.Q).map (homOfLE (Nat.le_succ n)).op := by
    let f : T (n + 1) ⟶ T n :=
      { τ₁ := r • 𝟙 R
        τ₂ := 𝟙 R
        τ₃ := Y.map (homOfLE (Nat.le_succ n)).op
        comm₁₂ := by
          change (r • 𝟙 R) ≫ (r ^ (n + 1) • 𝟙 R) =
            (r ^ (n + 1 + 1) • 𝟙 R) ≫ 𝟙 R
          rw [Category.comp_id, Linear.smul_comp, Linear.comp_smul,
            Category.id_comp, smul_smul]
          exact congrArg (fun t : Λ ↦ t • 𝟙 R) (pow_succ' r (n + 1)).symm
        comm₂₃ := by
          change (𝟙 R) ≫ p n = p (n + 1) ≫ Y.map (homOfLE (Nat.le_succ n)).op
          rw [Category.id_comp, hp] }
    have hnat := CochainComplex.mappingCone.map_descShortComplex (T (n + 1)) (T n) f
    dsimp only [b]
    rw [← Category.assoc, hd, Category.assoc, ← DerivedCategory.Q.map_comp]
    rw [hnat, DerivedCategory.Q.map_comp]
    exact (Category.assoc _ _ _).symm
  let β : addOpFunctor 1 ⋙ G ⟶ Y ⋙ DerivedCategory.Q := NatTrans.ofOpSequence b hn
  have (n : ℕᵒᵖ) : IsIso (β.app n) := hb n.unop
  have : IsIso β := NatIso.isIso_of_isIso_app β
  refine ⟨asIso β, ?_⟩
  intro n
  change a n ≫ ((d n).hom ≫ DerivedCategory.Q.map (q n)) = _
  have hinc : CochainComplex.mappingCone.inr (r ^ (n + 1) • 𝟙 R) ≫ q n = p n :=
    CochainComplex.mappingCone.inr_descShortComplex (T n)
  rw [← Category.assoc, ha, Category.assoc, ← DerivedCategory.Q.map_comp, hinc]

/-- Degreewise regular scalar quotients identify with the positive derived quotient tower. -/
theorem regular_principal_quotient_tower
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {Λ : Type (u + 1)} [CommRing Λ]
    (r : Λ) (hr : r ∈ nonZeroDivisors Λ)
    (R : CochainComplex (Sheaf J (ModuleCat.{u + 1} Λ)) ℤ)
    (Y : ℕᵒᵖ ⥤ CochainComplex (Sheaf J (ModuleCat.{u + 1} Λ)) ℤ)
    (p : ∀ n : ℕ, R ⟶ Y.obj (op n))
    (hz : ∀ n : ℕ, (r ^ (n + 1) • 𝟙 R) ≫ p n = 0)
    (hT : ∀ n : ℕ, (ShortComplex.mk _ _ (hz n)).ShortExact)
    (hp : ∀ n : ℕ, p (n + 1) ≫ Y.map (homOfLE (Nat.le_succ n)).op = p n)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ)))
    (g : K ≅ DerivedCategory.Q.obj R) :
    let I := Ideal.span {r}
    let G := DerivedCategory.derivedCompletionDiagram J I K
    ∃ β : addOpFunctor 1 ⋙ G ≅ Y ⋙ DerivedCategory.Q,
      ∀ n : ℕ, (DerivedCategory.derivedCompletionCone J I K).π.app (op (n + 1)) ≫
        β.hom.app (op n) = g.hom ≫ DerivedCategory.Q.map (p n) := by
  let I := Ideal.span {r}
  let G := DerivedCategory.derivedCompletionDiagram J I K
  let d (n : ℕ) : G.obj (op (n + 1)) ≅
      DerivedCategory.Q.obj (CochainComplex.mappingCone (r ^ (n + 1) • 𝟙 R)) :=
    (DerivedCategory.reductionFunctor J I (n + 1)).mapIso g ≪≫
      DerivedCategory.reductionConeIso hr rfl (n + 1) R
  have hd (n : ℕ) : G.map (homOfLE (Nat.add_le_add_right (Nat.le_succ n) 1)).op ≫
      (d n).hom = (d (n + 1)).hom ≫ DerivedCategory.Q.map
        (CochainComplex.mappingCone.map (r ^ (n + 1 + 1) • 𝟙 R)
          (r ^ (n + 1) • 𝟙 R) (r • 𝟙 R) (𝟙 R)
          (by
            rw [Category.comp_id, Linear.smul_comp, Linear.comp_smul,
              Category.id_comp, smul_smul]
            exact congrArg (fun t : Λ ↦ t • 𝟙 R) (pow_succ' r (n + 1)))) := by
    have hc := DerivedCategory.derivedCompletionDiagram_map_comp_reductionFunctor_map
      hr (show I = Ideal.span {r} from rfl) g.hom
      (Nat.add_le_add_right (Nat.le_succ n) 1)
    have he : (n + 1 + 1) - (n + 1) = 1 := by omega
    simpa only [d, Iso.trans_hom, Functor.mapIso_hom, Category.assoc, he, pow_one] using hc
  let a (n : ℕ) := (DerivedCategory.derivedCompletionCone J I K).π.app (op (n + 1))
  have ha (n : ℕ) : a n ≫ (d n).hom =
      g.hom ≫ DerivedCategory.Q.map
        (CochainComplex.mappingCone.inr (r ^ (n + 1) • 𝟙 R)) :=
    DerivedCategory.derivedCompletionCone_π_app_comp_reductionFunctor_map hr rfl g.hom (n + 1)
  exact quotient_tower_from_cones r R Y p hz hT hp K G g.hom d hd a ha

end AlgebraicGeometry.ProEtale
