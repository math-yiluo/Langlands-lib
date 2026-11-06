import Langlands.GroupScheme.LocalGroupIso

/-! # Universal overlap equations for local group isomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S} {U : Over S}

namespace Cocycle

/-- A natural cocycle is represented by its value at the universal pair of cover points. -/
def overlap (ξ : Cocycle A U) : U ⊗ U ⟶ A.X :=
  ξ.toFun (fst U U) (snd U U)

/-- Every value of the cocycle is pulled back from the actual overlap morphism. -/
theorem toFun_eq_lift_overlap (ξ : Cocycle A U) {T : Over S} (b c : T ⟶ U) :
    ξ.toFun b c = CartesianMonoidalCategory.lift b c ≫ ξ.overlap := by
  simpa only [lift_fst, lift_snd, overlap] using
    ξ.naturality (CartesianMonoidalCategory.lift b c) (fst U U) (snd U U)

end Cocycle

namespace LocalGroupIso

variable (e : LocalGroupIso G H U) (a : AutomorphicAction A G)

/-- A single equation on the universal overlap and the universal group point. -/
def HasOverlapDiscrepancy (δ : U ⊗ U ⟶ A.X) : Prop :=
  e.toFun (fst (U ⊗ U) G.X ≫ fst U U)
      (a.act (fst (U ⊗ U) G.X ≫ δ) (snd (U ⊗ U) G.X)) =
    e.toFun (fst (U ⊗ U) G.X ≫ snd U U) (snd (U ⊗ U) G.X)

/-- Pulling back the universal equation gives the discrepancy on every relative test. -/
theorem discrepancy_of_overlap {δ : U ⊗ U ⟶ A.X}
    (hδ : e.HasOverlapDiscrepancy a δ) {T : Over S} (b c : T ⟶ U)
    (g : T ⟶ G.X) :
    e.toFun b (a.act (lift b c ≫ δ) g) = e.toFun c g := by
  have h := congrArg (fun f => lift (lift b c) g ≫ f) hδ
  simpa only [HasOverlapDiscrepancy, ← e.naturality, a.naturality,
    ← Category.assoc, lift_fst, lift_snd] using h

/-- The single universal equation is equivalent to the full all-test equation. -/
theorem hasOverlapDiscrepancy_iff (δ : U ⊗ U ⟶ A.X) :
    e.HasOverlapDiscrepancy a δ ↔
      ∀ {T : Over S} (b c : T ⟶ U) (g : T ⟶ G.X),
        e.toFun b (a.act (lift b c ≫ δ) g) = e.toFun c g := by
  constructor
  · exact e.discrepancy_of_overlap a
  · intro h
    have h' := h (fst (U ⊗ U) G.X ≫ fst U U)
      (fst (U ⊗ U) G.X ≫ snd U U) (snd (U ⊗ U) G.X)
    simpa only [← comp_lift, lift_fst_snd, Category.comp_id, HasOverlapDiscrepancy]
      using h'

/-- The same overlap morphism represents the discrepancy after every refinement. -/
theorem discrepancy_on_refinements_of_overlap {δ : U ⊗ U ⟶ A.X}
    (hδ : e.HasOverlapDiscrepancy a δ) {T : Over S} (b c : T ⟶ U)
    {W : Over S} (t : W ⟶ T) (g : W ⟶ G.X) :
    e.toFun (t ≫ b) (a.act (t ≫ (lift b c ≫ δ)) g) =
      e.toFun (t ≫ c) g := by
  simpa only [← comp_lift, Category.assoc] using
    e.discrepancy_of_overlap a hδ (t ≫ b) (t ≫ c) g

/-- A natural cocycle has the discrepancy exactly when its overlap morphism does. -/
theorem hasDiscrepancy_iff_overlap (ξ : Cocycle A U) :
    e.HasDiscrepancy a ξ ↔ e.HasOverlapDiscrepancy a ξ.overlap := by
  rw [e.hasOverlapDiscrepancy_iff]
  constructor
  · intro h T b c g
    rw [← ξ.toFun_eq_lift_overlap]
    exact h b c g
  · intro h T b c g
    rw [ξ.toFun_eq_lift_overlap]
    exact h b c g

end LocalGroupIso

end Langlands.GroupScheme
