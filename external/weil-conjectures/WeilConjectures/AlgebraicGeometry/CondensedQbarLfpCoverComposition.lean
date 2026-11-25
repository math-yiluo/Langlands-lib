/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

@[expose] public section
universe u
open CategoryTheory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
/-!
# Composition of local finite-free refinements

The theorem packages the categorical composition of the original presentation cover
with a chosen refinement over each member.
-/
-- Keep the member property abstract when checking the dependent cover construction.
private theorem exists_cover_of_local_property
    {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (Q : ∀ Y : Scheme.{u}, (Y ⟶ X) → Prop)
    (hQ : ∀ i : 𝒰.I₀,
      ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (𝒰.X i),
        ∀ j : C.I₀, Q (C.X j) (C.f j ≫ 𝒰.f i)) :
    ∃ 𝒲 : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
      ∀ i : 𝒲.I₀, Q (𝒲.X i) (𝒲.f i) := by
  classical
  obtain ⟨C, hC⟩ := Classical.skolem.mp hQ
  exact ⟨𝒰.bind C, fun i ↦ hC i.1 i.2⟩

/-- Compose local finite-free refinements into one pro-etale cover.

Source: Stacks Project, Sites, covering composition; RefactorInstruction.tex, Section 4
(auxiliary; not a blueprint node).
The covering presieve is the indexed composition of the original presieve with each
local presieve; the finite-free isomorphisms are carried along the composite maps. -/
theorem exists_condensedQbar_refinement_of_local
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hC : ∀ (i : 𝒰.I₀), ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (𝒰.X i),
      ∀ (j : C.I₀), ∃ r : ℕ, Nonempty
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
          (C.f j ≫ 𝒰.f i)).obj P ≅
          Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (C.X j)) r)) :
    ∃ 𝒲 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒲.I₀,
      ∃ r : ℕ, Nonempty
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (𝒲.f i)).obj P ≅
          Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (𝒲.X i)) r) := by
  exact exists_cover_of_local_property 𝒰
    (fun Y f ↦ ∃ r : ℕ, Nonempty
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) f).obj P ≅
        Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) r)) hC
end AlgebraicGeometry.ProEtale
