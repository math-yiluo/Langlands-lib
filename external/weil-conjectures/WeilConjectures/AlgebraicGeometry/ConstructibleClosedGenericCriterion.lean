/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.OpenClosed

/-! # A closed-subscheme generic criterion for constructibility -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Generic finite local constancy on every closed subscheme implies constructibility.
Source: Stacks Project, Tag 09BH, Noetherian-induction step, and Tag 095E
(blueprint: lem-weil-pbc-constructible-closed-generic-criterion).

Proof: Induct on closed subsets of X, giving each its reduced induced subscheme.
The empty subset has the empty stratification. For a nonempty closed subset Z,
apply the hypothesis to obtain a dense open U on which the restriction of F is
finite locally constant. Its complement is a proper closed subset of Z and thus
of X. The induction hypothesis supplies a finite stratification of this complement.
Append U as one stratum. Composition of immersions gives schemes realizing the
strata in Z, and pullback composition identifies the restrictions. All strata are
locally closed and therefore constructible in a Noetherian space. Finally apply
this construction to X itself. Closed subschemes of X are Noetherian, so the
hypothesis applies at each stage. No assumption on any target sheaf is used. -/
theorem constructible_of_closed_generic
    {X : Scheme.{u}} [IsNoetherian X] {Λ : Type (u + 1)} [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : ∀ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i → IsNoetherian Z →
      ∃ U : Z.Opens, Dense (U : Set Z) ∧
        IsFiniteLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj F))) :
    IsConstructibleSheaf F := by
  classical
  have key : ∀ (C : TopologicalSpace.Closeds X) (Z : Scheme.{u})
      (i : Z ⟶ X) [IsClosedImmersion i], Set.range i ⊆ C →
      IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj F) := by
    intro C
    induction C using WellFoundedLT.induction with
    | ind C ih =>
      intro Z i hi hiC
      have hZ : IsNoetherian Z := by
        have := LocallyOfFiniteType.isLocallyNoetherian i
        have := QuasiCompact.compactSpace_of_compactSpace i
        exact {}
      cases isEmpty_or_nonempty Z
      · exact IsConstructibleSheaf.of_isZero (Etale.isZero_sheaf_of_isEmpty _)
      obtain ⟨U, hUd, hU⟩ := h Z i hi hZ
      obtain ⟨z, hz⟩ := hUd.nonempty
      let D : TopologicalSpace.Closeds Z := ⟨(U : Set Z)ᶜ, U.isOpen.isClosed_compl⟩
      let i' := (IdealSheafData.vanishingIdeal D).subschemeι
      have hrange : Set.range i' = (U : Set Z)ᶜ := by
        simp [i', D, IdealSheafData.range_subschemeι,
          IdealSheafData.coe_support_vanishingIdeal]
      let C' : TopologicalSpace.Closeds X :=
        ⟨i '' (U : Set Z)ᶜ, i.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl⟩
      have hlt : C' < C := by
        refine lt_of_le_of_ne (fun y ⟨t, _, ht⟩ ↦ hiC ⟨t, ht⟩) fun heq ↦ ?_
        have : i z ∈ (C' : Set X) := heq ▸ hiC ⟨z, rfl⟩
        obtain ⟨t, ht, hti⟩ := this
        exact ht (i.isClosedEmbedding.injective hti ▸ hz)
      have hC' := ih C' hlt _ (i' ≫ i) (by
        rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]
        exact subset_rfl)
      have hclosed : IsConstructibleSheaf
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) i').obj
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj F)) :=
        IsConstructibleSheaf.of_iso
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) i' i).app F)
      have hopen : IsConstructibleSheaf
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj F)) :=
        ⟨Stratification.trivial U.toScheme, fun _ ↦
          IsFiniteLocallyConstantSheaf.upperStar (𝟙 U.toScheme) _⟩
      exact (isConstructibleSheaf_iff_upperStar U.ι i'
        (by rw [Scheme.Opens.range_ι]; exact hrange) _).mpr ⟨hopen, hclosed⟩
  have := key ⊤ X (𝟙 X) (by simp)
  exact IsConstructibleSheaf.of_iso ((Etale.upperStarId (ModuleCat.{u + 1} Λ) X).app F)


end AlgebraicGeometry.Scheme
