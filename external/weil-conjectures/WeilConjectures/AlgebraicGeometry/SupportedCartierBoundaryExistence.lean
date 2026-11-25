/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerSystem
import WeilConjectures.AlgebraicGeometry.CartierReductionData

/-! # SupportedCartierBoundaryExistence -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The normalized relative boundary exists and determines its Ext representative.
proof.md, paragraphs 1--4;
Stacks 03PL and 0A45 (auxiliary; not a blueprint node).

Proof: Use existence and uniqueness of the integral pole boundary and of the etale
Cartier reduction from CartierReductionSiteComparison. A boundary witness is also a
pole-boundary witness: all complements agree as open subsets. Uniqueness identifies
its extension class with the canonical pole boundary. Reassociation of Yoneda products
then makes its final equation exactly CartierEtaleReductionSpec. Conversely the pole
boundary supplies the torsor witnesses for every complement, and the reduction equation
supplies their final Ext equation. Transport existence and uniqueness through this
pointwise equivalence. No arbitrary representative is chosen: the pole and reduced
classes are both uniquely characterized by their specifications. -/
theorem supported_cartier_boundary_existsUnique (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) {D : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    ∃! κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2, SupportedKummerBoundary A N hA i hI hT κ := by
  classical
  obtain ⟨β, hβ, hβuniq⟩ := cartierPoleBoundary_existsUnique i hI
  have hpole : cartierPoleBoundary i hI = β :=
    hβuniq _ (Classical.choose_spec (cartierPoleBoundary_existsUnique i hI)).1
  let spec := AlgebraicGeometry.ProEtale.CartierEtaleReductionSpec A N hA i hI hT
  have hequiv (κ : Ext
      ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2) :
      SupportedKummerBoundary A N hA i hI hT κ ↔ spec κ := by
    constructor
    · intro hκ
      let := hI.isInvertible_dual_toModules
      let := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
        (Scheme.Modules.dual i.ker.toModules)
      let W : T.Opens :=
        ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
      unfold SupportedKummerBoundary at hκ
      obtain ⟨τ, E, a, b, hab, hE, f, hτ, hf, hb, hzero, hext⟩ := hκ W rfl
      have hEspec : CartierPoleBoundarySpec i hI hE.extClass := by
        intro W' hW'
        have hw : W' = W := by
          apply TopologicalSpace.Opens.ext
          exact hW'
        subst W'
        exact ⟨τ, E, a, b, hab, hE, f, hτ, hf, hb, hzero, rfl⟩
      have hEβ : hE.extClass = β := hβuniq _ hEspec
      dsimp only [spec, AlgebraicGeometry.ProEtale.CartierEtaleReductionSpec,
        AlgebraicGeometry.ProEtale.cartierScalarBoundaryEquation]
      rw [hpole, ← hEβ]
      unfold AlgebraicGeometry.ProEtale.cartierEtaleKummerUnit
        AlgebraicGeometry.ProEtale.cartierKummerClass
      simpa only [Ext.comp_assoc] using hext
    · intro hκ
      let := hI.isInvertible_dual_toModules
      let := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
        (Scheme.Modules.dual i.ker.toModules)
      unfold SupportedKummerBoundary
      intro W hW
      obtain ⟨τ, E, a, b, hab, hE, f, hτ, hf, hb, hzero, he⟩ := hβ W hW
      refine ⟨τ, E, a, b, hab, hE, f, hτ, hf, hb, hzero, ?_⟩
      dsimp only [spec, AlgebraicGeometry.ProEtale.CartierEtaleReductionSpec,
        AlgebraicGeometry.ProEtale.cartierScalarBoundaryEquation] at hκ
      rw [hpole, he] at hκ
      unfold AlgebraicGeometry.ProEtale.cartierEtaleKummerUnit
        AlgebraicGeometry.ProEtale.cartierKummerClass at hκ
      simpa only [Ext.comp_assoc] using hκ
  obtain ⟨κ, hκ, hu⟩ :=
    (AlgebraicGeometry.ProEtale.cartierReduction_existsUnique A N hN hA i hI hT).1
  exact ⟨κ, (hequiv κ).2 hκ, fun κ' hκ' ↦ hu κ' ((hequiv κ').1 hκ')⟩

end AlgebraicGeometry.Etale
