/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedSiteComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
/-!
# Full faithfulness in the ordinary finite-coefficient presentation

Source: blueprint finite comparison localizing proof, unbounded comparison step
(blueprint: lem-ctf-finite-comparison-ordinary-fully-faithful).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
/-- Cancel the exact coefficient-realization equivalence from unbounded comparison.
Source: blueprint finite comparison localizing proof, unbounded comparison step
(blueprint: lem-ctf-finite-comparison-ordinary-fully-faithful).

Proof: factor the recorded ringed-coefficient derived comparison as ordinary comparison
followed by derived realization, using the exact-functor composition isomorphism.
Realization is an equivalence, and its derived functor is therefore faithful.
Fullness and faithfulness of the composite imply both for ordinary comparison.
The argument includes the zero ring and empty scheme. -/
theorem finiteComparisonOrdinary_fullyFaithful
    (A : Type (u + 1)) [CommRing A] [TopologicalSpace A]
    [DiscreteTopology A] [Finite A]
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] :
    Nonempty ((comparisonUpperStar
      (ModuleCat.{u + 1} A) X).mapDerivedCategory).FullyFaithful := by
  obtain ⟨_, ⟨h⟩, _⟩ :=
    finiteCoefficientDerivedComparison_fullyFaithful.{u, u + 2} k hbase hℓ A hA X
  let F : Etale.DerivedCategoryModule A X ⥤
      DerivedCategory.{u + 1} (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let G : DerivedCategory.{u + 1} (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      FiniteCoefficientDerivedCategory.{u} X A :=
    (finiteCoefficientRealization.{u} X A).mapDerivedCategory.{u + 1, u + 2}
  have : (finiteCoefficientDerivedComparison.{u} X A).Full := h.full
  have : (finiteCoefficientDerivedComparison.{u} X A).Faithful := h.faithful
  let e : F ⋙ G ≅ finiteCoefficientDerivedComparison.{u} X A :=
    Functor.mapDerivedCategoryCompIso
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)
      (finiteCoefficientRealization.{u} X A)
  have : F.Full := Functor.Full.of_comp_faithful_iso e
  have : F.Faithful := Functor.Faithful.of_comp_iso e
  exact ⟨Functor.FullyFaithful.ofFullyFaithful F⟩

end AlgebraicGeometry.ProEtale
