/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModels
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.AlgebraicGeometry.ProEtaleOriginFromFiniteModels
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Lisse pro-etale module sheaves have etale origin

Source: Stacks Project, Pro-etale Cohomology, Tag 099Y, lemma-compare-locally-constant;
Bhatt--Scholze, Corollary 5.1.5 (auxiliary; not a blueprint node).

Both clauses use the fixed-coefficient comparison adjunction. Local constancy uses
module-sheaf isomorphisms, and finiteness is tested at all bounded geometric points.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A fixed-coefficient pro-etale module sheaf is lisse when it is locally constant
and all geometric stalks are finite as sets. No freeness or constant rank is required.
Source: Stacks Project, Tag 099Y, specialized to a finite commutative coefficient ring
(auxiliary; not a blueprint node). -/
noncomputable def IsLisseProEtaleFixedModuleSheaf (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) : Prop :=
  IsLocallyConstantProEtaleFixedModuleSheaf X Λ F ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      Finite (proEtaleGeometricFixedModuleStalk x Λ F)

/-- Inverse image preserves lisse module sheaves, and every lisse pro-etale module sheaf
is isomorphic to the inverse image of a lisse etale module sheaf.
Source: Stacks Project, Tag 099Y, lemma-compare-locally-constant; Bhatt--Scholze,
Corollary 5.1.5 (auxiliary; not a blueprint node).

Proof:
1. Choose finite etale constant models using finite_locally_constant_module_values_iff.
The helper comparison_finite_models_of_etale_finite_values transports them through
comparison, which commutes with restriction and sends constants to constants.
2. The existing finiteModels_over helper gives fixed-coefficient local constancy.
The existing finite_geometricStalk_of_finite_models gives finite geometric stalks.
This proves the forward implication.
3. Conversely, finite_models_of_fixed_lisse discards empty covering members and
identifies each remaining model with a finite geometric stalk. Removing empty members
preserves quasi-compactness by retaining a finite affine refinement over compact opens.
4. The helper proEtale_model_type_opens descends model-type loci by fpqc open descent:
models on a nonempty double overlap have the same geometric fiber and are isomorphic.
On each type open the original covering therefore has one fixed finite model.
5. The remaining theorem etale_cover_of_proetale_uniform_model uses the Isom sheaf
from that model to F. Finite presentation identifies it locally with constant Aut(M).
Locally-classical comparison descends its sections to an etale trivializing cover.
The helper etale_cover_of_proetale_finite_models combines the type opens and these
covers; choosing one type open through each point makes the resulting index small.
6. The helper etale_origin_of_finite_models constructs G = comparisonLowerStar F.
Over the etale cover, the comparison unit and the constant-sheaf comparison identify
G with the finite constant models, so the finite-values characterization makes G lisse.
7. The local counits are invertible because the models are in the comparison image.
The mate calculation comparison_counit_restriction_isIso identifies their invertibility
with that of the restricted global counit. Conservativity on the covering proves the
global counit invertible, giving the required isomorphism. Empty schemes, empty covers,
zero modules and zero coefficient rings are included throughout. -/
theorem proEtale_lisse_origin (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] :
    (∀ G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsFiniteLocallyConstantSheaf G →
        IsLisseProEtaleFixedModuleSheaf X Λ
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj G)) ∧
    (∀ F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ),
      IsLisseProEtaleFixedModuleSheaf X Λ F →
        ∃ G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
          IsFiniteLocallyConstantSheaf G ∧
            Nonempty ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj G ≅ F)) := by
  constructor
  · intro G hG
    let : IsFiniteLocallyConstantSheaf G := hG
    obtain ⟨d, hd⟩ := (finite_locally_constant_module_values_iff G).1.mpr hG
    obtain ⟨I, W, g, hg, hmodels⟩ :=
      comparison_finite_models_of_etale_finite_values X Λ G ⟨d, hd⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨I, U, f, hf, h⟩ :=
        AlgebraicGeometry.ProEtale.finiteModels_over Λ _
          ⟨I, W, g, hg, hmodels⟩
      exact ⟨I, U, f, hf, fun i ↦ by
        obtain ⟨M, _, he⟩ := h i
        exact ⟨M, he⟩⟩
    · intro Ω hΩ hΩalg x
      exact AlgebraicGeometry.ProEtale.finite_geometricStalk_of_finite_models
        Λ _ ⟨I, W, g, hg, hmodels⟩ Ω x
  · intro F hF
    obtain ⟨I, W, g, hg, hmodels⟩ := finite_models_of_fixed_lisse X Λ F hF
    exact etale_origin_of_finite_models X Λ F ⟨I, W, g, hg, hmodels⟩

end AlgebraicGeometry.Scheme
