/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonConstantChartCounit
import WeilConjectures.AlgebraicGeometry.CoefficientFpLocalSystemEtaleCover

/-! # Etale origin of coefficient-sized finitely presented local systems

Source: Stacks Project, proetale.tex, lemma-compare-locally-constant (Tag 099Y).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.ProEtale

/-- Finitely presented local constant models descend to the etale site, with no
Noetherian hypothesis on the coefficient ring.

Source: Stacks Project, Tag 099Y, lemma-compare-locally-constant
(auxiliary; not a blueprint node).

Proof: evaluate the local-model hypothesis at the final pro-etale object and extract
its trivializing covering. Group the covering members by isomorphism type of their
constant module models. These groups have disjoint open images: pro-etale covers
are fpqc covers, and fpqc descent detects openness. Work over one such open, with
fixed model M. Finite presentation identifies the sheaf of automorphisms of the
constant M with the constant discrete group Aut_A(M). The sheaf of isomorphisms
from constant M to F is a torsor under this group. Comparison for discrete-group
torsors makes this torsor etale locally trivial. Descend the constant modules with
the resulting transition maps to an etale module sheaf. Their comparison inverse
images glue to F. The AsSmall equivalences preserve the covers, slice constant
sheaves and transition maps, so this is the displayed canonical fixed-scalar
inverse image. On an empty scheme the empty covering gives the unique zero sheaf;
zero module models have the same construction with the trivial automorphism group. -/
theorem coefficientFpLocalSystem_essImage (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
    (hF : ∀ V : Scheme.coefficientProEtaleSiteModel.{u, v} X,
      ∃ S : Sieve V, S ∈ Scheme.coefficientProEtaleModelTopology.{u, v} X V ∧
        ∀ (U : Scheme.coefficientProEtaleSiteModel.{u, v} X) (f : U ⟶ V), S f →
          ∃ M : ModuleCat.{max v (u + 1)} A, Module.FinitePresentation A M ∧
            Nonempty (F.over U ≅
              (constantSheaf ((Scheme.coefficientProEtaleModelTopology.{u, v} X).over U)
                (ModuleCat.{max v (u + 1)} A)).obj M)) :
    (Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).essImage F := by
  classical
  obtain ⟨I, V, hV, hmodels⟩ := coefficientFpLocalSystem_etaleCover X A F hF
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)
  have : IsIso (adj.counit.app F) := by
    apply Sheaf.isIso_of_coversTop hV
    intro i
    obtain ⟨M, _, ⟨e⟩⟩ := hmodels i
    exact coefficientComparison_counit_isIso_of_constant_over X A F (V i) M e
  exact ⟨((Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
    (ModuleCat.{max v (u + 1)} A) (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)).obj F,
      ⟨asIso (adj.counit.app F)⟩⟩

end AlgebraicGeometry.ProEtale
