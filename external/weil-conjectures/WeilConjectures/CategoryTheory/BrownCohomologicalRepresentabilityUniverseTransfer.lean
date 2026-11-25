/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Triangulated.Yoneda
import WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransferAux

/-!
# Changing universes in the Brown representability criterion

Source: Stacks Project, Tag 0A8F, Lemma `lemma-brown`, with its set-indexing
convention made explicit (blueprint: lem-pc-brown-representability-universe-transfer).
-/

@[expose] public section

universe w v vH u

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

/-- (blueprint: lem-pc-brown-representability-universe-transfer) -/
theorem brownCohomologicalRepresentabilityUniverseTransfer
    (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [IsTriangulated C] [HasCoproducts.{max w v vH} C]
    (hC : IsCompactlyGeneratedTriangulated.{max w v vH} C)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{vH}) [H.IsHomological]
    (hH : ∀ I : Type (max w v vH), PreservesLimitsOfShape (Discrete I) H) :
    (H ⋙ forget AddCommGrpCat).IsRepresentable := by
  obtain ⟨G, hG⟩ := brownCohomologicalRepresentabilityUniverseTransfer_aux
    C hC H hH
  exact ⟨⟨G, hG⟩⟩

end CategoryTheory
