/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps

/-! # Base tensor models for semilinear systems

## References

* Zheng, Construction 4.1
* Stacks Project, Tags 06YS, 06YN, 07A4, 08JD and 0A97
-/
@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
/-- The normalized model uses the same explicit sheafification and derived universes as Closed. -/
abbrev NormalizedTensorModel (R : Sheaf J CommRingCat.{max c v r}) :=
  @RingedSiteDualityModel.{c, v, r, (max c v r) + 1} C _ J
    (abelianSheafify.{c, v, max c v r} J) (locallyBijective.{c, v, max c v r} J) R
      (hasDerived.{c, v, max c v r} J R)

/-- The closed structures and K-flat tensor models used by all comparisons. -/
structure SystemTensorBase where
  closed : Closed.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ)
  tensorModels : Models.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ) closed
  /-- The system constraints are those of an actual normalized ringed-site model. -/
  tensorNormalization : Nonempty { M : NormalizedTensorModel.{c, v, r}
    (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) //
      M.closed = closed }
  levelClosed : ∀ n : ℕ, Closed.{c, v, r} J (B n)
  levelTensorModels : ∀ n : ℕ, Models.{c, v, r} J (B n) (levelClosed n)
/-- Closed structures and K-flat tensor models for semilinear systems exist. -/
theorem systemTensorBase_nonempty :
    Nonempty (SystemTensorBase.{c, v, r} J B τ) := by
  classical
  let : HasSheafify J AddCommGrpCat.{max c v r} := abelianSheafify J
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} := locallyBijective J
  let : HasSheafify (coefficientSequenceTopology J) AddCommGrpCat.{max c v r} :=
    abelianSheafify (coefficientSequenceTopology J)
  let : (coefficientSequenceTopology J).WEqualsLocallyBijective
      AddCommGrpCat.{max c v r} := locallyBijective (coefficientSequenceTopology J)
  let := hasDerived (coefficientSequenceTopology J) (systemRing J B τ)
  obtain ⟨M⟩ := ringedSiteDualityMaps_exists.{c, v, r, (max c v r) + 1}
    (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ)
  have levels (n : ℕ) : ∃ S : Closed.{c, v, r} J (B n),
      Nonempty (Models.{c, v, r} J (B n) S) := by
    let := hasDerived J (B n)
    obtain ⟨N⟩ := ringedSiteDualityMaps_exists.{c, v, r, (max c v r) + 1} J (B n)
    exact ⟨N.closed, ⟨N.models⟩⟩
  choose levelClosed levelModels using levels
  exact ⟨⟨M.closed, M.models, ⟨⟨M, rfl⟩⟩, levelClosed,
    fun n ↦ Classical.choice (levelModels n)⟩⟩
end WeilConjectures.SemilinearSections
