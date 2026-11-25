/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.WeilIndSheafCategory
public import WeilConjectures.SmoothPurity.Sf.SfCommonStageWeilCohomology
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
import all WeilConjectures.DeligneLaumon.WeilIndSheafCategory
import all WeilConjectures.DeligneLaumon.CommonStageOpenHeartAdjunction

/-! # Realization of open extension on represented Weil ind-sheaves

Source: SGA 4, XVII, §5.1; Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7.
(blueprint: lem-zl-ind-open-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open CategoryTheory.Endofunctor
attribute [local irreducible] Scheme.residueField
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

section CommonStageModel
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)
open CommonOpenHeartProof CategoryTheory.Functor
attribute [local instance] stageCategory
attribute [local implicit_reducible] catToReflQuiver StageHom
set_option allowUnsafeReducibility true in
attribute [local reducible] Stage stageCategory
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] stageCategory._aux_1 stageCategory._aux_3 stageCategory._aux_5
set_option allowUnsafeReducibility true in
attribute [local irreducible] stageSystem commonStageDerivedPullback
  sfCompactSupportFiniteFunctor rationalDerivedPullback

end CommonStageModel

end WeilConjectures
