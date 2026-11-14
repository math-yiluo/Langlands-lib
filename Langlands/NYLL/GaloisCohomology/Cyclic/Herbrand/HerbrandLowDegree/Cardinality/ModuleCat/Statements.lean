/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 194 (2026-11-14): extract the listed M117 units
from Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Cardinality.lean
at fbd320cd8b1b06487c58227e92eb135794267709; adapt namespace/imports and theorem statements
as documented in the paired Markdown. Source construction bodies are retained.
Original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.SetTheory.Cardinal.Finite

namespace Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

open CategoryTheory

set_option linter.unusedVariables false

/-- Source M117.014: exact proposition target. -/
def moduleCatRangeCard_eq_of_conjugateStatement
    {X Y X' Y' : ModuleCat.{0} ℤ}
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (eX : X ≅ X') (eY : Y ≅ Y')
    (h : eX.inv ≫ f ≫ eY.hom = g) : Prop :=
    Nat.card (MonoidHom.range
        f.hom.toAddMonoidHom.toMultiplicative) =
      Nat.card (MonoidHom.range
        g.hom.toAddMonoidHom.toMultiplicative)

/-- Source M117.015: exact proposition target. -/
def mulExact_of_moduleCat_exactStatement
    {X Y Z : ModuleCat.{0} ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hexact : Function.Exact f g) : Prop :=
    Function.MulExact
      f.hom.toAddMonoidHom.toMultiplicative
      g.hom.toAddMonoidHom.toMultiplicative

/-- Source M117.017: exact proposition target. -/
def moduleCat_card_eq_card_range_mul_card_range_of_exactStatement
    {X Y Z : ModuleCat.{0} ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hexact : Function.Exact f g) [Finite Y] : Prop :=
    Nat.card Y =
      Nat.card (MonoidHom.range
        f.hom.toAddMonoidHom.toMultiplicative) *
      Nat.card (MonoidHom.range
        g.hom.toAddMonoidHom.toMultiplicative)

end Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand
