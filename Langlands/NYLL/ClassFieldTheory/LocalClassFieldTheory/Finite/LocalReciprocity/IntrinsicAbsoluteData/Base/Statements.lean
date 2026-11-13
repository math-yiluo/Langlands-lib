/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 13 November 2026:
Extract the statement of M091.007 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
IntrinsicAbsoluteData.lean at fbd320cd8b1b06487c58227e92eb135794267709 as a
closed Prop-valued definition without its proof and without its @[simp]
attribute. Add the Langlands.NYLL namespace prefix and the suffix Statement.
Qualify the published name FiniteAbstractField.base, and import the Library
module of intrinsicFiniteAbstractBase instead of the source imports. Omit all
other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Base.Definitions

/-!
# The finite intrinsic base is the distinguished finite base: statement

The closed proposition that, for every field `F`, the intrinsic abstract base
packaged as a finite abstract field equals the distinguished finite base of
`Gal(SeparableClosure F / F)`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The finite intrinsic base is the distinguished finite base of the
abstract class formation. -/
def intrinsicFiniteAbstractBase_eq_baseStatement : Prop :=
  ∀ (F : Type) [Field F],
    intrinsicFiniteAbstractBase F =
      Langlands.NYLL.ClassFormation.FiniteAbstractField.base
        (intrinsicAbsoluteGalois F)

end Langlands.NYLL.LocalClassFieldTheory
