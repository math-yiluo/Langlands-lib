/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only the asserted type of the private theorem M086.018
normResidueNaturality_symm_naturality from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Main.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Name it by its source row as
Langlands.NYLL.PortInternal.M086.d018Statement and package all binders of
the theorem, in order and with the same binder kinds and the four universes
of its `Type*` binders, inside a closed Prop-valued definition. The named
hypothesis h, which the conclusion does not mention, becomes an anonymous
premise. Replace the source imports by the Mathlib module defining additive
equivalences and defer the truth proof. Omit all other declarations of the
module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.Algebra.Group.Equiv.Defs

/-!
# Inverting the horizontal isomorphisms of a commutative square: statement
-/

namespace Langlands.NYLL.PortInternal.M086

universe u₁ u₂ u₃ u₄

/-- Statement target for the private theorem
`normResidueNaturality_symm_naturality`, source unit M086.018: a commutative
square of additive homomorphisms whose horizontal arrows are additive
isomorphisms remains commutative after replacing both horizontal
isomorphisms by their inverses. -/
def d018Statement : Prop :=
  ∀ {Q : Type u₁} {B : Type u₂} {Q' : Type u₃} {B' : Type u₄}
    [AddCommGroup Q] [AddCommGroup B]
    [AddCommGroup Q'] [AddCommGroup B']
    (r : Q ≃+ B) (r' : Q' ≃+ B')
    (q : Q →+ Q') (b : B →+ B'),
    b.comp r.toAddMonoidHom = r'.toAddMonoidHom.comp q →
      q.comp r.symm.toAddMonoidHom =
        r'.symm.toAddMonoidHom.comp b

end Langlands.NYLL.PortInternal.M086
