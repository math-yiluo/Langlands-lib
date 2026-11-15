/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.Equiv.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions

/-!
# Finite local reciprocity: the residue datum

The arithmetic-Frobenius degree on an algebraic closure of a finite field is
packaged as the initial datum of the abstract class-formation framework.

Adapted from NYLL
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueDatum.lean`,
commit fbd320cd8b1b06487c58227e92eb135794267709, line 37 (M238.001), with the
section variables of lines 31–33. Worker 59 prefixed the namespaces by
`Langlands.NYLL`, dropped the unused `open RamificationTheory` (no import of this
file declares that namespace), moved the definition into the
`ResidueDatum/Initial/Definitions` file, replaced the NYLL imports by the Library
modules that publish the reused declarations, and kept the first sentence of the
module documentation. The
binders, universes, documentation string, `noncomputable` status and body are
unchanged. The theorems of the source module are stated in the sibling
`Statements` file. The original license and notices are retained in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.ClassFormation

noncomputable section

variable (k Omega : Type)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

/-- The abstract class-formation datum supplied by arithmetic Frobenius on the actual
residue algebraic closure. -/
noncomputable def residueDatumIn : DegreeData (Omega ≃ₐ[k] Omega) where
  degree := residueAbsoluteDegreeIn k Omega
  degree_surjective := (residueAbsoluteFrobeniusEquivIn k Omega).symm.surjective

end
end Langlands.NYLL.LocalClassFieldTheory
