import Langlands.Sheaf.Renard.BasisPresheaf
import Langlands.CategoryTheory.RenardAbelian

/-!
# Abelianness statements for Renard's normalized basis presheaves

These are unproved targets for the presheaf example in Renard A.VI.1,
using the published category and the normalization convention of II.2.1.
-/

set_option autoImplicit false

universe u v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X]

/-- Renard A.VI.1: the actual normalized basis-presheaf category admits abelian data. -/
def PresheafAbelianStatement (B : OpenBasis X) : Prop :=
  Nonempty (CategoryTheory.Abelian (Presheaf.{u,v} B))

/-- The same source example expressed using Renard's existing seven-axiom interface. -/
def PresheafAbelianAxiomsStatement (B : OpenBasis X) : Prop :=
  Langlands.Renard.AbelianAxioms (Presheaf.{u,v} B)

end Langlands.Sheaf.Renard
