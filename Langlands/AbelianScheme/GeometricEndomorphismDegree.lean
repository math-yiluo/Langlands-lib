import Langlands.AbelianScheme.Basic
import Langlands.AbelianScheme.Isogeny
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # The geometric degree of an integral abelian endomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

/-- The native finite-flat rank of an isogeny at the identity, and zero for
other endomorphisms. -/
def geometricEndomorphismDegree {k : Type u} [Field k]
    (A : AbelianScheme (Spec (CommRingCat.of k))) (f : End A) : ℕ := by
  classical
  exact if GroupScheme.IsIsogeny (groupHom f.asHom) then
    (hom f.asHom).finrank (η[A.X].left (Classical.arbitrary (Spec (CommRingCat.of k))))
  else 0

end Langlands.AbelianScheme
