import Langlands.AbelianScheme.MultiplicationIsogenyStatement
import Langlands.AbelianScheme.MultiplicationSign
import Langlands.AbelianScheme.FieldMultiplicationIsogenyProof
import Langlands.AbelianScheme.FiberwiseIsogeny
import Mathlib.AlgebraicGeometry.Fiber

/-! # Nonzero integer multiplication is an isogeny over any base scheme -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Nonzero integer multiplication is finite, flat and surjective on every
commutative smooth proper geometrically connected group scheme. -/
theorem multiplicationIsogeny : MultiplicationIsogenyStatement.{u} := by
  intro S G hcomm hs hp hc n hn
  let := hs
  let := hp
  let := hc
  apply isIsogeny_multiplication_of_positive G ?_ n hn
  intro m hm
  apply fiberwiseIsogeny S G G hs hs hp hp (multiplication G (m : ℤ))
  intro s
  rw [multiplication_baseChange]
  let Gs := (Over.pullback (S.fromSpecResidueField s)).mapGrp.obj G
  have hs' : Smooth Gs.X.hom := by
    change Smooth (Limits.pullback.snd G.X.hom (S.fromSpecResidueField s))
    infer_instance
  have hp' : IsProper Gs.X.hom := by
    change IsProper (Limits.pullback.snd G.X.hom (S.fromSpecResidueField s))
    infer_instance
  have hc' : GeometricallyConnected Gs.X.hom := by
    change GeometricallyConnected (Limits.pullback.snd G.X.hom (S.fromSpecResidueField s))
    infer_instance
  exact fieldMultiplicationIsogeny (S.residueField s) Gs hs' hp' hc' m hm

end Langlands.GroupScheme
