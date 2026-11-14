import Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement
import Langlands.AllField.Group.GL.PadicSupplement
/-!
# The exact compact open orbit of the last row

This proposition isolates the matrix geometry behind the Schwartz test used in
the equal-rank JPSS argument. It does not assert a proof or an integral identity.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding LastRowCompactOrbitStatement
open Langlands.AllField.RankinSelberg

universe uF

/-- For every compact open subgroup of the actual positive-rank general linear
group, its last-row orbit is compact open in the full row space, has an exact
Schwartz–Bruhat indicator, and has inverse image equal to the product of the
actual mirabolic subgroup with the supplied open subgroup. -/
def LastRowCompactOrbitStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  let G := Langlands.GeneralLinear (n + 1) F
  let P := GeneralLinear.mirabolic n F
  ∀ J : OpenSubgroup G, IsCompact (J : Set G) →
    let R : Set (Fin (n + 1) → F) := lastRow '' (J : Set G)
    IsCompact R ∧ IsOpen R ∧
    (∀ r ∈ R, r ≠ 0) ∧
    lastRow (1 : G) ∈ R ∧
    (∃ Φ : HarmonicAnalysis.SchwartzBruhat (Fin (n + 1) → F),
      (Φ : (Fin (n + 1) → F) → ℂ) = R.indicator (fun _ => (1 : ℂ))) ∧
    (∀ g : G, lastRow g ∈ R ↔
      ∃ (a : P) (j : J), g = a.val * j.val)

end Langlands.AllField.RankinSelberg
