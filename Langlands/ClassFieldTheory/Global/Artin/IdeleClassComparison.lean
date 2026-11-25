import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibComparison
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison
import Langlands.Global.Adelic

/-!
# The idèle class group of the NYLL library against the Library's

This file belongs to the Library. It states the comparison of the NYLL library's idèle class
group with the Library's `Langlands.Global.IdeleClasses K` (which is Mathlib's
`NumberField.IdeleClassGroup (𝓞 K) K`) in the Library's vocabulary.

NYLL's group `_root_.IdeleClassGroup K` is the quotient of its own idèle group, an infinite
part times a restricted product of the unit groups of the adic completions, by the principal
idèles. NYLL proves that it is isomorphic, as a topological group, to Mathlib's group; this
file gives that isomorphism a Library name and records where the one-place idèle classes go.

## Main declarations

* `nyllIdeleClassEquiv K : _root_.IdeleClassGroup K ≃ₜ* IdeleClasses K`.
* `nyllIdeleClassEquiv_finitePlaceIdeleClass`: the class of a local unit at a finite place
  `v`, put at `v` and `1` elsewhere, goes to the Library's `finiteClassInclusion K v`.
-/

noncomputable section

universe u

namespace Langlands.ClassFieldTheory.Global.Artin

open Langlands.Global

variable (K : Type u) [Field K] [NumberField K]

/-- NYLL's idèle class group, a quotient of a restricted product of unit groups, as a
topological group isomorphic to the Library's `IdeleClasses K`, which is Mathlib's idèle
class group. -/
def nyllIdeleClassEquiv : _root_.IdeleClassGroup K ≃ₜ* IdeleClasses K :=
  _root_.IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K

theorem nyllIdeleClassEquiv_apply (c : _root_.IdeleClassGroup K) :
    nyllIdeleClassEquiv K c = _root_.IdeleGroup.ideleClassGroupEquivMathlib K c :=
  rfl

/-- The one-place idèle class of a local unit at a finite place corresponds to the Library's
`finiteClassInclusion`. -/
theorem nyllIdeleClassEquiv_finitePlaceIdeleClass (v : Langlands.Global.FinitePlace K)
    (x : (FiniteCompletion K v)ˣ) :
    nyllIdeleClassEquiv K (_root_.IdeleGroup.finitePlaceIdeleClass v x) =
      finiteClassInclusion K v x :=
  _root_.IdeleGroup.ideleClassGroupEquivMathlib_finitePlaceIdeleClass K v x

theorem nyllIdeleClassEquiv_symm_finiteClassInclusion (v : Langlands.Global.FinitePlace K)
    (x : (FiniteCompletion K v)ˣ) :
    (nyllIdeleClassEquiv K).symm (finiteClassInclusion K v x) =
      _root_.IdeleGroup.finitePlaceIdeleClass v x := by
  rw [← nyllIdeleClassEquiv_finitePlaceIdeleClass, ContinuousMulEquiv.symm_apply_apply]

end Langlands.ClassFieldTheory.Global.Artin
