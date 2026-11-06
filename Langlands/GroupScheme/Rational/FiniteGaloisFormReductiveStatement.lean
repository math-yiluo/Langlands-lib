import Langlands.GroupScheme.LocalGroupIso
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.FieldTheory.Galois.Basic

/-! # Statement: connected reductivity of finite-Galois forms -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Connected reductivity passes to finite-Galois forms.** If natural local group
isomorphisms from `G` to `H` exist on the points of the cover `Spec L → Spec K` of a finite
Galois extension `L/K`, and `G` is connected reductive, then so is `H`. -/
def FiniteGaloisFormConnectedReductiveStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (G H : GroupScheme (Spec (CommRingCat.of K))),
    LocalGroupIso G H (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))) →
    IsConnectedReductive G → IsConnectedReductive H

end Langlands.GroupScheme
