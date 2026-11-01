import Langlands.Representation.RankinSelberg.TwoBlockDominantRectangularData
import Langlands.Group.GL.Maps

/-! # The actual reversed-dual matrices in JPSS Section 4.10 -/

namespace Langlands.RankinSelberg

open GeneralLinear TwoBlockDominantRectangular TwoBlockLowerUnipotentQuotient

universe uF

/-- The three-Weyl, signed rectangle and full reversed-dual matrix identities
for the complementary five-block decompositions in JPSS Section 4.10. -/
def TwoBlockDominantDualMatrixStatement : Prop :=
  ∀ (K : Type uF) [Field K] (t r j k : ℕ) (m : Fin 2 → ℕ)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1)),
    let mD : Fin 2 → ℕ := fun i => m i.rev
    let hD : ∑ i, (mD i + 1) = t + 1 := reverse_sum h
    let hrD : r = t + (k + j + 1) := by omega
    (blockWeyl (K := K) (m := mD) (j := k) (k := j) hD hrD *
        append hr (weylLong (t + 1) K) * rightWeyl hr =
      weylLong (r + 1) K * blockWeyl h hr) ∧
    ∀ (xD : Matrix (Fin (m 1 + 1)) (Fin j) K)
      (yD : Matrix (Fin k) (Fin (m 0 + 1)) K),
      let x : Matrix (Fin (m 0 + 1)) (Fin k) K := fun i l => -yD l.rev i.rev
      let y : Matrix (Fin j) (Fin (m 1 + 1)) K := fun i l => -xD l.rev i.rev
      (weylLong (r + 1) K *
          inverseTranspose (r + 1) K
            (rectangleUnipotent (m := mD) (j := k) (k := j) hD hrD xD yD) *
          weylLong (r + 1) K =
        rectangleUnipotent h hr x y) ∧
      ∀ g : GeneralLinear (t + 1) K,
        let Tg := weylLong (t + 1) K * inverseTranspose (t + 1) K g
        weylLong (r + 1) K *
            inverseTranspose (r + 1) K (reversedMatrix h hr Tg xD yD) =
          matrix h hr g x y

end Langlands.RankinSelberg
