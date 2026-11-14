import Langlands.Global.AdelicGaloisTwistDescent

/-! # Galois twisting preserves norm-one adelic points (Lemma C)

This module states `TwistPointNormOneStatement`, an input of the proof of
`GaloisBorelTwistingStatement`: the Galois translate `twistPoint` of a norm-one upper adelic
point of an `L`-group is a norm-one adelic point of the Galois-translated group.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Lemma C: the Galois translate of a norm-one upper adelic point of an `L`-group is a
norm-one adelic point of the Galois-translated group. -/
def TwistPointNormOneStatement : Prop :=
  ∀ (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] (σ : L ≃ₐ[F] L)
    (H : GroupScheme (Spec (CommRingCat.of L))) (p : adeleTest L ⟶ H.X),
    (p : AdelicGroupPoints L H) ∈ normOneSubgroup L H →
      (twistPoint F L σ H p :
          AdelicGroupPoints L ((GroupScheme.baseChange (galoisBaseMap F L σ)).obj H)) ∈
        normOneSubgroup L ((GroupScheme.baseChange (galoisBaseMap F L σ)).obj H)

end Langlands.Global.AdelicGaloisUnit
