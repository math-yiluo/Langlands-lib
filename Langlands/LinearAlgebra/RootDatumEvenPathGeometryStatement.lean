import Langlands.LinearAlgebra.RootDatumEvenPathGeometry

/-! # Existence of stable even paths and middle-out remaining-root orbit blocks -/

universe u v w z

namespace Langlands.LinearAlgebra

open RootDatumEvenPathGeometry RootDatumOrbitPairs

/-- A pairing-compatible simple-root action admits disjoint even path
components preserved up to reversal and an orthogonal orbit-block ordering of
the remaining roots which is middle-out along every selected path. -/
def EvenPathOrbitGeometryStatement : Prop :=
  ∀ (I : Type u) [Finite I] (M : Type v) (N : Type w)
    [AddCommGroup M] [AddCommGroup N] (P : RootDatum I M N) (b : P.Base)
    (Γ : Type z) [Group Γ] (ρ : Γ →* Equiv.Perm b.support),
    IsPairingCompatible b ρ →
      ∃ (J : Type u) (_ : Fintype J) (C : EvenPathFamily b J),
        Nonempty (C.CompatibleAction ρ) ∧ Nonempty (C.OrbitOrdering ρ)

end Langlands.LinearAlgebra
