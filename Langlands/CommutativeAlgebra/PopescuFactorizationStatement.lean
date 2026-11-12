import Langlands.CommutativeAlgebra.RegularRingMaps
import Mathlib.RingTheory.Smooth.Basic

/-! # Finite-type factorization through a smooth algebra -/

universe u

namespace Langlands.CommutativeAlgebra

/-- The finite-type factorization consequence of Popescu's theorem for regular
maps between Noetherian rings. -/
def PopescuFactorizationStatement : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S],
    RegularAlgebra R S →
      ∀ (C : Type u) [CommRing C] [Algebra R C] [Algebra.FiniteType R C]
        (f : C →ₐ[R] S),
        ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B),
          Algebra.Smooth R B ∧
            ∃ (g : C →ₐ[R] B) (h : B →ₐ[R] S), h.comp g = f

end Langlands.CommutativeAlgebra
