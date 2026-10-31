import Langlands.AlgebraicGeometry.CotangentDualNumber
import Mathlib.RingTheory.Nakayama

/-! # Cotangent surjectivity for finite maps of augmented local algebras -/

universe u v w

namespace Langlands.CommutativeAlgebra

/-- A finite map of local algebras with a common rational residue field is
surjective if its cotangent map is surjective and its target is Noetherian. -/
def FiniteLocalCotangentSurjectivityStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (A : Type v) [CommRing A] [Algebra K A] [IsLocalRing A]
    (B : Type w) [CommRing B] [Algebra K B] [IsLocalRing B] [IsNoetherianRing B]
    (r : B →ₐ[K] K) (f : A →ₐ[K] B),
    letI := f.toRingHom.toAlgebra
    Module.Finite A B →
    Function.Surjective (Langlands.AlgebraicGeometry.augmentationCotangentMap r f) →
    Function.Surjective f

end Langlands.CommutativeAlgebra
