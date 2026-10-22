import Langlands.Geometry.EtaleGaloisAction
import Langlands.Representation.Smooth.Definitions
import Mathlib.FieldTheory.KrullTopology

/-!
# Smoothness of Galois actions on étale cohomology with constant coefficients

Let `L / K` be an algebraic extension of fields and `f : X ⟶ Spec K` a
quasi-compact quasi-separated morphism of schemes. The group `L ≃ₐ[K] L` of
`K`-automorphisms of `L` acts on the étale cohomology of the base change
`X ×_{Spec K} Spec L` with constant coefficients through the second factor.
This statement says that the action is smooth for the Krull topology: every
cohomology class is fixed by an open subgroup. The source of the argument is
SGA 4, Exposé VII, Corollaire 5.8: the cohomology of the base change is the
colimit of the cohomology of the base changes to finite subextensions.
-/

namespace Langlands.Cohomology.EtaleGaloisSmooth

open AlgebraicGeometry Langlands.Geometry.EtaleGaloisAction

universe u

/-- For an algebraic field extension `L / K` and a quasi-compact
quasi-separated `f : X ⟶ Spec K`, the action of `L ≃ₐ[K] L`, with its Krull
topology, on every étale cohomology module of `X ×_{Spec K} Spec L` with
constant coefficients is smooth. -/
def GaloisCohomologySmoothStatement (K : Type u) [Field K] (L : Type u) [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [QuasiCompact f] [QuasiSeparated f]
    (R : Type u) [CommRing R] : Prop :=
  ∀ (M : ModuleCat.{u} R) (n : ℕ),
    Langlands.IsSmooth (galoisCohomologyRep (L := L) f R M n).ρ

end Langlands.Cohomology.EtaleGaloisSmooth
