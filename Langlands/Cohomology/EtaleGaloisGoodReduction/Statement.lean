import Langlands.Geometry.EtaleGaloisAction
import Langlands.Shimura.DecompositionGroupAction

/-!
# Unramified Galois actions on étale cohomology outside a uniform finite set of places

Let `K` be a number field and `f : X ⟶ Spec K` a smooth proper morphism. The absolute Galois
group of `K` acts on the étale cohomology of `X ×_{Spec K} Spec K̄` with constant coefficients
through the second factor. This module states that there is one finite set `S` of finite places
of `K` such that, for every finite coefficient module `M` and every degree, the action is
unramified at every finite place outside `S` whose residue characteristic does not divide the
order of `M`. The truth argument is the specialization theorem for smooth proper morphisms,
SGA 4 XVI Corollaire 2.2, after spreading `X` out over an open subscheme of `Spec O_K`.
-/

namespace Langlands.Cohomology.EtaleGaloisGoodReduction

open AlgebraicGeometry Langlands.Geometry.EtaleGaloisAction Langlands.Shimura

universe u

/-- For a number field `K`, a smooth proper morphism `f : X ⟶ Spec K` and a commutative ring `R`,
there is a finite set `S` of finite places of `K` such that for every finite `R`-module `M`, every
degree `n` and every finite place `v ∉ S` at which the order of `M` is a unit, the action of the
absolute Galois group of `K` on the degree `n` étale cohomology of `X ×_{Spec K} Spec K̄` with
constant coefficients `M` is unramified at `v`. -/
def GaloisCohomologyGoodReductionStatement (K : Type u) [Field K] [NumberField K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] [IsProper f]
    (R : Type u) [CommRing R] : Prop :=
  ∃ S : Set (Global.FinitePlace K), S.Finite ∧
    ∀ (M : ModuleCat.{u} R) [Finite M] (n : ℕ) (v : Global.FinitePlace K), v ∉ S →
      ((Nat.card M : NumberField.RingOfIntegers K) ∉ v.asIdeal) →
      DecompositionGroupAction.IsUnramifiedAt (ModuleCat.{u} R) v
        ((Rep.RepToAction R (Field.absoluteGaloisGroup K)).obj
          (galoisCohomologyRep (L := AlgebraicClosure K) f R M n))

end Langlands.Cohomology.EtaleGaloisGoodReduction
