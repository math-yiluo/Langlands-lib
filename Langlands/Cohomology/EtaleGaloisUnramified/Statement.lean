import Langlands.Geometry.EtaleGaloisAction
import Langlands.Shimura.DecompositionGroupAction

/-!
# Almost-everywhere unramified Galois actions on étale cohomology

Let `K` be a number field and `f : X ⟶ Spec K` a morphism of finite type. The absolute Galois
group of `K` acts on the étale cohomology of `X ×_{Spec K} Spec K̄` with constant coefficients
through the second factor. This module states that for a finite coefficient module the action
in each degree is unramified at all but finitely many finite places of `K`: the inertia subgroup
of the completion at the place acts trivially. The truth argument is Deligne's generic base
change theorem, SGA 4½ [Th. finitude] 1.9.
-/

namespace Langlands.Cohomology.EtaleGaloisUnramified

open AlgebraicGeometry Langlands.Geometry.EtaleGaloisAction Langlands.Shimura

universe u

/-- For a number field `K`, a morphism of finite type `f : X ⟶ Spec K` and a commutative ring
`R`: for every finite `R`-module `M` and every degree `n`, the action of the absolute Galois group
of `K` on the degree `n` étale cohomology of `X ×_{Spec K} Spec K̄` with constant coefficients
`M` is unramified at every finite place of `K` outside some finite set. -/
def GaloisCohomologyUnramifiedStatement (K : Type u) [Field K] [NumberField K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    [QuasiCompact f] (R : Type u) [CommRing R] : Prop :=
  ∀ (M : ModuleCat.{u} R) [Finite M] (n : ℕ),
    ∃ S : Set (Global.FinitePlace K), S.Finite ∧ ∀ v ∉ S,
      DecompositionGroupAction.IsUnramifiedAt (ModuleCat.{u} R) v
        ((Rep.RepToAction R (Field.absoluteGaloisGroup K)).obj
          (galoisCohomologyRep (L := AlgebraicClosure K) f R M n))

end Langlands.Cohomology.EtaleGaloisUnramified
