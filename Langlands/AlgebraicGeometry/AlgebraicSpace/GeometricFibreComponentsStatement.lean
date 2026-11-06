import Langlands.AlgebraicGeometry.AlgebraicSpace.SpacePoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestriction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Constructible
import Mathlib.Topology.Connected.Clopen
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Constructibility of the number of geometric connected components

Conrad, *Weil and Grothendieck approaches to adelic points*, Lemma 5.1: for a finitely
presented algebraic space over a ring `B`, the locus of primes of `B` over which the geometric
fibre has exactly `n` connected components is constructible.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's Lemma 5.1. Let `X` be a quasi-separated algebraic space over `Spec B` with an
étale surjective atlas locally of finite presentation and quasi-compact over `Spec B`, and let
`n` be a natural number. For a point `p` of `Spec B` with residue field `κ(p)`, the geometric
fibre is the presheaf product `X × h_{Spec Ω}` over `Spec B`, where `Ω` is the algebraic
closure of `κ(p)` and `Spec Ω ⟶ Spec κ(p) ⟶ Spec B` is the canonical map. The set of points
`p` at which the points of the geometric fibre, with their topology, have exactly `n`
connected components is constructible in `Spec B`. -/
def GeometricFibreComponentsConstructibleStatement : Prop :=
  ∀ (B : Type u) [CommRing B] (X : AlgebraicSpace (Spec (CommRingCat.of B))),
    IsQuasiSeparated X → FinitePresentationOverRing B X → ∀ n : ℕ,
      Topology.IsConstructible
        {p : Spec (CommRingCat.of B) |
          ENat.card
            (@ConnectedComponents
              (Points (X.presheaf ⨯ (schemeYoneda (Spec (CommRingCat.of B))).obj
                (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap
                    ((Spec (CommRingCat.of B)).residueField p)
                    (AlgebraicClosure ((Spec (CommRingCat.of B)).residueField p)))) ≫
                  (Spec (CommRingCat.of B)).fromSpecResidueField p))))
              (pointTopology _)) = n}

end Langlands.AlgebraicGeometry.AlgebraicSpace
