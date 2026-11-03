import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.CentralIsogeny.Basic
import Mathlib.LinearAlgebra.RootSystem.Hom

/-! # The morphism of root data defined by a central isogeny of split reductive groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Central isogenies define morphisms of root data** (Milne Proposition 23.5, central case,
with Definitions 23.1 and 23.2). Let `φ : G ⟶ G'` be a central isogeny of connected reductive
groups over a field, `i : T ⟶ G` and `i' : T' ⟶ G'` maximal tori with `T`, `T'` split, and
`t : T ⟶ T'` with `i ≫ φ = t ≫ i'`. For root data `P`, `P'` of `i`, `i'`, there is a morphism
of root pairings `P' ⟶ P` with weight map `χ ↦ t ≫ χ` and coweight map `ν ↦ ν ≫ t`, both
injective, and `φ` is an isomorphism exactly when the weight map is bijective. -/
def CentralIsogenyRootDatumHomStatement : Prop :=
  ∀ (k : Type u) [Field k] (G G' : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (T T' : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → IsSplitTorus T'.toGrp →
    ∀ (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G'), IsMaximalTorus i → IsMaximalTorus i' →
    ∀ (φ : G ⟶ G') (t : T ⟶ T'), IsCentralIsogeny φ →
      i ≫ φ = CommGroupScheme.groupHom t ≫ i' →
    ∀ (J J' : Type u) (P : RootDatum J (characterLattice T) (cocharacterLattice T))
      (P' : RootDatum J' (characterLattice T') (cocharacterLattice T')),
      (haveI := hG.isAffineHom; IsRootDatumOf i P) →
      (haveI := hG'.isAffineHom; IsRootDatumOf i' P') →
        ∃ f : RootPairing.Hom P' P,
          (∀ χ : characterLattice T', f.weightMap χ = t ≫ χ) ∧
          (∀ ν : cocharacterLattice T, f.coweightMap ν = ν ≫ t) ∧
          Function.Injective f.weightMap ∧ Function.Injective f.coweightMap ∧
          (IsIso φ ↔ Function.Bijective f.weightMap)

end Langlands.GroupScheme
