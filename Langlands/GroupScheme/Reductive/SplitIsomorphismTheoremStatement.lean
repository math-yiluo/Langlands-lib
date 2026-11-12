import Langlands.GroupScheme.Reductive.RootDatum
import Mathlib.LinearAlgebra.RootSystem.Hom

/-! # Statement: the Isomorphism Theorem for split reductive groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Isomorphism Theorem** (Milne, *Algebraic Groups* (2017), Theorem 23.25 in its
"isomorphism" form, and Remark 23.26; existence part). Let `i : T ⟶ G` and `i' : T' ⟶ G'`
be split maximal tori of connected reductive groups over a field, with root data `P` of `i`
and `P'` of `i'`. Every equivalence of root pairings `f : P' ≃ P` arises from an isomorphism
`φ : G ≅ G'` and an isomorphism of tori `t : T ≅ T'` with `i ≫ φ.hom = t.hom ≫ i'` and
`f χ = t.hom ≫ χ` for every character `χ` of `T'`. -/
def SplitIsomorphismTheoremStatement : Prop :=
  ∀ (k : Type u) [Field k] (G G' : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (T T' : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → IsSplitTorus T'.toGrp →
    ∀ (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G'), IsMaximalTorus i → IsMaximalTorus i' →
    ∀ (J J' : Type u) (P : RootDatum J (characterLattice T) (cocharacterLattice T))
      (P' : RootDatum J' (characterLattice T') (cocharacterLattice T')),
      (haveI := hG.isAffineHom; IsRootDatumOf i P) →
      (haveI := hG'.isAffineHom; IsRootDatumOf i' P') →
      ∀ f : RootPairing.Equiv P' P,
        ∃ (φ : G ≅ G') (t : T ≅ T'), i ≫ φ.hom = CommGroupScheme.groupHom t.hom ≫ i' ∧
          ∀ χ : characterLattice T', f.weightMap χ = t.hom ≫ χ

end Langlands.GroupScheme
