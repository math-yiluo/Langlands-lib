import Langlands.GroupScheme.Reductive.RootDatum

/-! # Statement: the Isomorphism Theorem in semisimple rank at most one, common torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Isomorphism Theorem in semisimple rank at most one, common torus** (Milne Proposition
23.14, isomorphism case, for the identity of the character lattice; compare Remark 23.26).
This is `SplitCommonTorusIsomorphismStatement` with one added hypothesis: any two roots of
`i₁` are linearly dependent over `ℤ` in the character lattice. Let `i₁ : T ⟶ G₁` and
`i₂ : T ⟶ G₂` be maximal tori of connected reductive groups over a field with the same split
torus `T`. If root data `P₁` of `i₁` and `P₂` of `i₂` differ by a reindexing `e` that matches
their roots and their coroots, then there is an isomorphism `ψ : G₁ ≅ G₂` with
`i₁ ≫ ψ.hom = i₂`. -/
def SplitRankOneCommonTorusIsomorphismStatement : Prop :=
  ∀ (k : Type u) [Field k] (G₁ G₂ : GroupScheme (Spec (CommRingCat.of k)))
    (hG₁ : IsConnectedReductive G₁) (hG₂ : IsConnectedReductive G₂)
    (T : CommGroupScheme (Spec (CommRingCat.of k))), IsSplitTorus T.toGrp →
    ∀ (i₁ : T.toGrp ⟶ G₁) (i₂ : T.toGrp ⟶ G₂), IsMaximalTorus i₁ → IsMaximalTorus i₂ →
    ∀ (J₁ J₂ : Type u) (P₁ : RootDatum J₁ (characterLattice T) (cocharacterLattice T))
      (P₂ : RootDatum J₂ (characterLattice T) (cocharacterLattice T)),
      (haveI := hG₁.isAffineHom; IsRootDatumOf i₁ P₁) →
      (haveI := hG₂.isAffineHom; IsRootDatumOf i₂ P₂) →
      ∀ e : J₁ ≃ J₂, ⇑P₂.root ∘ ⇑e = ⇑P₁.root → ⇑P₂.coroot ∘ ⇑e = ⇑P₁.coroot →
      (haveI := hG₁.isAffineHom
        ∀ α ∈ roots i₁, ∀ β ∈ roots i₁, ¬ LinearIndependent ℤ ![α, β]) →
        ∃ ψ : G₁ ≅ G₂, i₁ ≫ ψ.hom = i₂

end Langlands.GroupScheme
