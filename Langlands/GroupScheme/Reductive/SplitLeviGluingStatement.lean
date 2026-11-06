import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Reductive.RootDatum

/-! # Statement: gluing isomorphisms of the Levi subgroups of semisimple rank at most one -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Gluing step of the Isomorphism Theorem, common torus** (Milne 23.16–23.18, the
isomorphism case for the identity of the character lattice; Steinberg's graph argument). Take
the data of `SplitCommonTorusIsomorphismStatement`: maximal tori `i₁ : T ⟶ G₁` and
`i₂ : T ⟶ G₂` of connected reductive groups over a field with the same split torus `T`, and
root data `P₁` of `i₁` and `P₂` of `i₂` that differ by a reindexing `e` matching their roots
and their coroots. Suppose that the isomorphism exists for the centralizers of cocharacters of
semisimple rank at most one: for every cocharacter `ν` of `T` such that any two roots `α`,
`β` of `i₁` with `⟨α, ν⟩ = ⟨β, ν⟩ = 0` are linearly dependent over `ℤ`, and all closed
subgroups `z₁ : Z₁ ⟶ G₁` and `z₂ : Z₂ ⟶ G₂` representing the dynamic centralizers of
`ν ≫ i₁` and `ν ≫ i₂`, with `t₁ : T ⟶ Z₁` and `t₂ : T ⟶ Z₂` such that `t₁ ≫ z₁ = i₁` and
`t₂ ≫ z₂ = i₂`, there is an isomorphism `φ : Z₁ ≅ Z₂` with `t₁ ≫ φ.hom = t₂`. Then there is
an isomorphism `ψ : G₁ ≅ G₂` with `i₁ ≫ ψ.hom = i₂`. -/
def SplitCommonTorusLeviGluingStatement : Prop :=
  ∀ (k : Type u) [Field k] (G₁ G₂ : GroupScheme (Spec (CommRingCat.of k)))
    (hG₁ : IsConnectedReductive G₁) (hG₂ : IsConnectedReductive G₂)
    (T : CommGroupScheme (Spec (CommRingCat.of k))), IsSplitTorus T.toGrp →
    ∀ (i₁ : T.toGrp ⟶ G₁) (i₂ : T.toGrp ⟶ G₂), IsMaximalTorus i₁ → IsMaximalTorus i₂ →
    ∀ (J₁ J₂ : Type u) (P₁ : RootDatum J₁ (characterLattice T) (cocharacterLattice T))
      (P₂ : RootDatum J₂ (characterLattice T) (cocharacterLattice T)),
      (haveI := hG₁.isAffineHom; IsRootDatumOf i₁ P₁) →
      (haveI := hG₂.isAffineHom; IsRootDatumOf i₂ P₂) →
      ∀ e : J₁ ≃ J₂, ⇑P₂.root ∘ ⇑e = ⇑P₁.root → ⇑P₂.coroot ∘ ⇑e = ⇑P₁.coroot →
      (∀ ν : cocharacterLattice T,
        (haveI := hG₁.isAffineHom
          ∀ α ∈ roots i₁, ∀ β ∈ roots i₁, latticePairing T α ν = 0 →
            latticePairing T β ν = 0 → ¬ LinearIndependent ℤ ![α, β]) →
        ∀ (Z₁ Z₂ : GroupScheme (Spec (CommRingCat.of k))) (z₁ : Z₁ ⟶ G₁) (z₂ : Z₂ ⟶ G₂),
          IsClosedSubgroup z₁ → IsClosedSubgroup z₂ →
          (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i₁)).IsRepresentedBy z₁ →
          (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i₂)).IsRepresentedBy z₂ →
          ∀ (t₁ : T.toGrp ⟶ Z₁) (t₂ : T.toGrp ⟶ Z₂), t₁ ≫ z₁ = i₁ → t₂ ≫ z₂ = i₂ →
            ∃ φ : Z₁ ≅ Z₂, t₁ ≫ φ.hom = t₂) →
        ∃ ψ : G₁ ≅ G₂, i₁ ≫ ψ.hom = i₂

end Langlands.GroupScheme
