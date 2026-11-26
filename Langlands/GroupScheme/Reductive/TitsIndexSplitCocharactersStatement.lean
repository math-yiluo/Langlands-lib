import Langlands.GroupScheme.Reductive.TitsIndex

/-! # The cocharacter lattice of the maximal split torus from the Tits index -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The integral form of the cocharacter equations in Tits, §2.5.1. A cocharacter of
`T` over the separable closure comes from a unique cocharacter of the chosen maximal
split torus `S` if and only if it annihilates the zero-restriction simple roots and
its pairings with absolute simple roots are constant on absolute Galois star orbits. -/
def TitsIndexSplitCocharactersStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G),
    let b := algebraBaseMap k (SeparableClosure k)
    ∀ μ : cocharacterLattice ((CommGroupScheme.baseChange b).obj d.pinning.torus),
      (∃! η : cocharacterLattice d.splitTorus,
        cocharacterLattice.baseChange b d.pinning.torus (η ≫ d.torusMap) = μ) ↔
      (∀ a ∈ d.zeroVertices, d.pinning.rootDatum.root' a.val μ = 0) ∧
      ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a : d.Vertex),
        d.pinning.rootDatum.root' (d.star σ a).val μ = d.pinning.rootDatum.root' a.val μ

end Langlands.GroupScheme
