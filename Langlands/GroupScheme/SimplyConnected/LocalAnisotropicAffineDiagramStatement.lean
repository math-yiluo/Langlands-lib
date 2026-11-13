import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicInnerTypeAStatement

/-!
# A vertex-transitive affine extension of the Cartan matrix of an anisotropic local group

This module states, on actual Tits-index data, the building-theoretic input of
Kaletha–Prasad's proof of Theorem 10.3.1 over a nonarchimedean local field, together
with the splitting over the maximal unramified extension proved there. For an
anisotropic absolutely almost-simple group, the actual Cartan matrix extends by one
vertex to a generalized Cartan matrix with a positive left kernel vector whose
symmetries act transitively on its vertices. It supplies no proof.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix

namespace Langlands.GroupScheme

/-- Over a nonarchimedean local field, let `G` be an affine anisotropic absolutely
almost-simple group with actual index `d`. Then there is an integer matrix `A` on
`Option d.Vertex` with the following properties. Its block on the actual simple
vertices is the actual Cartan matrix `d.cartan`. Its diagonal entries are `2`, its
off-diagonal entries are nonpositive and its zero pattern is symmetric. Some vector
`m` with positive entries satisfies `m ᵥ* A = 0`. For all indices `i` and `j`, some
permutation `σ` with `A (σ k) (σ l) = A k l` for all `k` and `l` sends `i` to `j`.

In the source, `A` is the matrix of Cartan integers of the basis of the affine root
system of `G` over the maximal unramified extension `K'` of `K` determined by a
`Gal(K'/K)`-stable chamber, with `none` the simple affine root whose gradient is not
simple for the finite root system. The vector `m` lists the positive coefficients of
the simple affine roots in their sum that is constant, and the permutations come from
the transitive action of `Gal(K'/K)` on that basis. Identifying the block of `A` with
the absolute matrix `d.cartan` uses that `G` splits over `K'`, which the source
derives at the end of the same proof from the classification of affine root
systems. -/
def LocalAnisotropicAffineDiagramStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G),
    IsAbsolutelyAlmostSimple G → IsAnisotropic G →
      ∃ A : Matrix (Option d.Vertex) (Option d.Vertex) ℤ,
        (∀ a b, A (some a) (some b) = d.cartan a b) ∧
        (∀ i, A i i = 2) ∧
        (∀ i j, i ≠ j → A i j ≤ 0) ∧
        (∀ i j, A i j = 0 ↔ A j i = 0) ∧
        (∃ m : Option d.Vertex → ℤ, (∀ i, 0 < m i) ∧ m ᵥ* A = 0) ∧
        ∀ i j, ∃ σ : Equiv.Perm (Option d.Vertex),
          (∀ k l, A (σ k) (σ l) = A k l) ∧ σ i = j

end Langlands.GroupScheme
