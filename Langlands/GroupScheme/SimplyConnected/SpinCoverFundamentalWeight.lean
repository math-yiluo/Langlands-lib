import Langlands.GroupScheme.Reductive.TitsIndex

/-!
# Fundamental weights trivial on the kernel of a homomorphism

For a numbered Tits index of `G` and a homomorphism `π : G ⟶ H`, this file
records when the fundamental weight attached to one simple vertex is trivial on
the part of `ker π` lying in the pinning torus, over the separable closure.

It is used to say which end vertex of a type-`D` diagram is the vector vertex
of a spin cover: the kernel of `Spin_{2n} → SO_{2n}` is killed exactly by the
weights in the weight lattice of `SO_{2n}`, and among the fundamental weights at
the ends of the diagram only the vector weight lies there.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace TitsIndexData

variable {K : Type u} [Field K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The fundamental weight at the simple vertex `v` is trivial on the kernel of
`π` restricted to the pinning torus, over the separable closure `K^s`.

A character `χ` of the base-changed pinning torus `T_{K^s}` is the fundamental
weight at `v` when its pairing with the simple coroot of `v` is `1` and its
pairing with every other simple coroot is `0`. The kernel of `π` on `T_{K^s}` is
read through points: a point `t` of `T_{K^s}` over a `K^s`-scheme `U` lies in it
when its image under `(T ⟶ G ⟶ H)_{K^s}` is the identity. The proposition says
that every such `χ` sends every such `t` to `1`. -/
def FundamentalWeightTrivialOnKernel (d : TitsIndexData G) (v : d.Vertex)
    (π : G ⟶ H) : Prop :=
  ∀ χ : characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).obj
        d.pinning.torus),
    latticePairing _ χ (d.pinning.rootDatum.coroot v.val) = 1 →
    (∀ b : d.Vertex, b ≠ v → latticePairing _ χ (d.pinning.rootDatum.coroot b.val) = 0) →
    ∀ (U : Over (Spec (CommRingCat.of (SeparableClosure K))))
      (t : U ⟶ ((CommGroupScheme.baseChange
        (algebraBaseMap K (SeparableClosure K))).obj d.pinning.torus).X),
      t ≫ ((GroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map
          (d.pinning.inclusion ≫ π)).hom.hom = 1 →
        t ≫ (CommGroupScheme.groupHom χ).hom.hom = 1

end TitsIndexData

end Langlands.GroupScheme
