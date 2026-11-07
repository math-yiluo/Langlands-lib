# Statement: every rational point lies in a Borel subgroup

Author: Worker 1531.

This module defines the proposition
`Langlands.GroupScheme.BorelPointContainmentStatement.{u}`. A separate proof
must prove this exact proposition.

## Complete Lean proposition

```lean
def BorelPointContainmentStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X),
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G)
      (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X),
      IsBorelSubgroup i ∧ b ≫ i.hom.hom = g
```

The only import is `Langlands.GroupScheme.Absolute.Borel`. The namespace is
`Langlands.GroupScheme`, and the one universe parameter `u` is arbitrary.

## Objects, hypotheses and conclusion

The field `k : Type u` is algebraically closed, and its characteristic is
unrestricted. `G` is a group scheme over `Spec k` whose structure morphism is
smooth and affine and whose underlying space is connected. These are the same
instance hypotheses as in the published `BorelConjugacyStatement` and
`SolvableSubgroupBorelContainmentStatement`. No reductivity is assumed.

The point `g` is a morphism from `Over.mk (𝟙 (Spec k))`, the terminal object
of `Over (Spec k)`, to `G.X`, that is, an actual `k`-point of `G`.

The conclusion supplies an actual group scheme `B`, an actual homomorphism
`i : B ⟶ G` satisfying the published predicate `IsBorelSubgroup i`, and a
`k`-point `b` of `B` with `b ≫ i.hom.hom = g`. Here `i.hom.hom : B.X ⟶ G.X`
is the underlying morphism over `Spec k`. The equation says that `g` is the
image of a point of the Borel subgroup. The predicate `IsBorelSubgroup` is
the one in `Absolute.Borel`: a smooth connected solvable closed subgroup that
is maximal among such subgroups under actual factorizations. Since
`IsBorelSubgroup i` includes closedness, `i` is a closed immersion. The
point `b` is therefore determined by `g`.

The conclusion concerns `k`-points only. It does not say that `G` is covered
scheme-theoretically by the conjugates of a fixed Borel subgroup. It also
says nothing about the number of Borel subgroups containing `g`.

## Source

Provenance: source.

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field*, corrected reprint, Cambridge University Press, 2022,
registered source `milne-2022-algebraic-groups`. The registered PDF was read
at Section 17c, "The density theorem", printed pp.361–362 (one-based PDF
pp.372–373). Throughout that section, `G` is a connected group variety over
an algebraically closed field `k`. A group variety is a smooth algebraic
group, so it is of finite type. The Lean proposition additionally assumes
that `G` is affine, like the published Borel statements of the Library.
It is therefore a special case of Milne's corollary.

- Lemma 17.32 (printed p.361 and p.362): (a) if `G/H` is complete, the union
  of the conjugates of a connected subgroup variety `H` is closed; (b) it
  contains a nonempty open subset if some element of `H(k)` has finitely many
  fixed points on `(G/H)(k)`.
- Theorem 17.33 (printed p.362): (a) the union of the conjugates of
  `C_G(T)` contains a nonempty open subset of `|G|`; (b) for a Borel subgroup
  `B`, `|G| = ⋃_{g ∈ G(k)} g|B|g⁻¹`.
- Corollary 17.34 (printed p.362), first sentence: "Every element of `G(k)`
  is contained in a Borel subgroup of `G`." The proof observes that
  conjugates of `B` are Borel and that `G(k) = ⋃_{g ∈ G(k)} (gBg⁻¹)(k)`.

The Lean proposition is the first sentence of Corollary 17.34 for affine
`G`. Milne's hypotheses are formalized by the three instance arguments above
(smoothness, affineness and connectedness; finite type follows from
smoothness and affineness over a field), his Borel
subgroups by the published `IsBorelSubgroup`, and his containment by the
factorization `b ≫ i.hom.hom = g`. The second sentence of the corollary,
about normal Borel subgroups, is not part of this statement.

The registered errata snapshot `milne-2022-algebraic-groups-errata-2026-11-04`
was read and has no entry for printed pp.360–364. The same result is
A. Borel, *Linear Algebraic Groups*, 2nd ed., Theorem 11.10.

## Boundary

This unit states the proposition only. It does not prove it, and it supplies
no density, closedness or completeness results for `G/B`. Borel existence and
conjugacy are published separately as `BorelConjugacyStatement` and are not
premises here.
