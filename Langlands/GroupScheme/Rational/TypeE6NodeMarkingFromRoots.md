# E₆ markings with marked short arm and unmarked centre

Module: `Langlands.GroupScheme.Rational.TypeE6NodeMarkingFromRoots`.

## Statement

```lean
def TypeE6NodeMarkingStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
    (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
    IsSimplyConnected G → e.symm 1 ∈ d.distinguishedVertices →
    e.symm 3 ∉ d.distinguishedVertices →
    e.symm 2 ∉ d.distinguishedVertices ∧ e.symm 4 ∉ d.distinguishedVertices ∧
      (e.symm 5 ∈ d.distinguishedVertices ↔ e.symm 0 ∈ d.distinguishedVertices) ∧
      (e.symm 0 ∈ d.distinguishedVertices →
        ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
          ∀ j, d.star σ (e.symm j) = e.symm (symmetry j))
```

`typeE6NodeMarking : TypeE6NodeMarkingStatement.{u}` proves it.

Let `G` be an affine, locally finite-type, simply connected group over any field `k`, with
actual Tits index data `d` whose simple vertices are numbered by `CartanMatrix.E 6` through
`e` (numbering as in [`LinearAlgebra.CartanE6NodeMarking`](../../LinearAlgebra/CartanE6NodeMarking.md):
vertex `i` is Bourbaki's `α_{i+1}`). Suppose the short-arm vertex `1` (`α₂`) is
distinguished and the central vertex `3` (`α₄`) is not. Then the inner long-arm vertices
`2` and `4` are not distinguished, and the endpoints `0` and `5` are distinguished together.
If they are, some element of the absolute Galois group acts on the simple vertices by the
exchange `symmetry` of the two long arms (module `LinearAlgebra.CartanE6Root`), so `G` is an
outer form. There is no hypothesis on the field and no isotropy or almost-simplicity
hypothesis.

## Proof

1. *Opposition and star action.* The actual opposition involution of the index is the arm
   exchange (`opposition_eq_symmetry_of_E6`, module
   [`SimplyConnected.TypeE6Opposition`](../SimplyConnected/TypeE6Opposition.md)), and it
   preserves distinguished vertices (`opposition_mem_distinguished_iff`). So `0, 5` and
   `2, 4` are marked in pairs. Every Galois element preserves the Cartan entries, so it acts
   on the numbered vertices as the identity or as the arm exchange
   (`CartanE6Root.eq_id_or_symmetry_of_preserves`). These facts give a `NodeMarking` `p`
   whose flag `swapsArms` records whether some element exchanges the arms.
2. *Coordinates.* Let `R j` be the restriction of the simple root at vertex `j` to the
   maximal split torus. Unmarked vertices restrict to zero, and two marked vertices have the
   same restriction exactly when they lie in one star orbit
   (`titsIndexRelativeSimpleRoots`). Hence `∑ j, (project p c) j • R j = ∑ j, c j • R j`
   for all integral coordinates `c`. The restrictions at the active representatives are the
   distinct simple relative roots, which are linearly independent
   (`HasRelativeRootSystem.linearIndependent_simpleRelativeRoots`). So the map
   `c ↦ ∑ j, c j • R j`, into the rational span of the relative roots, is injective on
   vectors supported on active coordinates.
3. *Roots.* Every listed coefficient vector of
   [`LinearAlgebra.CartanE6RootCoordinates`](../../LinearAlgebra/CartanE6RootCoordinates.md)
   is an actual absolute root (`isRoot_positiveCoefficients`), and every actual root is a
   signed listed vector (`exists_signedCoefficients`). Restricting, a vector supported on
   active coordinates is a projected root exactly when its image is zero or a relative root.
4. *Reflections.* By the Library's relative root system (`relativeRootSystem`), the relative
   roots are the roots of a crystallographic root pairing over `ℚ`. For the root `r`
   represented by `m • unit i`, the integral pairings of the coroot of `r` with the images
   of the unit vectors give `f`, and the reflection in `r` gives closure. This is the private
   lemma `integralReflections`, which yields `p.HasIntegralReflections`.
5. *Conclusion.* `NodeMarking.eq_of_hasIntegralReflections` excludes the inner long-arm
   vertices and, without an arm exchange, the endpoints.

## Source

Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), registered as
`platonov-rapinchuk-1994-algebraic-groups-number-theory`, §6.8, diagrams (6.52), (6.53)
and (6.57), printed pp. 379 and 382: among the isotropic E₆ indices with `α₂`
distinguished and `α₄` not, only (6.53)(a) (`α₂` alone) and (6.53)(c) (`α₁, α₂, α₆`), both
outer, occur. The theorem here derives the restriction on the marking from the relative
root system and the finite calculation. The inner marking with `α₂` alone satisfies the
reflection condition and is excluded separately in the Library by
`TitsIndexData.not_hasRankOneE6BranchIndex` (module
[`SimplyConnected.LocalRankOneE6Exclusion`](../SimplyConnected/LocalRankOneE6Exclusion.md)).
