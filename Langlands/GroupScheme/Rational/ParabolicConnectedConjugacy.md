# Parabolic connectedness and conjugacy from smooth-group conjugacy

This internal deduction proves `ParabolicConnectedStatement.{u}`: over every
field `k : Type u`, a subgroup `j : P ⟶ G` satisfying the published
`IsParabolicSubgroup j` is connected when `G` is smooth, affine and connected.
No reductivity or minimality is needed for this connectedness result. The
statement uses the existing geometric definition of a parabolic, with its
actual Borel factorization after extension to the algebraic closure.

`IsParabolicSubgroup.connectedSpace` proves the result. Put
`b = toAlgebraicClosure k` and `F = GroupScheme.baseChange b`. Smoothness
and affineness of `G` persist under base change, and the published
`connectedSpace_baseChange_of_smooth_affine` gives connectedness of `F.obj G`.
Parabolicity supplies a Borel subgroup `i : B ⟶ F.obj G` and an actual map
`f : B ⟶ F.obj P` with `f ≫ F.map j = i`. The original parabolic is smooth
and closed, so its base change has the same properties. The published theorem
`borelContainingSubgroupConnectedStatement` applies to these objects over
`AlgebraicClosure k` and proves `ConnectedSpace (F.obj P).X.left`.
The algebraic-closure field-extension map is surjective by
`fieldExtension_fpqc`. The published `connectedSpace_of_baseChange` therefore
reflects this connectedness to the original `P`.
`parabolicConnected` packages that proof as the named proposition.

The two remaining lemmas improve the existing parabolic split-torus
conjugacy reduction. They retain a single explicit premise,
`SmoothMaximalSplitTorusConjugacyStatement.{u}`. For a connected reductive
ambient group, smoothness and affineness of `P` follow from parabolicity and
its closed immersion, and connectedness follows from the preceding
unconditional theorem. The existing
`exists_innerIso_comp_eq_of_smooth_connected_closed_factorizations` then
transfers maximality of the two given ambient split tori into `P` and applies
the conjugacy premise to `P` itself. The resulting point is a ground-field
point of `P`, and the equation is

```lean
f ≫ (P.innerIso p).hom = e.hom ≫ f'
```

`minimalParabolicSplitTorusConjugacy_of_smoothConjugacy` specializes this to
the unchanged published `MinimalParabolicSplitTorusConjugacyStatement.{u}`.
It uses only the parabolic part of minimality. Finite fields, imperfect
fields and arbitrary characteristic are included throughout.

This unit proves connectedness, but its conjugacy conclusions still depend
on the unproved smooth-group conjugacy statement. It does not prove the
unconditional minimal-parabolic split-torus conjugacy target. The new
connectedness proof uses no parabolic-dynamic comparison, rational Bruhat
covering, relative Weyl group or Tits-system result.

The provenance is an internal composition of published proofs and the
published definition of parabolicity. Worker 1226 proposed the geometric
Borel route. The original Borel-connectedness theorem and its implemented
identity-component argument are documented in
[BorelContainingSubgroupConnected](../Absolute/BorelContainingSubgroupConnected.md),
which proves the connectedness clause of Milne, *Algebraic Groups* (2017),
Corollary 17.49. The arbitrary-field descent here is the surjective
continuous-image argument already implemented by
`connectedSpace_of_baseChange`; no rational Borel descent is asserted or
needed.
