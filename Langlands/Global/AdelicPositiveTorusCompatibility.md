# Adelic positive-torus compatibility from archimedean Levi intersections

Author: Worker 112. Markdown precision edits and submission: Worker 1517.

The selected theorem `adelicPositiveTorusCompatibility` has exactly the type
`Langlands.Global.AdelicSiegelFactors.AdelicPositiveTorusCompatibilityStatement`
in universe `u`. The final wrapper introduces its universal parameters and
applies `isPositiveTorusCompatible_of_leviCompatibleIwasawaCompacts`.

This internal proof development proves the Library's actual adelic
`IsPositiveTorusCompatible` condition from supplied archimedean
Levi-compatible Iwasawa compacts and containment of the archimedean projections
of the chosen adelic subgroup. It also specializes the implication to an
existing Siegel algebraic setup and its coordinate subgroups.

## Objects and hypotheses

The field `F : Type u` is an arbitrary number field. The ambient `G` is a
group scheme over `Spec F` whose structure morphism is affine. The commutative
group schemes `T₀` and `T` have actual group-scheme maps `j : T₀ ⟶ T` and
`i : T.toGrp ⟶ G`, and `ν` is a cocharacter of `T`. The standard parabolic
and Levi are the existing canonical representatives
`Standard.parabolicScheme i ν ∅` and `Standard.leviScheme i ν ∅`, with their
existing inclusions. The positive subgroup is
`PositiveRealTorus.intrinsicSubgroup F T₀`, and its ambient map is the
unchanged `positiveMap F G T i T₀ j`.

For the main implication, `T₀` is assumed split and
`standardLevi i ν ∅ = torusCentralizer i` is assumed as an equality of
subgroup functors on all test schemes. For each infinite place `v`, a
subgroup `Karch v` of the actual completion-point group is supplied with
`IsLeviCompatibleIwasawaCompact` for the canonical parabolic and Levi.
This predicate includes maximal compactness, local Iwasawa coverage,
the parabolic/Levi intersection equality, and maximal compactness of the
pullback to the Levi. Every infinite-place projection of each member of
the chosen adelic subgroup `K` is assumed to belong to `Karch v`.
No compactness or maximality of `K` itself is needed for this implication.

## Finite components and coefficient centrality

`PositiveRealTorus.atFinitePlace_full` proves that each finite-place
projection of a coordinate positive point `full F I T e x` is the
identity. Its proof applies the injective splitting coordinates at the
finite completion. `coordinates_affineMap` identifies these coordinates
with the finite projection of the scalar positive ideles, whose finite
components are one by construction.

`PositiveRealTorus.atFinitePlace_intrinsic` chooses a finite splitting from
`IsSplitTorus`, identifies its coordinate positive subgroup with the
intrinsic subgroup, and applies the preceding result.
`AdelicSiegelFactors.atFinitePlace_positiveMap` then uses
`atPlace_map` to prove that the actual ambient positive image has identity
finite components. These assertions require no nonzero split rank;
the splitting index may be empty. The last assertion does not require
affineness of `G`.

`commute_of_mem_standardLevi_image` is algebraic: over every commutative
`F`-algebra `A` in universe `u`, a point in the actual standard Levi image
commutes with every point mapped from `T₀(A)` through `j` and `i`, under
the stated centralizer equality. The proof uses
`Standard.isRepresentedBy_leviHom` to convert image membership to subgroup
functor membership, rewrites by the centralizer equality, and evaluates
the all-test commutation condition at the identity refinement. This
lemma keeps the affineness premise `[IsAffineHom G.X.hom]` on the ambient
group but needs only a field `F`, without the number-field hypothesis.

## Adelic compatibility

`isPositiveTorusCompatible_of_leviCompatibleIwasawaCompacts` proves

```text
∀ k ∈ K, k ∈ image(P(𝔸_F) → G(𝔸_F)) →
  ∀ a ∈ A_{T₀}, k * positiveMap(a) = positiveMap(a) * k.
```

This is precisely the existing `IsPositiveTorusCompatible` predicate.
The implemented proof compares the products at every place via
`ext_atPlace`. At a finite place the positive component is the identity.
At an infinite place, naturality of projection sends global parabolic
image membership to local parabolic image membership. The supplied
compact containment and
`IsLeviCompatibleIwasawaCompact.mem_levi` give local Levi membership.
`Standard.leviToParabolic_comp` identifies its ambient inclusion with the
canonical Levi inclusion, and the coefficient centrality lemma proves
commutation. No identification of an arbitrary number field with a
subfield of `ℝ` enters this proof.

`isPositiveTorusCompatible_of_setup_leviCompatibleIwasawaCompacts`
extracts the centralizer equality from an existing
`IsSiegelAlgebraicSetup`. The same setup contains a maximal split torus
`T₀` in an actual derived-subgroup witness, so it also supplies
`IsSplitTorus T₀.toGrp`. The theorem then applies the main implication.

`isPositiveTorusCompatible_coordinateSubgroup` assumes an existing
`IsSiegelAlgebraicSetup` and applies that setup theorem to the unchanged
`CoordinateCompactAssembly.coordinateSubgroup`, formed with the actual
place projections `atPlace F G v`, of any family `Kloc` of local
subgroups indexed by all places whose infinite-place members satisfy the
specified local predicate. Its projection-containment hypothesis follows
directly from the definition of the coordinate subgroup. It imposes no
condition on the finite-place members, since the positive factor has
identity finite components. Compactness, maximality or global coverage
of this coordinate subgroup must still be proved separately when needed.

## Provenance and retained obligations

The contribution is derived internally from the Library's actual adelic
points and local projections, intrinsic positive subgroup,
splitting-coordinate naturality, standard representability and
all-test centralizer. Its compact-intersection input is the existing
local Levi-compatible predicate. The proof route above is the implemented
Lean proof, with no external existence result introduced.

The algebraic setup, the local compacts and their Levi-compatible
properties remain hypotheses. This module constructs none of them and
proves no unconditional good Siegel reduction, global Iwasawa coverage,
Siegel coverage, finite-volume or unimodularity theorem. It does not
identify a maximal `F`-split centre with the greatest `ℚ`-split centre
after restriction of scalars. Those obligations of the host task remain.
