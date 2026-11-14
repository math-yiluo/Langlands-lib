# The whole-apartment fixer over an arbitrary field

Let `k` be a field, `G` a connected reductive group scheme over `k`, and
`i : S.toGrp ⟶ G` a maximal split torus with monomorphic underlying scheme map.
Assume `G` is affine over `k`. Let `ω : kˣ → ℝ` be any function and let
`D : KPApartmentData i ω` be supplied root-datum valuation apartment data. All
constructions use the original rational-point group, apartment and reduced
quotient of this datum, at arbitrary universe `u`.

`pointwiseFixer_apartment_le_centralizerPoints` proves

```text
D.pointwiseFixer (Set.range D.apartmentMap) ≤ centralizerPoints i.
```

Here the fixer acts on the original reduced quotient; it is not defined using
an assumed faithful apartment action. The right-hand side is the rational
centralizer of the actual split torus inclusion.
`wholeApartmentFixerToCentralizer` is the subgroup inclusion homomorphism
supplied by this containment. Its coercion theorem states that it preserves
each ambient rational point.

The result requires neither a local-field structure on `k` nor affine-root
system axioms for `D`. It is a supporting geometric comparison for the
unramified integral-model task. It constructs no integral model and asserts no
equality between the fixer and the whole centralizer.

## Ordered coordinates and their intersections

`exists_indivisiblePositiveRoot_eq_or_double_of_rankOne` uses the published
`rootRankOneFactorization` theorem to obtain actual opposite factor pairs for
every relative root of `i`. The published common-positive-multiple
classification then expresses every positive root as an indivisible positive
root or its double. The alternative in which that indivisible root is twice
the original root contradicts indivisibility.

`range_orderedIndivisiblePositiveRootGroupProduct_eq_iSup_of_rankOne` lists the
indivisible positive roots in any finite ordering covering them. It puts each
root and its potential double consecutively, gives nonroots the trivial group,
and uses the published height-collection theorem and filtration commutator
relations to identify the range of ordered multiplication with the generated
positive subgroup. The double-root filtration is contained in the original
root filtration, so each consecutive pair reduces to a single factor. This
works for both the depth-zero and strict chamber root groups.

The theorem `iInf_iSup_chamberRootGroup_eq_iSup_rootFixer_of_rankOne`, reused
from [GenericPositiveRootFixerCoordinates](GenericPositiveRootFixerCoordinates.md),
proves, for every
nonempty set `Ω` of apartment points and every cocharacter `ν`,

```text
⋂ x ∈ Ω, ⟨U_(b,x,0) : b is ν-positive⟩
  = ⟨U_(b,Ω,0) : b is ν-positive⟩.
```

The finite root set gives an injective finite enumeration of the indivisible
positive roots. Take ordered coordinates at one point of `Ω`. At each other
point, the preceding collection theorem supplies coordinates with the same
product. The published ordered-root-point injectivity theorem, supplied with
the same actual opposite factor pairs, identifies these coordinates. Hence
every coordinate belongs to its root fixer over all of `Ω`. The other
containment follows directly from the definition of a root fixer.

## Separation on a ray

`cocharacterRay x ν` is the set of points
`mk (t ⊗ ν) +ᵥ x`, for real `t ≥ 0`, in the reduced apartment.
`rootFixer_cocharacterRay_eq_bot` proves that the root fixer of this ray is
trivial whenever `⟨a, ν⟩ < 0`. Translation changes the value of a root element
by `t ⟨a, ν⟩`. A nonidentity root element has finite value by valuation axiom
V 1, so it cannot have nonnegative value for all `t ≥ 0`.

Intersecting positive coordinates over the opposite ray therefore gives the
trivial subgroup (`iInf_positiveRootGroups_oppositeRay_eq_bot`).
`eq_one_of_unipotent_fixes_oppositeRay` applies the published unipotent-fixer
coordinate theorem at every point of this ray. A point of the dynamic
unipotent subgroup for a generic cocharacter fixing that entire opposite ray
is consequently the identity.

## The normalizer and the complete fixer

`normalizerAffineEquiv_eq_one_of_fixes_positiveCone` proves an affine spanning
fact for the actual normalizer action. The translated positive cone at `x`
consists of `mk w +ᵥ x` with `b(w) ≥ 0` for each `ν`-positive root `b`. It
contains `x`. For any `w`, choose `t` to be the sum of `|b(w)|` over the finite
root set. A positive integral root-cocharacter pairing is at least one, so
both `t ⊗ ν` and `w + t ⊗ ν` belong to the positive cone. An affine action
fixing the cone fixes their difference in its linear action, and hence fixes
the whole apartment.

`translationAction_eq_one_iff_mem_centralizerPoints_of_isMaximalSplitTorus`
extends the existing normalizer-action kernel argument to these arbitrary-field
hypotheses. Trivial reduced linear action fixes every relative root. The
published restricted-character span theorem and faithfulness of the split
torus Weyl action imply centralizer membership. Conversely, centralizer
membership makes the original cocharacter action trivial, and therefore its
quotient action trivial. This gives
`mem_centralizerPoints_of_normalizerAffineEquiv_eq_one_of_isMaximalSplitTorus`.

For `mem_centralizerPoints_of_fixes_apartment`, choose a generic cocharacter
and decompose an element fixing the apartment image at one point using the
original quotient stabilizer relation and published sharp exchange:
`g = u * (v * n)`, with `u` positive unipotent, `v` negative unipotent and `n`
in the actual normalizer. The factor `u` fixes the translated positive cone.
Thus `v * n` fixes its image. The published unipotent-normalizer lemma implies
that `n` fixes the cone in the apartment itself. The preceding spanning
argument makes its affine action trivial.

Along the positive cocharacter ray, `u`, `g` and `n` now fix the original
quotient points, so `v` does too. Negative-unipotent separation on this ray
gives `v = 1`. Then `u` fixes the whole apartment image, and separation on its
opposite ray gives `u = 1`. Hence `g = n`, and the normalizer kernel comparison
places `g` in the centralizer.

## Provenance

This is an internal derivation from the published root-rank-one,
height-collection, ordered-root-injectivity, generic point-exchange,
positive-cone fixing and split-torus Weyl interfaces. The collection and
intersection proofs adapt the Library's `ChamberPositiveCollection` and
`PositiveRootFixerCoordinates` arguments, replacing their affine-root-system
premises by actual reductive rank-one factorization. The normalizer kernel
proof adapts the first two comparisons in `NormalizerApartmentActionKernel`,
whose proof uses only the arbitrary-field hypotheses retained here. The
whole-apartment comparison is derived through the implemented cone and ray
arguments above; no new assertion is attributed to external literature.
