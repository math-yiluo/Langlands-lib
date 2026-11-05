# Topology of the actual tensor-base-change Weil comparison

This is derived infrastructure for the scalar-base-change step in Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), Example 4.2, printed pp. 9–10. On p. 10 Conrad first identifies
the base change of a Weil restriction to a completed base field with
restriction along the completed tensor algebra. He then decomposes that
restriction over the places above the original place and applies the
local-field point comparison. The present pair proves that the first
scheme identification preserves the independently constructed topologies
on points over a local topological value ring. It does not perform the
upper-place decomposition.

The cited original is registered as
`conrad-2011-weil-grothendieck-adelic-points`, with SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The arbitrary commutative-ring formulation below is a proved extension
of the source's field-valued base-change step, using the existing scheme
base-change topology theorem. It is not a separately stated theorem in
the paper.

## The general point base-change homeomorphism

Let `A`, `B`, and `S` be commutative rings in one arbitrary universe.
There are algebra structures `A → B`, `A → S`, and `B → S`, and their
composites agree through `IsScalarTower A B S`. Only `S` has a topology:
it is a topological ring, a local ring, and has open units with continuous
inversion, as specified by `IsOpenUnits S`. Locality and the open-unit
condition are separate hypotheses. No topology on `A` or `B`, or
continuity assertion about their algebra maps, is required.

For any actual relative scheme `X` over `Spec A`,
`schemePointBaseChangeHomeomorph` packages the existing
`ringPointBaseChangeEquiv A B S X` as

```text
X(S) ≃ₜ (X ×_{Spec A} Spec B)(S).
```

Here each point set is the actual relative scheme-morphism set
`RingPoint`, and each side has its own `schemePointTopology`. These
topologies are defined from affine-chart point topologies by the final
topology construction; neither topology is transported from the other.
The imported `schemeBaseChangeTopology_proof` proves that this exact
pullback-adjunction equivalence is a homeomorphism. The definition uses
`IsHomeomorph.homeomorph` to retain that equivalence's forward map, and
`schemePointBaseChangeHomeomorph_apply` records this by definitional
equality. There is no finite-type, separation, affine-cover finiteness,
or representability premise on `X`.

## The tensor Weil point spaces and their hypotheses

Let `A`, `B`, and `C` be commutative rings in the same arbitrary universe,
with `A`-algebra structures on `B` and `C`. Assume that `B` is finite
and projective as an `A`-module. Put `R = C ⊗[A] B`; its `C`-algebra
structure is the left tensor inclusion and its `B`-algebra structure is
the right tensor inclusion.

Let `Y` be an actual `B`-scheme, locally of finite type and separated
over `B`, such that every finite subset of `Y.left` lies in an affine
open subscheme. The latter is the geometric predicate
`HasFiniteAffineNeighborhoods Y.left`, not an assumed representing
property. Define the actual schemes

```text
G  = affineChartWeilRestriction A B Y,
YR = ringBaseChange B R Y,
G' = affineChartWeilRestriction C R YR.
```

The imported tensor-base-change construction derives the corresponding
geometry of `YR` from that of `Y`: locally finite type and separation
are stable under base change, and finite-set affine neighborhoods pull
back along the affine projection `YR → Y`. Finiteness and projectivity
of `R` over `C` follow by scalar extension. Thus the second glued Weil
scheme and its proved representing equivalence have no additional
geometric premise.

Only `C` has a topology in this part. It is a topological local ring
with `IsOpenUnits C`. There is no topology or locality assumption on
`R`; completed tensor algebras used in the source can be products of
several fields. No field, characteristic, separability, Hausdorffness,
completeness, or nontrivial-valuation hypothesis occurs here.

`affineChartWeilRestrictionTensorPointHomeomorph` constructs

```text
G(C) ≃ₜ G'(C),
```

where the left topology is `schemePointTopology A G C` and the right
topology is `schemePointTopology C G' C`. These are the original
independent point topologies, including for nonaffine `Y`.

## Implemented map and proof

The homeomorphism is the composite of two proved homeomorphisms:

1. `schemePointBaseChangeHomeomorph A C C G`, from `G(C)` to
   the `C`-points of the actual base change `G_C`;
2. `schemePointIsoHomeomorph C C e`, where
   `e = affineChartWeilRestrictionTensorBaseChangeIso A B C Y hY`
   is the canonical isomorphism `G_C ≅ G'` constructed by the natural
   all-test representing equivalences and Yoneda.

The second factor uses the existing functoriality theorem for
`schemePointTopology` applied to a scheme isomorphism and its inverse.
No new topology comparison is assumed.

The apply theorem fixes the forward map exactly:

```text
p ↦ ringPointBaseChangeEquiv A C C G p ≫ e.hom.
```

The theorem ending in `_comparison` further identifies this function
under the second Weil scheme's actual counit comparison. With
`T = ringTest C C`, its equation is

```text
comparison(C,R,YR,T)(homeomorph(p))
  = tensorBaseChangeComparison(A,B,C,Y,T)
      (ringPointBaseChangeEquiv A C C G p).
```

The left side is the actual base-change/counit morphism for `G'`.
The right side is the previously constructed tensor comparison, made
from the original counit, actual pullback pasting, and the tensor-spectrum
isomorphism. The proof applies the existing all-test counit identity
for `e`. These formulas identify the canonical function, as well as
proving the existence of a homeomorphism between the carriers.

## Actual projective-immersion specialization

`projectiveImmersionWeilRestrictionTensorPointHomeomorph` takes an actual
immersion `i : Y.left → ProjectiveSpace B n` and an equality saying that
its composite to `Spec B` is the given structure map of `Y`. The existing
projective-immersion adapters derive relative separation and finite-set
affine neighborhoods. Consequently these are not additional inputs to
the specialized homeomorphism. Local finite type is retained explicitly.
The specialization has its own apply and counit-comparison theorems,
with the same maps and the specialized canonical tensor scheme
isomorphism.

## Retained obligations

This pair supplies the topology compatibility of scalar base change
between the two actual Weil schemes. It does not identify the resulting
space with a product over upper places, put a topology on `Y(R)`, or
claim that a final affine-chart topology over a nonlocal product ring
is the required product topology. The actual finite-product Weil
decomposition, arithmetic completed-tensor identifications, compatible
local-field and valuation-ring factors, integral models, function-field
arithmetic instances, geometric preservation properties, and the global
adelic limit comparison remain separate obligations in the whole-paper
task. The source's full adelic conclusion is not asserted here.
