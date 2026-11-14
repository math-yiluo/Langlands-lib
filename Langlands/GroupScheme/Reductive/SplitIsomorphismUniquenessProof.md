# Unpinned uniqueness for split reductive isomorphisms

Worker 3483 (original proof) and Worker 561 (verification and submission).
This file documents the implemented proof of
`Langlands.GroupScheme.splitIsomorphismUniqueness`, whose exact type is the
proposition `Langlands.GroupScheme.SplitIsomorphismUniquenessStatement`.

The target is the isomorphism case of unpinned uniqueness in Milne,
*Algebraic Groups* (2017), Proposition 23.7, Theorem 23.25 and Remark 23.26;
its source comparison is documented in
[the statement](SplitIsomorphismUniquenessStatement.md).
The proof below is an internal deduction from the published actual
root-datum, pinning, root-scaling, quotient and descent interfaces. It does
not formalize general noncentral isogenies.

## Exact scope

Over an arbitrary field, let two actual isomorphisms of connected reductive
groups carry supplied split maximal tori to one another. Suppose their
restrictions induce the same pullback on every actual character of the
target torus. For any supplied actual adjoint quotient and actual fppf image
of that torus in it, a unique ground-field point of the image torus acts
after the first isomorphism to give the second.

The point is a rational point of the quotient torus itself. No lift to a
rational point of the original torus is assumed. The statement retains the
full scheme-theoretic centre, which may be nonsmooth, central torus factors,
empty root systems and equality on all test schemes. The source
reductivity and maximality hypotheses occur through the exact statement;
target reductivity and splitness follow from its supplied adjoint-image
data.

## Faithfulness of the adjoint inner action

The three lemmas in `IsAdjointQuotient` establish the required faithfulness:

- `point_eq_one_of_innerAction_trivial` considers an adjoint quotient point
  acting trivially after every restriction of its test scheme. It lifts the
  point locally through the fpqc quotient. After every further restriction,
  the lift commutes with every point of the original group, so the lift
  belongs to the full centre functor. Its quotient image is the identity.
  Equality descends along the covering morphism by the published local
  quotient-lift cancellation lemma.
- `point_eq_of_innerAction_eq` applies the first lemma to the quotient of
  two points whose natural inner actions agree. The action laws show that
  this quotient acts trivially.
- `innerAction_basePointIso_injective` evaluates equality of actual
  group-scheme automorphisms on every test scheme. A map from any test
  scheme to the base object is its structure morphism, so the resulting
  equality is exactly the hypothesis of the previous lemma.

These arguments use
[`Adjoint.Quotient`](../Adjoint/Quotient.md),
[`Adjoint.InnerAction`](../Adjoint/InnerAction.md) and
[`AutomorphicActionPointIso`](../AutomorphicActionPointIso.md).
No smoothness assertion for the centre is used.

## Factorization through the supplied torus image

For a split pinning on the supplied target torus,
`SplitPinning.exists_rootScalingTorusImageHom` factors the published
simple-root scaling homomorphism into the adjoint group through the exact
supplied image torus. The kernel of the simple-root projection maps
centrally into the original group by
`rootScalingProjection_kernel_central`. The kernel/centre identity
`IsAdjointSplitTorusImage.comp_eq_one_iff_mem_center` therefore shows that
the supplied map to the image torus kills this kernel.

The actual projection is fppf and is a morphism of affine schemes, hence
fpqc. `FpqcHomDescent.hom` descends the supplied torus map through it.
`FpqcHomDescent.fac`, the supplied quotient square and
`FpqcHomDescent.unique` identify the composition of this descended map
with the image-torus inclusion as `rootScalingAdjointHom`.

`SplitPinning.exists_torusImagePoint_of_inclusion_fixed` now treats any
automorphism fixing the pinned torus pointwise. The published
`exists_eq_rootScalingIso` writes it as a simple-root scaling. The
corresponding scaling point maps through the descended homomorphism to a
point of the supplied image torus.
`innerAction_basePointIso_rootScaling` identifies its actual inner action
with the given automorphism.

The inputs are
[`RootScalingTorus`](RootScalingTorus.md),
[`PinnedWeylInner`](PinnedWeylInner.md),
[`HomDescent`](../HomDescent.md) and
[`Adjoint.SplitTorus`](../Adjoint/SplitTorus.md).
Descent is used at the scheme level, so this step makes no rational-point
surjectivity assumption.

## Proof of the exact target

Actual characters separate homomorphisms into a split torus by
`IsSplitTorus.hom_ext_of_characters`. Thus the two torus restrictions agree.
The automorphism obtained by applying the inverse of the first group
isomorphism and then the second fixes the target torus pointwise.

`rootDatumExistence` supplies a finite reduced root datum on that exact
torus. `SplitPinning.ofRootDatum`, using `splitRootLieLine`, constructs a
pinning retaining that torus and inclusion definitionally. The preceding
factorization lemma produces the desired point of its supplied adjoint
image torus, and composition with the first isomorphism proves existence.

For uniqueness, cancel the first group isomorphism. The faithful adjoint
inner action then identifies the images of the two proposed torus points.
The supplied image-torus inclusion is a closed immersion and therefore a
monomorphism; cancelling it identifies the points themselves.

The additional inputs are
[`CharacterIsomorphism`](../Torus/CharacterIsomorphism.md),
[`RootDatumExistence`](RootDatumExistence.md),
[`PinningConstruction`](PinningConstruction.md) and
[`RootPinningFromSplitTorus`](RootPinningFromSplitTorus.md).
All supporting lemmas and the final theorem are proved in Lean with no new
axioms or unproved structural premises.
