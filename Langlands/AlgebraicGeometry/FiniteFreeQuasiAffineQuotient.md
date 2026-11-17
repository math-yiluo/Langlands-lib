# Quasi-affine quotients of finite free actions

This internal construction extends the published affine finite free action quotient.
Let `G : Type u` be a finite group and `X : Scheme u` a quasi-affine scheme. An action
`A : FiniteFreeSchemeAction G X` uses the composition convention
`act g ≫ act h = act (g * h)` and is free on points valued in every nonempty scheme.

`quasiAffineQuotient A` chooses an `EffectiveQuotient` whose scheme is quasi-affine.
The quotient map is finite, étale, and surjective. The two action projections from
the coproduct of the graphs form its kernel pair on all scheme tests. The map is
also their categorical coequalizer in schemes. Invariant morphisms to any scheme
descend through `EffectiveQuotient.desc`, and `map_desc` and `hom_ext` express the
factorization and its uniqueness.

The implemented proof has the following steps.

1. The action projections are proper finite coproducts of isomorphisms and locally
   quasi-finite, hence finite. This step does not require affineness of `X`.
2. A finite set in a quasi-affine scheme has an affine principal neighborhood, by
   the published `OrbitSaturatedAffineOpen` construction. Taking the product of all
   translates of its defining function gives an invariant function. Its principal
   open contains the original finite set and is affine, since it is a principal
   open inside the first affine neighborhood.
3. In particular every action class has an affine neighborhood. The published
   finite locally free equivalence-relation quotient theorem constructs an effective
   scheme quotient and its coequalizer. Étaleness of its projection descends from an
   action projection along the finite faithfully flat quotient map.
4. Invariant global functions descend using the coequalizer and their interpretation
   as maps to the affine line. For each quotient point, the function from step 2
   therefore descends to a principal open whose preimage is affine. The auxiliary
   `FiniteLocallyFreeQuotient.isAffine_of_finite_flat_surjective` shows that this
   principal open is affine: it compares the published affine quotient of the
   restricted map's kernel pair with the restricted map's given target using
   coequalizer uniqueness. The hypotheses here include finite presentation,
   flatness, and surjectivity.
5. The quotient is quasi-compact as the continuous surjective image of `X`.
   Its covering by affine principal opens of global functions then proves
   quasi-affineness.

The provenance is derived from the imported Library constructions and Mathlib;
this module introduces no independent literature translation. It supplies the
finite free-action quotient prerequisite, without constructing a normalizer
orbit map or asserting the full multiplicative-type quotient statement.
