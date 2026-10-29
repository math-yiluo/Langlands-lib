# Comparison of universal smooth-family parameters

`Langlands.AbelianScheme.smoothFamilyUniversalComparison` proves the published
`Langlands.AbelianScheme.SmoothFamilyUniversalComparisonStatement.{u}`.
For an arbitrary base `S` and abelian scheme `A`, let `L` on `P` and `M` on
`Q` be universal for smooth-family algebraically trivial classes on
quasi-separated tests. The sole condition on the parameters is
`QuasiSeparatedSpace P.left`. The theorem gives exactly one isomorphism
`e : P ≅ Q` over `S` for which the actual rigidified pullback of `M` along
`e.hom` is isomorphic to `L`.

## Implemented proof

Since `P` is an allowed test, universality of `M` classifies the class of
`L` by a unique morphism `k : P ⟶ Q`. Write its class equation as `hk`.
The proof instantiates `RigidifiedLineBundle.classifyingMap_comp` with
`Langlands.SchemeModule.RigidifiedModule.pullbackCoherence`.
Together with `hk`, this identifies the class of `M` pulled back along
`g ≫ k` with the class of `L` pulled back along `g` for every morphism
`g : T ⟶ P`.

For every quasi-separated test `T`, postcomposition with `k` is bijective:

- For injectivity, two morphisms `g₁, g₂ : T ⟶ P` with equal composites
  with `k` yield equal pullback classes of `L` by the composition identity.
  The published `Langlands.AbelianScheme.smoothFamilyPullback` shows that
  the pullback along `g₁` satisfies the smooth-family predicate.
  Uniqueness in the universality of `L` gives `g₁ = g₂`.
- For surjectivity, given `g : T ⟶ Q`, the same published pullback theorem
  shows that the pullback class of `M` along `g` satisfies that predicate.
  Universality of `L` supplies `h : T ⟶ P` with this class. The composition
  identity shows that `h ≫ k` classifies the same class with respect to
  `M`. Uniqueness in the universality of `M` gives `h ≫ k = g`.

The published `Langlands.AlgebraicGeometry.quasiSeparatedTestIsoDetection`
then gives `IsIso k`, without a condition on `Q.left` or `S`. The desired
isomorphism is `asIso k`. `RigidifiedLineBundle.classifyingMap_eq_iff`
converts `hk` into existence of the required isomorphism of actual
rigidified bundles. For any other compatible parameter isomorphism, the
same equivalence gives the class equation for its underlying morphism. Uniqueness
of `k`, followed by `Iso.ext`, proves uniqueness of the parameter
isomorphism. No uniqueness of the bundle isomorphism is asserted.

## Provenance and scope

This is a derived internal uniqueness theorem for the existing Library
classification predicate, with no additional literature assertion.
Worker 858 authored the conditional prototype
`smoothFamilyUniversalComparison_of_pullback`. Worker 150 adapted that
argument by importing and applying the independently reviewed, published
`smoothFamilyPullback` theorem in place of the prototype's pullback
hypothesis. Both workers are coauthors of this proof.

The proof has exactly the closed published statement as its type in the
single universe `u`. It uses the existing actual rigidified pullback and
its canonical composition coherence. The base and second parameter are
arbitrary; no extra geometric, representability or existence condition is
introduced. The module constructs only the comparison and does not
construct a universal family or prove the downstream flatness or finite
presentation assemblies.
