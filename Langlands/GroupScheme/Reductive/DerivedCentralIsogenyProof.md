# Central isogenies from the derived group and the maximal central torus

`Langlands.GroupScheme.reductiveDerivedCentralIsogeny` proves the unchanged
published `Langlands.GroupScheme.ReductiveDerivedCentralIsogenyStatement.{u}`.
It applies to every scheme base and reductive group scheme in every universe
`u`, with no additional hypotheses or retained structural premises.

The conclusion includes existence of a maximal central relative torus. For
every closed normal semisimple subgroup inclusion `d : D → G`, every supplied
fppf quotient `q : G → Q` by its range with torus target, and every maximal
central torus `z : Z → G`, it gives a central isogeny
`prodHom z d (hz.commute_values d) : Z ⊗ D → G`. For every supplied fppf
quotient `p : G → P` by the range of `z`, it also gives a central isogeny
`CartesianMonoidalCategory.lift q p : G → Q ⊗ P`. The theorem preserves the
statement's local maximality predicate and all its original quantifiers.

The implemented proof supplies the three proved inputs of
[`reductiveDerivedCentralIsogeny_of_structuralInputs`](DerivedCentralIsogenyStructuralReduction.md):

- [`reductiveRelativeCenter`](RelativeCenterProof.md) represents the full
  centre as a closed subgroup of relative multiplicative type, compatibly
  with arbitrary base change.
- [`relativeMultiplicativeTypeLargestSubtorus`](../Torus/RelativeLargestSubtorusProof.md)
  supplies the largest relative subtorus of that centre and its maximality
  after every base change.
- [`reductiveFibrewiseCentralIsogeny`](FibrewiseCentralIsogenyProof.md)
  proves the fibrewise central-isogeny criterion for a surjective
  homomorphism between reductive group schemes over an arbitrary base.

The imported structural reduction uses the first two inputs to construct
the maximal central torus. It proves multiplication is a central isogeny
on residue-field fibres, obtains surjectivity of the total multiplication,
and applies the third input to its full scheme-theoretic kernels. The
quotient-pairing reduction then gives the second central isogeny for the
actual supplied quotient maps.

This is an internal composition of those published results; it adds no
source assertion or modification to the target or its imports. It does not
assert existence of the represented quotients quantified over in the target.
The final proof is assembled from the structural reduction and its
supporting results.
