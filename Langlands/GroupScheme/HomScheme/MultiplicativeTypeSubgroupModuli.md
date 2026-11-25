# Actual families of closed subgroups of multiplicative type

`MultiplicativeTypeSubgroupModuli.IsAdmissible F` means that the actual
subgroup functor `F` is represented by an actual homomorphism `j : K ⟶ G`
which is a closed immersion and whose source satisfies
`RelativeMultiplicativeType.IsMultiplicativeType`. The representation
condition includes monomorphy and equality of the ranges on every test
scheme over the base. In particular it includes nonreduced and nonaffine
tests.

The multiplicative-type predicate is the imported fppf-local
diagonalizability condition with finitely generated abelian character
groups. Torsion in the character group is allowed, so this interface
includes finite nonsmooth diagonalizable groups as well as tori and
nonsplit forms.

The module reuses `TorusSubgroupModuli.familyHom` and `evaluate`.
These two constructions and their composition and closedness lemmas
have no torus hypothesis: they pull back an actual inclusion, apply
`Descent.pullbackComparison` to identify the ambient group, and take its
all-test range. `IsUniversal j` asks that every admissible subgroup on
every base change be the evaluation of `j` at a unique parameter
morphism. Closedness and multiplicative type of the universal family
are separate hypotheses in the representability statement.

The three auxiliary lemmas construct admissible ranges, preserve
admissibility under arbitrary base change, and preserve it under
family evaluation. Their proofs use closed-immersion monomorphy,
the published subgroup base-change API, and base-change stability
of the relative multiplicative-type predicate.

This is a derived interface for the functor in SGA 3, Exposé XI,
Theorem 4.1, in the registered source
`sga3-exposes-xi-xii-xiv-gille-polo-2008`: `Expo11.pdf`,
PDF page 20, recomposed page 104, original page 157.
It generalizes the existing torus-only interface by changing the
admissibility condition. It defines the functor's intended universal
property; it does not assert representability.
