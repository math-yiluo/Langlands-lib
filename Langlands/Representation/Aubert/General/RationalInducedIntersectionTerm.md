# Induced rational geometric terms and source alternating terms

This internal specialization combines `InducedIntersectionTerm`,
`RationalGeometricTermComparison` and actual rational normalized induction
stages. It retains the actual standard rational-point family, canonical
`pointTopology`, independent universes `u` and `v`, every pair of standard
subsets, every minimum point Weyl representative, and every normalizer lift.
Carriers have universe `max (u + 1) v` and K0 retains all actual short exact
sequence relations.

`pointInducedGeometricTermK0` applies ambient normalized induction from the
coarse target Levi to the complete actual `pointGeometricTermK0`. Ambient
exactness is derived by `standardParabolicFiniteLength`. The source and target
restricted preservation premises are the literal ones from the rational
induction target; no preservation premise for the geometric factor is added.

`pointInducedGeometricTermK0_eq` identifies this whole map with
`inducedLeviAlternatingTerm` at the literal source index
`intersectionLeviIndex pointCs I J w : Finset J`. Its target fine index is
`intersectionLeviIndex pointCs J I w⁻¹ : Finset I`, with no change of signs or
inside-Levi labels. The theorem assumes the exact fine-Levi induced Weyl
equality with inverse conjugation by the supplied normalizer lift. This is an
equality of full K0 maps, not an assumed representation isomorphism.

The proof rewrites the geometric map with
`pointGeometricTermK0_eq_standard` and applies
`inducedStandardIntersectionTermK0_eq`. Both stages isomorphisms are supplied by
`standardInductionStagesIso`, which derives its Haar-modulus identity. The
source family exactness and target induction exactness are supplied by
`standardLeviParabolicFiniteLength`. Fine-Levi inclusions and conjugation
membership are derived by the rational twisted-intersection adapters. The
generic proof applies target stages, the Weyl equality, and reversed source
stages. Thus no induction stages or modulus equality is an extra hypothesis
of this rational reduction.

The provenance is internal assembly and specialization of the named
constructions. The scheme Coxeter system, its all-test standard Levi and source
twisted-intersection identities, point normalizer and centralizer comparisons,
and the fine-Levi induced Weyl equality remain explicit inputs. This does not
construct these inputs from the weaker premises of
`RationalInductionCompatibilityStatement`, prove geometric expansion, or prove
that final proposition. No final-target premise or target file is changed.
The implemented assembly invokes no classification, character-independence,
adjointness, geometric-lemma or cuspidal-support theorem; a later proof of its
Weyl or structural inputs must record its own dependencies.
