# Full fixed indices restrict to the published standard fixed indices

This derived comparison proves that the new full fixed-index construction
agrees with the existing standard construction through the prescribed actual
standard-to-full map. It preserves that map's explicit discrete-series
comparison premise and both standard-slice Borel compatibility hypotheses,
with no new global orbit-finiteness assumption.

## Provenance and hypotheses

The source setting is J.-L. Waldspurger (2003), printed p.321, definition of
`Theta^H` and VIII.1.3(i), specialized to the standard indices; the actual orbit
index and standard/full split-center comparison are the derived interfaces
imported from `RationalSemistandardStandardComparison`. Registered source
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

The context retains an arbitrary nonarchimedean local field, an affine locally
finite type connected reductive ambient group, a maximal split torus, a generic
cocharacter, independent representation universe `uV`, and the canonical
point topology. The two actual families supply their own split components,
normal center images, quotient measurable structures and Haar measures.

Before the discrete-series comparison premise, all three declarations require
these two instance families, for every standard root subset `I`:

- `BorelSpace` on
  `levi (standardIndex hG hi hnu I)` modulo the split-center image from
  `chosenLeviModel (standardIndex hG hi hnu I)` and `a` at that index, using
  the full family's supplied quotient measurable structure.
- `BorelSpace` on the same literal Levi modulo `rationalLeviSplitCenter I (b I)`,
  using the independently supplied old-standard quotient measurable structure
  `hMeas I`.

These are exactly the two standard-slice families required by the imported
comparison maps. They identify each supplied sigma algebra with the Borel
sigma algebra of its quotient topology. A Haar-measure instance alone does
not state that equality. No Borel compatibility is imposed on nonstandard
indices. This correction propagates the measure hypotheses of the imported
map to its fixed-index consumers; it does not prove a discrete-series
comparison or an analytic finiteness theorem.

The explicit premise
`RationalSemistandardStandardDiscreteSeriesComparison a ha mu hG hi hnu b hb eta`
compares discrete-series membership for the identical actual smooth-dual class
on the common literal standard Levi. The imported orbit equivalence preserves
that class and reindexes only its actual unitary character relation. This unit
does not prove the same-class split-component/measure comparison.

## Declarations and proofs

All names are in `Langlands.HarishChandraSchwartz`.

| Declaration | Exact result and dependencies | Status |
| --- | --- | --- |
| `rationalStandardFullIndex_mem_fixed_iff` | For every subgroup `H`, the actual mapped standard pair is in `rationalSemistandardThetaFixed a ha mu H` exactly when its old pair is in `rationalThetaFixed hG hi hnu b hb eta H`. | Conditional elementary comparison, using both displayed Borel families and the discrete-series comparison. |
| `rationalSemistandardThetaFixed_standard_preimage` | Pullback of the full fixed set by the imported `rationalStandardFullIndex` equals the existing standard fixed set. | Set-extensionality form of the membership equivalence, retaining the same Borel families. |
| `finite_rationalThetaFixed_of_full` | Finiteness of the full fixed set implies finiteness of the old standard fixed set. | Conditional transfer using the imported finite-fiber theorem and both Borel families. |

For the membership proof, unfold the two fixed sets as images of actual
discrete-series classes with nonzero induced fixed vectors. The imported
`rationalStandardFullDiscreteSeriesEquiv` and its inverse retain the same
smooth-dual class. They therefore preserve the class-level induced-fixed
predicate by definitional equality. The induced orbit equivalence is injective
and its quotient-constructor formula identifies the corresponding witnesses.
This gives both implications without an assumption that `H` lies inside a
compact picture; the proof compares existential fixed-orbit definitions, not
the independent arbitrary-level any-representative target.

Set extensionality proves the preimage equality. The finiteness corollary uses
`rationalStandardFullIndex_finite_fibers` and `Set.Finite.preimage'`. It assumes
no injectivity of standard parabolic presentations and no geometric finiteness
of the full index. It also does not strengthen the published standard analytic
results: both Borel families, the explicit comparison premise and the supplied
full-finiteness proof remain visible. No Fourier-family, smoothness,
invariant-carrier or covariance claim is made here.
