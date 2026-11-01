# Cohomology vanishing for nontrivial translation-invariant line bundles

`Langlands.AbelianScheme.algClosedFieldTranslationInvariantCohomologyVanishing.{u}`
proves the published proposition
`Langlands.AbelianScheme.AlgClosedFieldTranslationInvariantCohomologyVanishingStatement.{u}`.
Its full type is exactly this proposition. For every algebraically closed
field `K : Type u`, every abelian scheme `A` over `Spec K` and every actual
line bundle `L` on `A`, translation invariance and nontriviality imply

```text
∀ n : ℕ, IsZero ((DerivedSections.relativeCohomology A.X.hom n).obj L.obj).
```

The result includes degree zero, every characteristic and dimension zero.
It uses the actual right-derived cohomology of structure-sheaf modules,
with no supplied cohomology data or additional geometric or compatibility
hypothesis. The statement pair and all of its imports are preserved.

## Published inputs

The proof imports the following proved results by their Lean names:

- `algClosedFieldTranslationInvariantH0Vanishing` in
  `TranslationInvariantH0VanishingProof` gives the degree-zero case from
  exactly translation invariance and nontriviality.
- The first component of
  `algClosedFieldTranslationInvariantPullbackIdentities` in
  `TranslationInvariantPullbackIdentitiesProof` identifies the actual
  coefficient module `m*L` with the external tensor product of `L` and `L`.
- `coherentFieldExternalTensorKunneth` in
  `CoherentFieldExternalTensorKunnethProof` identifies cohomology of that
  external tensor product with the direct sum of the tensor products
  `Hᵃ(A,L) ⊗[K] Hᵇ(A,L)` indexed by `a + b = n`.
- `DerivedSections.relativeCohomologyPullbackSplitRetractionStatement` in
  `CohomologyPullbackSplitRetractionProof` gives the retraction equation for
  the actual cohomology pullbacks and their prescribed coefficient
  identification, whenever the scheme morphisms form a split pair.

The geometric and cohomological inputs above are used as proved theorems;
the final result has no cube, Künneth, vanishing, pullback-law, ample,
projectivity, Picard or dual-existence premise.

## Implemented proof

The private structural lemma takes
`j = prod.lift (𝟙 A.X) 1 : A.X ⟶ A.X × A.X` and
`m = prod.fst * prod.snd : A.X × A.X ⟶ A.X` in the category over the base.
The morphism `1` is the constant group-identity morphism. Thus `j` is the
source's inclusion `(id,0)` in additive notation. Precomposition of the
product of morphisms, followed by the two product projection identities
and the group unit law, proves `j ≫ m = 𝟙 A.X`.

The private lemma `multiplicationPullbackMono` applies the published split
law to this equality. The actual pullback along `j`, followed by the
cohomology map of
`DerivedSections.relativeCohomologySplitCoefficientIso m j w`, is a
retraction of the actual pullback along `m`. These maps form a `SplitMono`,
which gives monicity. This lemma works over every commutative base ring
and for every actual module and natural degree.

The second private lemma carries out strong induction on `n`. The case
`n = 0` is the published degree-zero theorem. When `n ≠ 0`, for every pair
`(a,b)` with `a+b=n`, either `a<n` or `b<n`. Strong induction makes one of
the two cohomology modules zero. The corresponding tensor product is
therefore a subsingleton, as is their direct sum, so that direct sum is a
zero object of `ModuleCat K`.

The multiplication coefficient isomorphism is mapped through the actual
cohomology functor and composed with the published Künneth isomorphism.
It identifies `Hⁿ(A × A,m*L)` with this zero module. The identity of
`Hⁿ(A,L)` can now be cancelled against the monomorphism given by actual
pullback along `m`: both composites into the zero target agree. Its
identity is zero, hence `Hⁿ(A,L)` is a zero object. The final theorem
introduces precisely the binders of the published target and supplies the
proved multiplication-pullback monicity to this induction.

## Provenance and scope

This is the algebraically closed field specialization of Edixhoven,
van der Geer and Moonen, *Abelian Varieties*, Lemma (7.19), printed p.105 /
PDF p.109, in the registered manuscript
`edixhoven-vandergeer-moonen-abelian-varieties-draft` (SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`).
Its multiplication identity comes from the route of Lemma (7.16), printed
p.104 / PDF p.108. The statement Markdown documents the translation from
`φ_L = 0` to the ordinary translation-invariance hypothesis over an
algebraically closed field and the conventions for the actual Library
cohomology.

The implementation uses strong induction in place of the source's least
nonvanishing-degree contradiction. Its tensor-summand argument and
factorization through the zero product cohomology are the same route.
The structural split and categorical monicity adapters are internal
consequences of the published group-object and actual pullback laws.
No parent translation-difference lifting theorem or downstream dual
existence result is used. No positive-dimension hypothesis is needed;
the degree-zero theorem and the induction apply with the unchanged
binders in every dimension.

Worker 306 implemented the structural split, monicity consumer, induction
and exact theorem. Worker 100 contributed the cohomology-law interface
and dependency design used by the consumer. The separate geometric and
cohomological proofs are reused through the published imports above.
