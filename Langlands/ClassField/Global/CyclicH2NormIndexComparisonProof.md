# Cyclic idele-class H² divides the actual norm index

`Langlands.ClassField.Global.cyclicH2NormIndexComparison.{u, v}` proves exactly
the published proposition
`Langlands.ClassField.Global.CyclicH2NormIndexComparison.{u, v}`, imported from
`Langlands.ClassField.Global.CyclicH2NormIndexComparisonStatement`.

Assuming `IdeleClassGaloisDescent.{u, v}` and
`IdeleClassNormGaloisProduct.{u, v}`, it proves, for every cyclic Galois
extension of number fields `E/F` with `F : Type u` and `E : Type v`,

```text
Nat.card (relativeIdeleClassCohomology F E 2)
  ∣ (ideleClassNorm (K := F) (L := E)).toMonoidHom.range.index.
```

The fields have independent universes, and the trivial extension is included.
The coefficient representation is the published
`relativeIdeleClassRepresentation F E`, the additive wrapper of the actual
`NumberField.IdeleClassGroup (𝓞 E) E` with arithmetic Galois action. The norm
and inclusion are the actual published idele-class maps.

## Implemented proof

Choose a generator `g` of `Gal(E/F)` and put
`A = relativeIdeleClassRepresentation F E`. The positive even degree-two
cyclic cohomology map
`Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2 even_two`
maps `ker(ρ(g) - 1)` onto `H²(Gal(E/F), C_E)`. Its surjectivity follows
from its definition as the composite of the inverse cycles isomorphism,
the homology projection, and the inverse cyclic cohomology isomorphism:
each is an epimorphism in the module category, and
`ModuleCat.epi_iff_surjective` supplies surjectivity.

Descent says that every included base idele class is Galois invariant.
Compose inclusion, the map to the additive wrapper of `ker(ρ(g) - 1)`,
and the cyclic cohomology map to construct a multiplicative homomorphism

```text
ψ : C_F → Multiplicative H²(Gal(E/F), C_E).
```

The map preserves multiplication because inclusion is a homomorphism and
the cohomology map is linear. To prove surjectivity of `ψ`, first lift a
degree-two class to `ker(ρ(g) - 1)`. Being fixed by the generator implies
being fixed by every Galois element, by
`Representation.mem_invariants_iff_of_forall_mem_zpowers`.
The image characterization in the descent hypothesis then lifts this
invariant class to `C_F`. Only the image characterization of descent is
used; its injectivity conjunct is not needed.

Next the actual norm range lies in `ker ψ`. For `y : C_E`, norm-product
compatibility rewrites the included norm of `y` as the product of its
Galois conjugates. In the additive coefficient representation this product
is the representation norm `∑ σ, ρ(σ)(Additive.ofMul y)`.
The criterion
`Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff`
therefore sends the included norm to zero.

Finally, `Subgroup.index_dvd_of_le` gives
`[C_F : ker ψ] ∣ [C_F : N(C_E)]`.
`Subgroup.index_ker` identifies the left index with the cardinality of
the range of `ψ`; surjectivity and `Subgroup.card_top` identify it with
`Nat.card H²`. The multiplicative wrapper has the same underlying type.

No finiteness of cohomology or of the norm quotient is assumed or concluded.
The subgroup-index argument applies with the `Nat.card` convention of zero
for infinite types. The theorem proves the stated implication; its two
antecedents remain hypotheses. It uses no Herbrand quotient formula,
H¹ vanishing, second inequality, or additional norm-index bound.

## Provenance and attribution

This is an internal derived comparison using the published arithmetic
interfaces and Mathlib's cyclic cohomology quotient and subgroup-index
theorems. It is not presented as a verbatim result from the literature.
The supporting Mathlib files are
`Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic`,
`Mathlib.RepresentationTheory.Invariants`, and `Mathlib.GroupTheory.Index`
at the project's pinned revision
`5ed2965256430c3649e86755f9576b54eca72435`.

Worker 392 extracted and adapted the proof to the exact published statement.
Worker 220 is a coauthor for the reused proof code and argument from
`Langlands.ClassField.Global.H1VanishingProof.card_H2_dvd_normIndex`
in revision 4 of draft task `16fe0104-64f0-48b9-9587-54db9de4c178`
(revision hash
`4a208eef3a53e6cf12a7c029a41f505b44c0b89598d6b48078862769c23430b8`).
That draft supplied source code and provenance; it is not an imported
dependency or accepted proof evidence. This module imports only the
published target statement and Mathlib's finite cyclic cohomology module.
