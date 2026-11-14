# Transferring a central product isogeny to the quotient pairing

This module is an internal reduction for Task 6385, the central isogenies
attached to a maximal central torus and a derived subgroup. It is derived from
the Library's represented quotient squares, categorical products and faithfully flat
descent; it is not a transcription of a separate external result.

`QuotientPairingTransferStatement` has the following meaning, in every universe
and over every base scheme `S`. Let `a : A ⟶ G` and `b : B ⟶ G` be group scheme
homomorphisms whose underlying morphisms in `Over S` are monomorphisms. Assume
`a` is central and the values of `a` and `b` commute on every test scheme.
Let `q : G ⟶ Q` and `p : G ⟶ P` be fppf quotient maps with full
scheme-theoretic kernels equal, as subgroup functors on all tests, to the
ranges of `b` and `a`, respectively. If multiplication
`prodHom a b hc : A ⊗ B ⟶ G` is a central isogeny, then the pairing
`lift q p : G ⟶ Q ⊗ P` is a central isogeny.

The fppf quotient predicate here is the published
`RelativeRoot.IsFppfQuotient`: flatness, surjectivity, local finite
presentation and the exact all-test kernel equality. A central isogeny means finite, flat,
surjective and locally of finite presentation, with central full
scheme-theoretic kernel, as in `CentralIsogeny.Basic`. No reductivity,
smoothness, torus, field or reduced-kernel assumption occurs in this reduction.

The module includes the proved helper
`isCentralIsogeny_quotientPairing_of_prodHom` and its universally quantified
wrapper `quotientPairingTransfer`. These prove this internal reduction; the
module does not prove the existence of the central factor or the multiplication
isogeny required by the original reductive target.

The proof proceeds as follows.

1. `prodHom_hom_eq_quotientCellMultiplication` identifies the pointwise
   `prodHom` construction with the multiplication map from `QuotientCell`.
   Because `b` represents the exact kernel of `q`,
   `QuotientCell.multiplication_isPullback` identifies multiplication with the
   pullback of `a ≫ q` along `q`. The helper
   `finiteFppf_restriction_of_prodHom` descends finiteness, flatness,
   surjectivity and local finite presentation along this fppf cover. The
   Mathlib bridge in `Morphisms.FlatDescent` deduces fppf descent from fpqc
   descent and Zariski locality on the target for each of these properties.
2. `prodHom_swap` identifies reversed multiplication with multiplication
   precomposed by the product symmetry. Isomorphism invariance of central
   isogenies gives the same four properties for `b ≫ p`, by the preceding
   argument with the factors reversed.
3. `quotientPairing_isPullback` proves that the square with top multiplication,
   left `id_A × (b ≫ p)`, right `lift q p`, and bottom
   `(a ≫ q) × id_P` is cartesian in `Over S`. Its composite with the first
   projections is the quotient square from step 1. The lower square is the
   product pullback square. The upper square commutes because `p` kills every
   point in the range of `a`; cancellation of the lower pullback square then
   gives the claimed square.
4. The left and bottom maps in this square are base changes of the
   restrictions from steps 1 and 2. The bottom map is a finite flat surjective
   cover, hence fpqc. Mapping the square to schemes and descending along its
   bottom map gives all four morphism properties for `lift q p`.
5. A point killed by the pairing is killed by `p`, by projection to the
   second factor. The exact kernel equality for `p` puts it in the range of
   `a`, so it is central. The all-test criterion
   `isCentral_kernelι_iff` gives centrality of the full kernel.

The argument uses the published fpqc descent instances in
`Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent` and Mathlib's
fpqc-to-fppf descent bridge. No quasi-compactness assumption on either quotient
map is needed. The private
product-square helpers are proved directly from the product universal
property. Throughout, quotient surjectivity is scheme-morphism surjectivity;
the proof does not require surjectivity on points of an unchanged test scheme.
