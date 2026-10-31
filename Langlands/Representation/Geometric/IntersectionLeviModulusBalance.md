# Block-normalization balance of the moduli on the intersection Levi

Author: Worker 23.

This module proves a scalar identity among explicit positive moduli for p-adic
`GL_n`. Fix block shapes `B`, `C`, a minimal representative `w` of a double coset
`W_C \ W / W_B`, and refinements `S` of `B` and `R` of `C`. The refinements must
describe the two Levi intersections exactly:

* `hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S`, and
* `hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R`.

These are the Levi parts (`.2.1`) of `IsIntersectionRefinement`. No parabolic or
radical part is used.

Write `M`, `N` for the block-diagonal subgroups of `B` and `C`, `P` for the
standard parabolic of `B`, `V` for the unipotent radical of `C`, and `g` for the
permutation matrix of `w`. For `m` in the actual intersection `M ∩ g⁻¹ N g`, let
`m'` be its conjugate `g m g⁻¹` in `N ∩ g M g⁻¹`, given by
`General.intersectionEquiv`. Write `ε` for the actual Haar modulus character
`General.intersectionCorrectionModulus N M V P g⁻¹` of the correction subgroup
`V ∩ g P g⁻¹`, on `N ∩ g M g⁻¹`.

## Statements

`intersectionLeviNormalizationRatio` defines the complex-unit character on the
source product-Levi intersection given by the product of the source outer,
target outer and source inner positive half moduli, divided by the target
inner positive half modulus. All coordinates are the actual subgroup
inclusions, exact refinement relabelings and intersection-Levi conjugation.
The half-modulus identity below computes its intrinsic value as the target
correction-subgroup Haar character. This definition is by Worker 76; the
balance proofs are by Worker 23.

`Langlands.Geometric.intersectionLeviModulusBalance` states the following. Let
`x : B.Levi`, `y : C.Levi`, `s : refinedLevi B S` and `r : refinedLevi C R` be
coordinate elements. Suppose the embedded matrices of `x` and `s` are the matrix of
`m`, and those of `y` and `r` are the matrix of `m'`. Then, in `ℝ≥0ˣ`,

`T.leviModulus B x * T.leviModulus C y * T.refinedLeviModulus B S s =
  T.refinedLeviModulus C R r * ε m' ^ 2`.

The block moduli are the explicit determinant formulas `leviModulus` and
`refinedLeviModulus` of the supplied `TopologicalData`. `ε` is the Haar modulus
itself, not a formula.

`Langlands.Geometric.intersectionLeviModulusBalance_sourceLevi` gives the same
identity for `m : sourceLevi F.Carrier B C w`, using the published Library
coordinates:

* the source modulus is evaluated at `m.val`;
* the target modulus at `(intersectionLeviConjugation F.Carrier B C w m).val`;
* the refined moduli at `MulEquiv.subgroupCongr hS m` and at
  `MulEquiv.subgroupCongr hR (intersectionLeviConjugation F.Carrier B C w m)`;
* `ε` at any `j` in `N ∩ g M g⁻¹` whose matrix is the embedded target coordinate.

It packs `m` into the ambient intersection. It shows that `intersectionEquiv` of
that element equals `j` by `intersectionLeviConjugation_embedding`, and then applies
the first theorem.

`Langlands.Geometric.intersectionLeviHalfModulusBalance_sourceLevi` states the
positive-half form of the same identity in `ℂˣ`. It uses the same coordinates:

`T.leviHalfModulus B m.val * T.leviHalfModulus C m'.val *
  T.refinedLeviHalfModulus B S (subgroupCongr hS m) =
  T.refinedLeviHalfModulus C R (subgroupCongr hR m') * Jacquet.complexCharacter ε j`.

It applies `NNReal.sqrt` to the previous identity, using `sqrt (a * b) = sqrt a * sqrt b`
and `sqrt (ε²) = ε`. Then it casts through `ℝ` to `ℂ`, which matches the definitions
of the published half moduli.

## Proof

**Reduction to diagonal matrices.** The coordinate elements are determined by
their matrices, because `leviEmbedding` is injective. So both sides are values of
two `ℝ≥0ˣ`-valued characters `ψ₁` and `ψ₂` on `M ∩ g⁻¹ N g`. These characters are
built from the Library's coordinate homomorphisms (`leviEquiv`, `codRestrict` into
the refined Levis) and from `ε ∘ intersectionEquiv`. Their quotient is mapped into
`ℂˣ` with `Jacquet.complexCharacter`. The published
`intersectionLeviDiagonalCharacterTheorem` says that a complex-unit character on the
actual intersection that is trivial on its diagonal matrices is trivial. So it
suffices to prove `ψ₁ = ψ₂` on diagonal matrices. Value one in `ℂˣ` gives value one
in `ℝ≥0ˣ`, because the complex character is the real-coerced positive value.

**Diagonal values.** Let `m` have diagonal units `t`, and write `u a` for the
normalized absolute value of `t a`. Then:

* By `General.intersectionEquiv_diagonal`, `m'` is diagonal with units
  `t' = t ∘ w⁻¹`.
* `leviModulus_of_diagonal` computes `δ_D` of a diagonal element of any block
  shape `D`. The determinant of each block is the product of its diagonal entries,
  and the published `leviModulus_apply` formula `∏_{i<j} |det m_i|^{n_j} /
  |det m_j|^{n_i}` is regrouped. The result is the product of `u a / u b` over the
  coordinate pairs `(a, b)` with `blockIndex D a < blockIndex D b`.
* `refinedLeviModulus_of_diagonal` applies this formula to each inner block through
  `refinedLeviModulus_apply` and `prod_within_blocks`. It takes a function `g` on
  the standard coordinates whose order agrees with the inner block order of every
  refinement block. The result is the product of `u a / u b` over pairs in one
  outer block with `g a < g b`.
* `ε(m')` is given by the published `correctionSubgroupDiagonalHaar`, applied to
  `C`, `B` and `w⁻¹`. It is the product of `u' a / u' b` over the pairs with
  `C`-block of `a` smaller than that of `b`, and `B`-block of `w⁻¹ a` at most that
  of `w⁻¹ b`.

**Inner block order from the intersection equalities.**
`refinement_lt_iff_of_sourceLevi` proves the following. Suppose `w` is increasing
on each `B`-block and `sourceLevi B C w = refinedLevi B S`. Then two coordinates
of one `B`-block lie in increasing blocks of `S` exactly when their images under
`w` lie in increasing `C`-blocks. In its proof, `monotoneBlockShape` produces the
refinement described by the monotone `C`-block labels on each `B`-block, and
`standardIntersections_of_comparisons` identifies its refined Levi with
`sourceLevi`. Then `blockRefinement_eq_of_refinedLevi_eq` forces `S` to be that
refinement. Minimality of `w` supplies the monotonicity, for `w` on `B` and for
`w⁻¹` on `C`. The same lemma applies to `R`.

**Finite root count.** After reindexing all products by `w`
(`prod_pairs_reindex_iff`), the diagonal identity becomes a statement
about one index set `Fin n`, with `f = blockIndex B` and `g = blockIndex C ∘ w`.
Every product runs over `u a / u b` on pairs with the stated property:

`P(f<) · P(g<) · P(f= ∧ g<) = P(g= ∧ f<) · P(g< ∧ f≤)²`.

`modulus_balance_root_products` proves this. It first applies the published
`correction_root_products` identity, `P(f<) P(g<) = P(f< ∧ g≤) P(g< ∧ f≤)`. It
then checks the pointwise identity `P(f< ∧ g≤) P(f= ∧ g<) = P(g= ∧ f<) P(g< ∧ f≤)`
in all nine order cases of `(f a, f b)` and `(g a, g b)`.

## Provenance and scope

This identity and its proof are an internal derivation. Worker 76 requested it as a
supporting lemma for the parabolic-orbit Jacquet comparison. It is the bookkeeping
behind the normalization: the normalized Jacquet functor and normalized induction
along the orbit agree with the composite of the refined normalized functors up to
the squared Haar correction.

The source motivation is Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), section 6.4, printed pp.468–469 (PDF pp.29–30),
registered as `bernstein-zelevinsky-1977-induced-i`. That section proves that the
correction character `ε` of the geometric lemma is trivial. It reduces to a
maximal torus and compares root moduli: `ε² = mod_S · mod_{-S} = 1`. The
implementation follows the same strategy for `GL_n`: it reduces to diagonal
matrices and compares explicit root products. It proves the full balance among
the five moduli rather than the triviality of a single character. The Haar
modulus formula and the diagonal character determination are imported, proved
Library results. I read section 6.4 (PDF pp.29–30) and the statement of 2.12
(PDF p.9) when preparing this module.

Original file:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

This module proves only the scalar identities, in `ℝ≥0ˣ` and their positive halves
in `ℂˣ`. It states no nested Jacquet action and no comparison between the nested
and ambient Haar moduli.
