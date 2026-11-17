# The Picard groups of SLₙ and GLₙ vanish: proof

Author: Worker 896.

`Langlands.GroupScheme.LinearPicardTrivial.linearPicardTrivialStatement` proves
the published proposition `Langlands.GroupScheme.LinearPicardTrivialStatement.{u}`.
Its type is exactly that proposition, for every universe `u`, with no additional
arguments or hypotheses. It covers every field `k : Type u` and every finite index
type `n : Type` with decidable equality, the empty index type included.

The statement says that over a field `k`, every line bundle on the scheme
underlying `SpecialLinear.groupScheme n (CommRingCat.of k)`, and every line bundle
on the scheme underlying `GeneralLinear.groupScheme n (CommRingCat.of k)`, is
isomorphic in `Langlands.AlgebraicGeometry.Picard.LineBundle` to
`LineBundle.trivial`. The source is Milne, *Algebraic Groups* (2017),
Proposition 20.30, as recorded in the statement's Markdown.

## Proof route

The proof follows Milne's argument for `GLₙ`. For `SLₙ` it replaces the product
decomposition `GLₙ ≃ SLₙ × 𝔾ₘ` of Milne's 2.42 with a weaker fact: the coordinate
ring of `SLₙ` is a ring retract of the coordinate ring of `GLₙ`. No tensor
product decomposition is constructed. Everything is proved first for module
Picard groups `CommRing.Pic` of coordinate rings, and then transferred to line
bundles on the spectra.

### Picard groups of retracts

`subsingleton_pic_of_retract` takes ring homomorphisms `f : A →+* B` and
`g : B →+* A` with `g.comp f = RingHom.id A`, where `A` and `B` are commutative
rings in the same universe. If `CommRing.Pic B` is a subsingleton, then so is
`CommRing.Pic A`. The proof uses Mathlib's functoriality of Picard groups under
base change, `CommRing.Pic.mapRingHom`, with `mapRingHom_mapRingHom` and
`mapRingHom_id_apply`. Every class `M` equals
`mapRingHom g (mapRingHom f M)`, and `mapRingHom f M` lies in the subsingleton
`Pic B`. So any two classes of `Pic A` are equal.

### GLₙ

- `determinantPolynomial_ne_zero`: the determinant
  `GeneralLinear.determinantPolynomial n k` of the matrix of polynomial entry
  variables is nonzero. This is Mathlib's `Matrix.det_mvPolynomialX_ne_zero`.
- `isDomain_determinantLocalization` (an instance): the localization
  `GeneralLinear.DeterminantLocalization n k`, the polynomial ring
  `MvPolynomial (n × n) k` with that determinant inverted, is a domain. This is
  `IsLocalization.isDomain_localization`, since the powers of a nonzero element of
  a domain are nonzero divisors.
- `subsingleton_pic_determinantLocalization`: the Picard group of this localization
  is trivial. It is found by instance search, combining four Mathlib facts. A
  polynomial ring over a field is a unique factorization domain
  (`MvPolynomial.uniqueFactorizationMonoid`). A localization of a unique
  factorization monoid is one (the `Localization` instance in
  `Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization`). A unique
  factorization monoid is a GCD monoid (`IsGCDMonoid`). Finally, a domain with
  `IsGCDMonoid` has trivial Picard group (the instance in
  `Mathlib.RingTheory.PicardGroup`, Stacks 0BCH).
- `subsingleton_pic_generalLinear`: `CommRing.Pic (GeneralLinear.CoordinateRing n k)`
  is a subsingleton. The published `GeneralLinear.determinantLocalizationEquiv`
  identifies the coordinate ring with the determinant localization, and
  `Langlands.CommutativeAlgebra.subsingleton_pic_of_ringEquiv` transports Picard
  triviality along the inverse ring equivalence.

### SLₙ as a retract of GLₙ

This part is proved over an arbitrary commutative ring `R : Type u`.

- `restriction n R : GeneralLinear.CoordinateRing n R →ₐ[R] SpecialLinear.CoordinateRing n R`
  restricts functions from `GLₙ` to `SLₙ`. It is `GeneralLinear.classify` applied
  to the universal determinant-one matrix, viewed as an invertible matrix
  through `Matrix.SpecialLinearGroup.toGL`. `point_restriction` records that
  `GeneralLinear.point (restriction n R)` is this matrix.
- `inverseDeterminant n R` is the determinant of the inverse of the universal
  invertible matrix `GeneralLinear.universal n R`.
  `det_universal_mul_inverseDeterminant` shows that the universal determinant times
  `inverseDeterminant` is `1`. `restriction_inverseDeterminant` shows that
  `restriction` sends `inverseDeterminant` to `1`: entrywise, `restriction` sends
  the inverse universal matrix to the inverse of the universal determinant-one
  matrix, whose determinant is `1` (`Matrix.SpecialLinearGroup.det_coe`).
- For an index `i₀ : n`, `normalizedUniversal n R i₀` is the determinant-one matrix
  `X · diag(Pi.mulSingle i₀ (det X)⁻¹)` over the `GLₙ` coordinate ring, where `X`
  is the universal invertible matrix. So column `i₀` of `X` is scaled by
  `(det X)⁻¹`. Its determinant is `1` by `Matrix.det_mul`, `Matrix.det_diagonal`,
  `Fintype.prod_pi_mulSingle'` and the previous item. Milne's 2.42 isomorphism
  `SLₙ × 𝔾ₘ → GLₙ`, `(A, r) ↦ A · diag(r, 1, …, 1)`, has inverse
  `g ↦ (g · diag(det g⁻¹, 1, …, 1), det g)`. This matrix is the universal case of
  its `SLₙ` component, with column `i₀` in place of the first column.
- `restriction_comp_classify_normalizedUniversal` proves
  `(restriction n R).comp (SpecialLinear.classify (normalizedUniversal n R i₀)) = AlgHom.id`.
  By injectivity of `SpecialLinear.homEquiv`, it suffices to compare the
  determinant-one matrices classified by both sides. Entrywise, `restriction`
  sends column `b` of `X` to column `b` of the universal determinant-one matrix.
  It sends the diagonal factor to `1` in column `i₀`, by
  `restriction_inverseDeterminant`, and to `1` in every other column. Geometrically,
  `SLₙ → GLₙ → SLₙ` is the identity.
- `exists_restriction_section`: there is an `R`-algebra map `s` from the `SLₙ`
  coordinate ring to the `GLₙ` coordinate ring with `(restriction n R).comp s` the
  identity. For nonempty `n` choose `i₀` and take
  `SpecialLinear.classify (normalizedUniversal n R i₀)`. For empty `n` take
  `SpecialLinear.classify 1`. The required equality of determinant-one matrices
  then holds because a matrix with empty index type has no entries.

`subsingleton_pic_specialLinear` combines `exists_restriction_section` with
`subsingleton_pic_generalLinear` and `subsingleton_pic_of_retract`. It shows that
`CommRing.Pic (SpecialLinear.CoordinateRing n k)` is a subsingleton for every field
`k`.

### From rings to line bundles

`nonempty_iso_trivial_of_pic_trivial` takes `R : CommRingCat.{u}` with
`Subsingleton (CommRing.Pic R)` and a line bundle `L` on `Spec R`. It produces an
isomorphism `L ≅ LineBundle.trivial (Spec R)` in the full subcategory `LineBundle`.
The published
`Langlands.AlgebraicGeometry.Picard.nonempty_lineBundle_iso_structureSheaf_of_pic_trivial`
gives an isomorphism of module sheaves `L.obj ≅ SheafOfModules.unit`, and
`ObjectProperty.isoMk` lifts it to the full subcategory. The underlying object of
`LineBundle.trivial` is the structure sheaf.

### The closing theorem

After introducing `k`, `n` and their instances, `refine` splits the goal into the
two conjuncts; the statement's local `let` reduces definitionally. The underlying schemes of
`SpecialLinear.groupScheme n (CommRingCat.of k)` and
`GeneralLinear.groupScheme n (CommRingCat.of k)` are, by definition, the spectra
of `CommRingCat.of (SpecialLinear.CoordinateRing n k)` and
`CommRingCat.of (GeneralLinear.CoordinateRing n k)` (the published `groupScheme_left`
lemmas hold by `rfl`). `nonempty_iso_trivial_of_pic_trivial` is applied to these
rings, with the Picard triviality supplied by `subsingleton_pic_specialLinear` and
`subsingleton_pic_generalLinear`.

## Dependencies and scope

Project dependencies, imported by Lean module name:

- `Langlands.GroupScheme.LinearPicardTrivialStatement` (the target);
- `Langlands.GroupScheme.GeneralLinearLocalization`
  (`GeneralLinear.determinantLocalizationEquiv`);
- `Langlands.AlgebraicGeometry.Picard.AffineLineBundlePicard`
  (`nonempty_lineBundle_iso_structureSheaf_of_pic_trivial`, and through it
  `Langlands.CommutativeAlgebra.subsingleton_pic_of_ringEquiv`).

The only axioms used are `propext`, `Classical.choice` and `Quot.sound`. The
retract argument for `SLₙ` holds over every commutative ring. The field hypothesis
is used only for `GLₙ`, through the unique factorization property of polynomial
rings over a field. The proof establishes no tensor decomposition
`O(GLₙ) ≃ O(SLₙ) ⊗ O(𝔾ₘ)` and no statement about the group structure of the
Picard group.
