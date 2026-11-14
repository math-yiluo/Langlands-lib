# The canonical anticommutation relation on `H*(A, 𝒪)`

Module `Langlands.AbelianScheme.CanonicalCAR`, namespace `Langlands.AbelianScheme`.

## Purpose

Let `K : Type u` be a field and `A : AbelianScheme (Spec (CommRingCat.of K))`. This module proves
that the actual creation and contraction operators on structure-sheaf cohomology satisfy the
anticommutation relation in all positive degrees. With `CanonicalCARData`, this reduces
`FieldH2ExteriorCoproductComparisonStatement` to `FieldStructureSheafH1DimensionStatement`.

Notation:

- `Hⁿ(X) = structureCohomology X n`;
- `P = A.X ⨯ A.X`, `p₁ = prod.fst`, `p₂ = prod.snd`, and `m = p₁ * p₂` (the multiplication);
- `f^* = pullStructure A f n`, the actual structure-sheaf pullback.

The operators, all from `CanonicalCreationContraction` and its extensions, are:

- `creation A n w : Hⁿ(A) →ₗ[K] Hⁿ⁺¹(A)` for `w ∈ H¹(A)`. This is `AllSeq.creationCanonical` on the
  fixed affine cover `cover A`.
- `creationProd A n` (from `CanonicalLeftAxisSlant`) and `productCreation A n` (from
  `CanonicalSlantRightCreation`). These are the same creation operator on `P`, namely
  `AllSeq.creationCanonical` on `mixedCover A`.
- `slant A ell n : Hⁿ⁺¹(P) →ₗ[K] Hⁿ(A)` for `ell : H¹(A) →ₗ[K] K`. This is the slant by `ell` in the
  first factor.
- `contraction A ell n = slant A ell n ∘ m^*`, a map `Hⁿ⁺¹(A) →ₗ[K] Hⁿ(A)`.

## Multiplication pullback and creation

`pullStructure_mul_creation A n w e`: for `w ∈ H¹(A)` and `e ∈ Hⁿ⁺¹(A)`,
`m^*(creation A (n+1) w e) = creationProd A (n+1) (m^* w) (m^* e)` in `Hⁿ⁺²(P)`.

Proof. The cover `productCover A` of `P` (from `CanonicalH1Primitive`) has, for each index `j`,
`productCover A j ≤ m⁻¹(cover A (Prod.snd j))` (`productCover_le_mul`). So
`AllSeq.pull_creationCanonical`, applied to `m`, `U = cover A`, `V = productCover A` and
`α = Prod.snd`, gives
`m^*(creation A (n+1) w e) = creation on productCover A of (m^* w, m^* e)`. Since
`productCover A j ≤ mixedCover A j.1` (`productCover_le_mixedCover`),
`AllSeq.creationCanonical_refine` with `β = Prod.fst` identifies creation on `productCover A`
with creation on `mixedCover A`, which is `creationProd A (n+1)`. Both covers are finite and
affine and cover `P`, and `P` is separated over `K`.

## The anticommutation relation

`contraction_creation_add_creation_contraction A ell w n e`: for `ell : H¹(A) →ₗ[K] K`,
`w ∈ H¹(A)`, `n : ℕ` and `e ∈ Hⁿ⁺¹(A)`,

`contraction A ell (n+1) (creation A (n+1) w e) + creation A n w (contraction A ell n e) = ell w • e`.

Proof. Unfold `contraction` as `slant ∘ m^*` and write `e' = m^* e ∈ Hⁿ⁺¹(P)`.

1. By `pullStructure_mul_creation`, the first term is `slant A ell (n+1) (creationProd A (n+1) (m^* w) e')`.
2. Primitivity (`pullStructure_mul`) gives `m^* w = p₁^* w + p₂^* w`. Since creation and slant are
   linear, the first term splits into two summands.
3. The left-axis formula `slant_creationProd_pull_fst` gives
   `slant A ell (n+1) (creationProd A (n+1) (p₁^* w) e') = ell w • (leftAxis A)^* e'`. Here
   `(leftAxis A)^* (m^* e) = e` by `unitCohomologyPullback_leftAxis_pullStructure_mul` (from
   `CanonicalCARData`). So this summand is `ell w • e`.
4. The right-axis formula `slant_creation_right` gives
   `slant A ell (n+1) (productCreation A (n+1) (p₂^* w) e') = -creation A n w (slant A ell n e')`.
   This is `-creation A n w (contraction A ell n e)`. Here `creationProd` and `productCreation` are
   the same term, which `change` makes visible.
5. Adding `creation A n w (contraction A ell n e)` leaves `ell w • e` (`abel`).

The relation holds for every field, in every characteristic, and for every `n ≥ 0`, that is, on
every `Hⁿ⁺¹(A)`.

## The canonical datum and the target from the `H¹` dimension

- `canonicalCARData A : CARData.{u, 0} A` is a definition. It is `CARData.ofBasis` (from
  `CanonicalCARData`) applied to the basis `Module.finBasis K H¹(A)` and to
  `contraction_creation_add_creation_contraction A`. Its operators are
  `c i n = creation A n (b i)` and `d i n = contraction A (b.coord i) n` for that basis `b`,
  indexed by `Fin (finrank K H¹(A))`.
- `fieldH2ExteriorCoproductComparison_of_H1Dimension hH1` proves
  `FieldH2ExteriorCoproductComparisonStatement.{u}` from
  `hH1 : FieldStructureSheafH1DimensionStatement.{u}`. It applies
  `fieldH2ExteriorCoproductComparison_of_H1Dimension_of_CARData` (from `DegreeTwoComparisonFinal`),
  with index universe `0`, to `hH1` and to `canonicalCARData A` for every field and abelian
  scheme. The hypothesis `hH1` is used only for the vanishing of `Hⁿ(A)` above degree `dim H¹(A)` (see
`DegreeTwoComparisonFinal`). This module does not prove `FieldStructureSheafH1DimensionStatement`
  (Task 6458), so the target is proved here only conditionally on it.

## Provenance and independence

This is internal derived content. The relation has the form of the identity
`ι_ell (w ∧ e) + w ∧ ι_ell e = ell(w) e` in an exterior algebra. Its proof here combines the
project's actual-cohomology interfaces: creation naturality and refinement
(`AllSeqCreationNaturality`), primitivity of `H¹` (`CanonicalH1Primitive`), the left-axis slant
formula (`CanonicalLeftAxisSlant`), the right-axis slant formula (`CanonicalSlantRightCreation`) and
the section property of the left axis (`CanonicalCARData`). None of these uses the excluded Picard
or dual-geometry statements, or a proof of `FieldH2PrimitiveInjectivityStatement`.
