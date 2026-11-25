# Unitary groups of Hermitian matrices

The module `Langlands.Group.Unitary.Basic` defines the unitary group of a sesquilinear form given
by its Gram matrix, Hermitian matrices, quadratic involutions, and the group `U(1)` of elements of
norm one with Hilbert's theorem 90.

## Content

Let `E` be a commutative `R`-algebra and `c : E →ₐ[R] E`.

- `UnitaryGroup.ofForm c J`, for `J : Matrix ι ι E`: the subgroup of `GL_ι(E)` of the `g` with
  `gᵀ J c(g) = J` (`UnitaryGroup.mem_ofForm_iff`), the automorphisms of the form
  `(x, y) ↦ xᵀ J c(y)`.
- `Matrix.IsHermitianFor c J` (namespace `Langlands`): `c (J j i) = J i j`. Nondegeneracy is a
  separate hypothesis `IsUnit J.det`. `UnitaryGroup.det_mem_normOneSubgroup`: for such `J`, the
  determinant of an element of `ofForm c J` has norm one.
- `IsQuadraticInvolution c ξ`: `E` is free over `R` with basis `1, ξ`, `ξ` is a unit and
  `c ξ = -ξ` (so `c` is the conjugation of the quadratic algebra `E`). Consequences:
  `exists_eq` (every element is `a + b ξ`), `algebraMap_injective`, `involutive` (`c ∘ c = id`),
  `finrank_eq_two`, `finite`; when `2` is invertible in `R`: `exists_of_fixed`,
  `exists_unit_of_fixed` (the elements fixed by `c` come from `R`), `map_eq_one_of_fixed` (a
  character of `Eˣ` trivial on `Rˣ` is trivial on the fixed units), `algebraMap_norm`
  (`N_{E/R}(z) = z c(z)`), `map_map_eq_inv` (a character trivial on norms satisfies
  `χ(c z) = χ(z)⁻¹`). Over fields: `isQuadraticExtension` (Mathlib's
  `Algebra.IsQuadraticExtension`), `isGalois` (when `2 ≠ 0`: `c` is a non-trivial automorphism, so
  the automorphism group has order the degree), and `exists_eq_mul_diagonal_mul`: an invertible
  Hermitian matrix `b` (`c(b)ᵀ = b`) is `a D c(a)ᵀ` with `a` invertible and `D` diagonal with
  entries in `Rˣ` (from `Sesquilinear.exists_congr_diagonal_of_hermitian`, the diagonal entries being
  fixed by `c`).
- `UnitaryGroup.hilbert90 c : Eˣ →* Eˣ`, `z ↦ z / c(z)`, `UnitaryGroup.normOneSubgroup c` (the
  `z` with `z c(z) = 1`, `mem_normOneSubgroup`), `hilbert90_apply_eq_iff`;
  `IsQuadraticInvolution.range_hilbert90_le_normOneSubgroup`, and Hilbert's theorem 90 for a
  quadratic algebra over a field with `2` invertible,
  `IsQuadraticInvolution.range_hilbert90_eq_normOneSubgroup` (for `u` of norm one, `u = z / c(z)`
  with `z = 1 + u`, or `z = ξ` when `u = -1`). `UnitaryGroup.descendToNormOne c χ hχ`: a character of
  `Eˣ` trivial on the elements fixed by `c` factors through `z ↦ z / c(z)`
  (`descendToNormOne_hilbert90`); with Hilbert 90 this makes it a character of `U(1)`.

The bridge from a quadratic involution to Mathlib's notions (`isQuadraticExtension`, `isGalois`)
is what the quadratic character `LocalClassField.normResidueSign F E` of
`Langlands/ClassFieldTheory/Local/QuadraticNormIndex.lean` needs.

The Library has unitary group schemes (`Langlands/Shimura/Unitary`,
`Langlands/GroupScheme/Quaternionic`); this file is about groups of points, for the theta
correspondence (`Langlands/Theta/DualPair/Unitary/`). Reference for unitary dual pairs: Mœglin–Vignéras–
Waldspurger, *Correspondances de Howe sur un corps p-adique*, LNM 1291 (1987), chapter 1, I: n° 1–2,
pp. 1–2 (ε-hermitian spaces and their unitary groups; hermitian spaces over a quadratic extension),
n° 17, pp. 10–11 (dual pairs), n° 19, pp. 13–14 (the reductive dual pairs of unitary groups), and
the list of irreducible dual pairs of `Sp(2n, F)`, p. 15. There the form lives on a right vector
space over a division algebra with involution and is linear in the second variable (n° 1, p. 1);
here it is `xᵀ J c(y)` over a commutative algebra, linear in the first.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`:
`src/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean`,
lines 142–320 (`UG`, `IsHerm`, `IsQuad` and its lemmas, `h90`, `normOne`, `tilde`, Hilbert 90,
`det_mem_normOne`) and lines 402–408 (`ResEtaPow.map_conj`);
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGLDiagonalCongruentHermitian.lean`
(whole); the bridges to `Algebra.IsQuadraticExtension` and `IsGalois` follow
`Proofs/DivisorProofs/MulMemRangeNorm.lean`, lines 38–41. The repository has no licence file; the
text is used with attribution, see
`licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespace `GlobalTheory.WeilM` → `Langlands`, `Langlands.UnitaryGroup`,
  `Langlands.IsQuadraticInvolution`.
- Renamed: `UG` → `UnitaryGroup.ofForm`, `IsQuad` → `IsQuadraticInvolution` (fields `unit`,
  `anti`, `basis` → `isUnit`, `map_eq_neg`, `exists_basis`), `IsQuad.invol` → `involutive` (stated
  as `Function.Involutive c`), `triv_fixed` → `map_eq_one_of_fixed`, `h90` →
  `UnitaryGroup.hilbert90`, `normOne` → `UnitaryGroup.normOneSubgroup`, `tilde` →
  `UnitaryGroup.descendToNormOne`, `tilde_norm_quotient` → `descendToNormOne_hilbert90`,
  `hilbertNinetyQuotientHom_eq_iff` → `hilbert90_apply_eq_iff`, `h90_range_eq_normOne_of_isQuad` →
  `range_hilbert90_eq_normOneSubgroup`, `det_mem_normOne` → `det_mem_normOneSubgroup`,
  `ResEtaPow.map_conj` → `IsQuadraticInvolution.map_map_eq_inv` (stated with only the hypothesis it
  uses: `χ` trivial on norms), `exists_gl_diagonal_hermitian` →
  `IsQuadraticInvolution.exists_eq_mul_diagonal_mul`.
- `IsHerm c J` (Hermitian and invertible) is split into `Matrix.IsHermitianFor c J` and
  `IsUnit J.det`.
- `IsTilde`, `isTilde_iff`, `IsTilde.unique` are not taken (a relational description of
  `descendToNormOne` with no use).
- `[CharZero F]` in `exists_gl_diagonal_hermitian` replaced by `[NeZero (2 : F)]`. Types in any
  universe.
- New: `UnitaryGroup.mem_ofForm_iff`, `finrank_eq_two`, `finite`, `isQuadraticExtension`,
  `isGalois`.

## Declarations

- `UnitaryGroup.ofForm`, `UnitaryGroup.mem_ofForm_iff`
- `Matrix.IsHermitianFor`
- `IsQuadraticInvolution` and `.exists_eq`, `.algebraMap_injective`, `.involutive`,
  `.finrank_eq_two`, `.finite`, `.range_hilbert90_le_normOneSubgroup`, `.exists_of_fixed`,
  `.exists_unit_of_fixed`, `.map_eq_one_of_fixed`, `.algebraMap_norm`, `.map_map_eq_inv`,
  `.range_hilbert90_eq_normOneSubgroup`, `.isQuadraticExtension`, `.isGalois`,
  `.exists_eq_mul_diagonal_mul`
- `UnitaryGroup.hilbert90`, `UnitaryGroup.normOneSubgroup`, `UnitaryGroup.descendToNormOne`,
  `UnitaryGroup.mem_normOneSubgroup`, `UnitaryGroup.hilbert90_apply_eq_iff`,
  `UnitaryGroup.descendToNormOne_hilbert90`, `UnitaryGroup.det_mem_normOneSubgroup`

All in the namespace `Langlands`.

## Dependencies

`Langlands.LinearAlgebra.HermitianDiagonalization`; Mathlib: `Analysis.Complex.Circle`,
`FieldTheory.Galois.Basic`, `LinearAlgebra.Matrix.GeneralLinearGroup.Defs`, `RingTheory.Norm.Basic`,
`Tactic.LinearCombination`.
