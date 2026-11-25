# The quasi-split unitary group `U(ν, ν)`

The module `Langlands.Group.Unitary.Hyperbolic` defines the hyperbolic skew-Hermitian form on
`E^{ν ⊕ ν}` (its Gram matrix `H = -J` satisfies `c(H)ᵀ = -H`), its unitary group `U(ν, ν)`, and the
elements and subgroups of `U(ν, ν)` that the construction of the Weil representation uses: the
Siegel parabolic subgroup with its Levi and unipotent elements, the Weyl element, and the big cell.

## Content

Let `E` be a commutative `R`-algebra with `c : E →ₐ[R] E`.

- `UnitaryGroup.hyperbolicForm ν E = -Matrix.J ν E`, that is `[[0, 1], [-1, 0]]`
  (`hyperbolicForm_eq_fromBlocks`, `hyperbolicForm_eq_neg_J`; Mathlib's
  `Matrix.J ν E = [[0, -1], [1, 0]]`). It squares to `-1` (`hyperbolicForm_mul_self`) and is
  antisymmetric (`transpose_hyperbolicForm`). Its unitary group
  `ofForm c (hyperbolicForm ν E)` is `U(ν, ν)`; membership can be read as `g J c(g)ᵀ = J`
  (`mem_ofForm_hyperbolicForm_iff`), and the inverse is `g⁻¹ = -J c(g)ᵀ J` (`val_inv`).
- `siegelLevi c hc a = diag(a, c(a⁻¹)ᵀ)` for `a ∈ GL_ν(E)` and `c` involutive (`siegelLevi_val`);
  `siegelUnipotent c b hb = [[1, b], [0, 1]]` for `b` with `c(b)ᵀ = b` (`siegelUnipotent_val`);
  `weylElement c ν = hyperbolicForm ν E = -J`, the matrix `[[0, 1], [-1, 0]]` (`weylElement_val`).
- `siegelParabolic c ν`: the subgroup of the `g` with vanishing lower left block
  (`mem_siegelParabolic`), containing the Levi and unipotent elements (`siegelLevi_mem`,
  `siegelUnipotent_mem`). `exists_eq_siegelLevi_mul_siegelUnipotent`: an element
  `p = [[A, B], [0, D]]` of the Siegel parabolic satisfies `A c(D)ᵀ = 1` and
  `A c(B)ᵀ = B c(A)ᵀ`, and `p = siegelLevi A · siegelUnipotent (c(D)ᵀ B)`.
- `IsInBigCell c g`: `g ∈ P w P` for `P` the Siegel parabolic and `w` the Weyl element; it is
  studied in `Langlands/Group/Unitary/BigCell.lean`.

The sign convention: the form is `-J`, the Gram matrix of `((x, y), (x', y')) ↦ x y' - y x'`. The
Weil representation of `U(ν, ν)` (`Langlands/Theta/DualPair/Unitary/`) acts on `M_{α×2ν}(E)` by right
multiplication and uses this convention throughout. Reference: Kudla, *Splitting metaplectic covers
of dual reductive pairs*, Israel J. Math. 87 (1994), 361–401, Introduction, (0.6)–(0.7), p. 364 (the
form `⟨(x₁, y₁), (x₂, y₂)⟩ = x₁ ᵗy₂^τ − ε y₁ ᵗx₂^τ` on row vectors, with `G` acting on the right; the
form here is the case `ε = 1`), and §1.2, (1.11)–(1.12), p. 370 (Bruhat cells `P τ_j P`, `n(p)`, `τ`).

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`, under
`src/Development/AbelianVarietyTheory/`: `PublishedTheorems/TwistedTraceFormula/KudlaSplittingSplitUnitary.lean`,
lines 15–74 (`stdJ`, `stdJ_mul_stdJ`, `mem_UG_iff`, `levi`, `levi_val`);
`Definitions/Divisors/UnipVal.lean`, lines 55–110 (`weyl`, `weyl_val`, `unip`, `unip_val`, `mat`,
`mat_inv`, `sieg`, `mem_sieg`, `InCell`); `Proofs/DivisorProofs/SplitUnitarySiegelParabolicBlockRelations.lean`
(whole). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespaces `GlobalTheory.SplitUnitary`, `GlobalTheory.KSp` → `Langlands.UnitaryGroup`.
- Renamed: `stdJ ν E` → `hyperbolicForm ν E`, defined as `-Matrix.J ν E` (the source's
  `fromBlocks 0 1 (-1) 0` is `hyperbolicForm_eq_fromBlocks`); `stdJ_mul_stdJ` →
  `hyperbolicForm_mul_self`; `mem_UG_iff` → `mem_ofForm_hyperbolicForm_iff`; `levi` → `siegelLevi`;
  `weyl` → `weylElement`; `unip` → `siegelUnipotent`; `mat_inv` → `val_inv`; `sieg` →
  `siegelParabolic`; `mem_sieg` → `mem_siegelParabolic`; `InCell` → `IsInBigCell`; `sieg_blocks` →
  `exists_eq_siegelLevi_mul_siegelUnipotent`.
- The abbreviation `KSp.mat` is replaced by the coercion `((g : GL (ν ⊕ ν) E) : Matrix _ _ E)`.
- The involutivity hypothesis `∀ z, c (c z) = z` is written `Function.Involutive c`. `E` is a
  commutative algebra over a commutative ring (the source: fields), and `[CharZero F]` and the
  quadratic involution of `sieg_blocks` are dropped (unused). Types in any universe.
- New: `transpose_hyperbolicForm`, `hyperbolicForm_eq_neg_J`, `siegelLevi_mem`,
  `siegelUnipotent_mem`.

## Declarations

- `UnitaryGroup.hyperbolicForm`, `hyperbolicForm_eq_fromBlocks`, `hyperbolicForm_eq_neg_J`,
  `hyperbolicForm_mul_self`, `transpose_hyperbolicForm`, `mem_ofForm_hyperbolicForm_iff`, `val_inv`
- `UnitaryGroup.siegelLevi`, `siegelLevi_val`, `UnitaryGroup.weylElement`, `weylElement_val`,
  `UnitaryGroup.siegelUnipotent`, `siegelUnipotent_val`
- `UnitaryGroup.siegelParabolic`, `mem_siegelParabolic`, `siegelLevi_mem`, `siegelUnipotent_mem`,
  `exists_eq_siegelLevi_mul_siegelUnipotent`
- `UnitaryGroup.IsInBigCell`

All in the namespace `Langlands.UnitaryGroup`.

## Dependencies

`Langlands.Group.Unitary.Basic`; Mathlib: `LinearAlgebra.Matrix.Block`,
`LinearAlgebra.SymplecticGroup` (`Matrix.J`).
