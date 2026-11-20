# Stable flags for extensions of diagonalizable groups by unipotent groups

Author: Worker 60 (Task 7805). Module
`Langlands.GroupScheme.Trigonalizable.StableFlag`, namespace
`Langlands.GroupScheme.TrigonalizableFlag`.

This module proves, for actual group schemes over a field, the implications
(d) ⇒ (a) ⇒ (b) of Milne's Proposition 16.2 in matrix form: every finite
matrix representation of a group `G` with a normal unipotent subgroup `U` and
an fppf quotient `G ⟶ D(Λ)` by `U` becomes upper triangular after a change of
basis over `k`, and `U` then acts with all diagonal entries equal to `1`.

## Setting

`k : Type u` is a field, `G` and `U` are group schemes over `Spec k`,
`i : U ⟶ G`, `Λ : Type u` is an additive commutative group and
`q : G ⟶ D(Λ)` with `D(Λ) = (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp`.
Representations are the Library's `MatrixRepresentation G n`, homomorphisms
`G ⟶ GL_n`; `ρ.pointMatrix T x` is the invertible matrix of a point
`x : T ⟶ G.X` over any scheme `T` over `Spec k`, and `scalarMap T` maps `k`
into `Γ(T, 𝒪_T)`. Points are tested over all schemes `T` over `Spec k`.

## Declarations

- `kernelι_comp_eq_zero`: if `RelativeRoot.IsFppfQuotient (range i) q` and a
  representation `σ` of `G` has `σ(h ≫ i) = 1` for every point `h` of `U`,
  then `kernelι q ≫ σ = 0`. The identity point of the actual kernel of `q`
  lies in `range (kernelι q) = range i`, so it factors through `U`.
- `exists_stable_line` (with `[IsAffineHom G.X.hom] [IsAffineHom U.X.hom]`,
  `IsUnipotent U`, `(range i).IsNormal` and the fppf quotient hypothesis):
  for every `ρ : MatrixRepresentation G (Fin (m + 1))` there is `v ≠ 0` in
  `k^(m+1)` that is fixed by `ρ.restrict i` and spans a stable line: for every
  `T` and `x` there is `c ∈ Γ(T, 𝒪_T)` with `ρ(x) v = c v`.
- Block matrices: `ext1 P` is the block-diagonal matrix with blocks `1` and
  `P`, `ext1GL` its invertible version; `ext1_mul`, `ext1_one`, `ext1_map` and
  the four entry lemmas. `block_conj` says: if the first column of `M` vanishes
  below the diagonal, so does that of `ext1 A * M * ext1 B`, its corner entry is
  `M 0 0`, and its lower right block is `A * tail M * B` (`tail` is the
  published lower right block from `Absolute.UnipotentPointsSolvable`).
- `dropFirst S m` and `insertFirst S m` are the coordinate projection
  `S^(m+1) → S^m` forgetting the first coordinate and its section;
  `dropFirst_mul_insertFirst`, `dropFirst_mul_mul_insertFirst` (the compression
  is `tail`), the `map` lemmas, and `dropFirst_quotient`, which is the quotient
  coordinate equation when the first column vanishes below the diagonal.
- `basePoint_mul`, `conjugate_basePoint_matrix` (the matrices of
  `ρ.conjugate (basePoint g)` are `g ρ(x) g⁻¹` with `g` mapped by
  `scalarMap T`), `map_mulVec'` and `mulVec_firstBasisVector`.
- `exists_triangular` (same hypotheses as `exists_stable_line`): for every
  `m` and `ρ : MatrixRepresentation G (Fin m)` there is `g : GL (Fin m) k` such
  that, writing `ρ' = ρ.conjugate (basePoint g)`, every matrix `ρ'(x)` has zero
  entries `(a, b)` with `b < a`, and every matrix `ρ'(h ≫ i)` with `h` a point
  of `U` has diagonal entries `1`.

## Proofs

`exists_stable_line` follows the proof of (d) ⇒ (a) in Milne 16.2. The
published `normalFixedSubrepresentation ρ i hN` is the representation of `G`
on the full `U`-fixed subspace, with split inclusion `B`, retraction `C`, the
intertwining law `ρ(x) B = B σ(x)` and `σ(h ≫ i) = 1`. Unipotence of `U`
gives a nonzero fixed vector `v₀`, and `C v₀ ≠ 0`, so the fixed space is
nonzero. By `kernelι_comp_eq_zero` and the published `FppfHomDescent`, `σ`
descends to `τ : D(Λ) ⟶ GL`, `q ≫ τ = σ`. The character spaces of `τ` span
(`iSup_characterSpace_eq_top_diagonalizable`), so one of them contains some
`w ≠ 0`. Then `v = B w` is nonzero (`C B = 1`), fixed by `U` (the columns of
`B` are fixed, computed directly from the intertwining law and
`kills_subgroup`), and `ρ(x) v = B τ(q x) w = χ(q x) v` by
`characterSpace_pointMatrix`.

`exists_triangular` is by induction on `m`, as in (a) ⇒ (b) of Milne 16.2.
For `m + 1`, take `v` from `exists_stable_line` and `g₀` with `g₀ v = e₀`
(published `exists_mulVec_eq_firstBasisVector`). The first column of
`ρ' = ρ.conjugate (basePoint g₀)` is a multiple of `e₀`, and `U` fixes `e₀`
(`isFixedVector_conjugate`). The published `quotientCoordinates` with
`dropFirst` and `insertFirst` is the representation `σ` of `G` on the quotient
by the line, whose matrices are `tail ρ'(x)`. The induction hypothesis gives
`g'` for `σ`, and `g = ext1GL g' * g₀` works: `conjugate_mul` and
`block_conj` reduce the entries in the first column and the corner to those of
`ρ'`, and the lower right block to the matrices of `σ.conjugate (basePoint g')`.

## Source and provenance

J. S. Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`; printed
pages (PDF page = printed page + 16):

- Proposition 16.2, pp.324–325, (d) ⇒ (a): "Then V^U is nonzero because U is
  unipotent, and it is stable under G because U is normal (5.15). Now G acts
  on V^U through G/U, and so V^U is a sum of one-dimensional
  subrepresentations (12.12)."
- Proposition 16.2, (a) ⇒ (b): induction on the dimension, passing to `V/V₁`.

The Lean results are derived: they state the matrix form of these steps for
the actual representation, with the extra information that `U` acts trivially
on each successive quotient of the flag. They do not define trigonalizable
groups or relate the statement to `IsTrigonalizable`. No smoothness,
connectedness, algebraic closure or characteristic hypothesis is used, and
`Λ` need not be finitely generated here.
