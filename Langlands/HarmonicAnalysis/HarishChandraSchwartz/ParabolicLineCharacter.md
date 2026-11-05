# The character of a dynamic parabolic on its Chevalley line, and Iwasawa bounds

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.ParabolicLineCharacter`.
The block lemma is in the namespace `Langlands.HarishChandraSchwartz`; all other declarations
are in the namespace `Langlands.GroupScheme.MatrixRepresentation`.

## Purpose and provenance

Provenance: internal. The module `ParabolicLineHeight` gives a representation `ρ` and a basis
vector `e j` whose line `k · e j` has stabilizer exactly the dynamic parabolic `P(χ)(k)`
(`IsRationalLineStabilizer`), and bounds heights on `Ū(F)` by a power of `‖ρ(x) e j‖`. This
module does two things.

1. It defines the character `χ_P : S →* kˣ` by which a line stabilizer `S` acts on the line.
2. Over a non-archimedean local field it rewrites the height bound in terms of `χ_P`, for points
   `x ∈ Ū(F)` written as `x = p k` with `p ∈ P(χ)(F)` and `k` in a fixed compact set `K`.

The result has the shape of the estimates in J.-L. Waldspurger, *La formule de Plancherel pour
les groupes p-adiques, d'après Harish-Chandra* (2003), II.2, printed pp. 253–254 (PDF
pp. 19–20). There the logarithm of the height of `ū ∈ Ū` is compared with the modulus character
of `P` evaluated at the Levi component of `ū` in an Iwasawa decomposition. Here `χ_P` is the
character on the Chevalley line, not the modulus character `δ_P`, and the comparison of the two
is not proved. The bounds below are proved directly from the line, without transcribing a
proof from the source.

## Setting and notation

- `k` is a field and `G` a group scheme over `Spec k`. `rationalPoints G` is the group `G(k)`,
  and `ρ.rationalMatrix x` is the matrix of `x` in `GL_n(k)` for a representation `ρ` on a
  finite type `n`. `e j` is `Pi.single j 1`.
- `IsRationalLineStabilizer ρ j S` (from `ParabolicLineHeight`): for every `x : G(k)`, `x ∈ S`
  exactly when `ρ(x) e j = u • e j` for some `u : kˣ`.
- `χ : 𝔾_m ⟶ G` is a cocharacter, `Dynamic.parabolic χ` is `P(χ)`, and
  `Dynamic.unipotent (Dynamic.oppositeCocharacter χ)` is the opposite unipotent subgroup
  `Ū = U(χ⁻¹)`.
- `IsCocharacterEigenvector χ ρ v` (from `OppositeUnipotentHeight`): for every `t : Fˣ`, `v` is
  an eigenvector of `ρ(χ(t))`.
- `blockUnipotentSubgroup A e` (public, `Dynamic/GeneralLinear`) is the subgroup of `GL_n(A)` of
  matrices `g` with `g i l = δ_{il}` whenever `e i ≤ e l`.
- In the local-field part, `F` carries `[ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]` and `|·|` is `LocalField.residueNormalizedAbsoluteValue F`.
  `rationalVectorNorm F` is the sup norm of vectors for `|·|`, and `rationalMatrixNorm F ρ₀ x`
  is the largest absolute value of an entry of `ρ₀(x)` or of `ρ₀(x)⁻¹`. `G(F)` carries the
  canonical point topology `rationalPointTopology F G.X`.

## Declarations

### Block unipotent matrices

- `HarishChandraSchwartz.mulVec_apply_eq_of_mem_blockUnipotentSubgroup`: let
  `g ∈ blockUnipotentSubgroup A (-e)` and let `w` vanish outside the block `{e = m}`. Then
  `(g w) i = w i` for every `i` with `e i = m`.

### The line character

Throughout, `h : IsRationalLineStabilizer ρ j S`.

- `mulVec_single_one_apply_self`: `(M *ᵥ e j) j = M j j` for a square matrix `M`.
- `IsRationalLineStabilizer.mulVec_single_eq`: for `x ∈ S`,
  `ρ(x) e j = ρ(x) j j • e j`.
- `IsRationalLineStabilizer.apply_self_ne_zero`: for `x ∈ S`, `ρ(x) j j ≠ 0`.
- `IsRationalLineStabilizer.character h : S →* kˣ` (definition): the monoid homomorphism
  sending `x` to the unit `ρ(x) j j`. Its value at `x` is the scalar by which `x` acts on the
  line `k · e j`.
- `IsRationalLineStabilizer.coe_character` (simp): the underlying field element of
  `h.character x` is `ρ(x) j j`.
- `IsRationalLineStabilizer.mulVec_single_eq_character_smul`: `ρ(x) e j = h.character x • e j`
  for `x : S`.
- `IsRationalLineStabilizer.mulVec_mul_inv`: for `p : S` and `g : G(k)`,
  `ρ((p g)⁻¹) e j = (h.character p)⁻¹ • ρ(g⁻¹) e j`.

### Local fields

- `exists_rationalVectorNorm_le_mul_of_weightVector`: let `χ` be a cocharacter of `G`, `ρ` a
  representation on a finite type `n`, and `v` with `IsCocharacterEigenvector χ ρ v`. There is
  `C > 0` with `rationalVectorNorm F v ≤ C * rationalVectorNorm F (ρ(x) v)` for every
  `x ∈ Ū(F)`. No hypothesis on `G` is needed.
- `exists_rationalVectorNorm_mulVec_inv_le`: let `G` be affine and locally of finite type over
  `F`, `ρ` a representation, `v` a vector and `K ⊆ G(F)` compact. There is `B ≥ 0` with
  `rationalVectorNorm F (ρ(k⁻¹) v) ≤ B` for every `k ∈ K`.
- `exists_parabolic_line_character_bounds` (main theorem). Let `G` be affine
  (`[IsAffineHom G.X.hom] [IsAffine G.X.left]`) and locally of finite type over `F`, `χ` a
  cocharacter of `G`, `ρ₀` a closed representation (`IsClosedSubgroup ρ₀`) on `Fin N` with `N`
  positive, and `K ⊆ G(F)` compact. Then there are `n`, `j : Fin (n + 1)`, a representation `ρ`
  on `Fin (n + 1)` and `h : IsRationalLineStabilizer ρ j (Dynamic.parabolic χ).rationalPoints`
  such that, writing `χ_P = h.character`:
  - there is `C₁` with `|χ_P(p)| ≤ C₁`, and
  - there are `C₂ > 0` and `D : ℕ` with
    `rationalMatrixNorm F ρ₀ x ≤ C₂ * max 1 |χ_P(p)|⁻¹ ^ D`,

  for every `x ∈ Ū(F)`, every `p ∈ P(χ)(F)` and every `k ∈ K` with `x = p * k`.

## Proofs as implemented

**Block lemma.** For `g ∈ blockUnipotentSubgroup A (-e)` we have `g i l = δ_{il}` whenever
`-e i ≤ -e l`. Expand `(g w) i = ∑_l g i l * w l`. Only the term `l = i` remains: for `l ≠ i`
with `e l = m = e i` the entry `g i l` is `0`, and for `e l ≠ m` the coordinate `w l` is `0`.
The term `l = i` is `1 * w i`.

**Line character.** By `exists_unit_of_mem`, `ρ(x) e j = u • e j` for a unit `u`. Taking the
`j`-th coordinate gives `ρ(x) j j = u`, which yields `mulVec_single_eq` and
`apply_self_ne_zero`. The character is `Units.mk0 (ρ(x) j j)`. It sends `1` to `1` since
`ρ(1)` is the identity matrix. For multiplicativity, `(ρ(x) ρ(y)) j j` is the `j`-th coordinate
of `ρ(x) (ρ(y) e j) = ρ(y) j j • ρ(x) e j`, which is `ρ(y) j j * ρ(x) j j`. For
`mulVec_mul_inv`, write `(p g)⁻¹ = g⁻¹ p⁻¹`, so that
`ρ((p g)⁻¹) e j = ρ(g⁻¹) (ρ(p⁻¹) e j) = ρ(g⁻¹) (χ_P(p)⁻¹ • e j)`.

**Lower bound on `Ū(F)`.** Use the norm of `|·|` on `F`, which is ultrametric. By public
`exists_innerIso_comp_eq_diagonalCocharacter` there are `g ∈ GL_n(F)` and weights `e : n → ℤ`
such that `χ` followed by `ρ` and conjugation by `g` is the diagonal cocharacter
`t ↦ diag(t^{e i})`. Let `t` be the uniformizer, so `|t| ≠ 1`. Since `v` is an eigenvector of
`ρ(χ(t))`, the vector `w = g v` is an eigenvector of `diag(t^{e i})`, and therefore vanishes
outside one block `{e = m}` (`exists_weight_block_of_mulVec_eq_smul`). For `x ∈ Ū(F)`, the
conjugated matrix `g ρ(x) g⁻¹` lies in `blockUnipotentSubgroup F (-e)`. This follows from public
`Dynamic.unipotent_le_comap`, applied to `ρ` followed by conjugation, together with
`unipotent_diagonalCocharacter` and `rationalMatrix_mem_blockUnipotentSubgroup_iff`. By the
block lemma, `g ρ(x) g⁻¹ w` agrees with `w` on the block `{e = m}`. As `w` vanishes elsewhere,
`‖w‖ ≤ ‖g ρ(x) v‖`. Finally `v = g⁻¹ w`, and multiplication by `g` and by `g⁻¹` changes norms by
at most fixed constants `K` and `K'` (`exists_norm_mulVec_le`). This gives
`C = max 1 K' * max 1 K`.

**Compact bound.** Inversion is continuous on `G(F)` (public `continuous_rationalPoint_inv`),
each entry of `ρ.rationalMatrix` is continuous (public `continuous_rationalMatrix_entry`), and
`|·|` is continuous (public `continuous_residueNormalizedAbsoluteValue`). Hence
`k ↦ rationalVectorNorm F (ρ(k⁻¹) v)` is continuous (`continuous_norm_pi_comp`). Its image of
the compact set `K` is bounded, giving `B`.

**Main theorem.** Take `n`, `j`, `ρ` and `h` from `exists_parabolic_line_rationalMatrixNorm_le`
(`ParabolicLineHeight`), which also gives `C > 0` and `D` with
`rationalMatrixNorm F ρ₀ y ≤ C * max 1 ‖ρ(y) e j‖ ^ D` for `y ∈ Ū(F)`. The vector `e j` is a
cocharacter eigenvector because each `χ(t)` lies in `P(χ)(F)`
(`gmRationalPoint_comp_mem_parabolic` and `exists_unit_of_mem`). Let `C'` come from the lower
bound for `v = e j`, and `B` from the compact bound for `v = e j`. Let `x = p k` be as in the
statement. By `mulVec_mul_inv` and multiplicativity of the norm,
`‖ρ(x⁻¹) e j‖ = |χ_P(p)|⁻¹ * ‖ρ(k⁻¹) e j‖ ≤ |χ_P(p)|⁻¹ * B`.

- Since `x⁻¹ ∈ Ū(F)`, the lower bound gives `1 = ‖e j‖ ≤ C' * |χ_P(p)|⁻¹ * B`. As
  `|χ_P(p)| > 0`, this is `|χ_P(p)| ≤ C' * B`; take `C₁ = C' * B`.
- `rationalMatrixNorm F ρ₀ x = rationalMatrixNorm F ρ₀ x⁻¹` (public `rationalMatrixNorm_inv`),
  and the height bound at `x⁻¹` gives at most `C * max 1 (|χ_P(p)|⁻¹ * B) ^ D`. Since
  `max 1 (a * b) ≤ max 1 a * max 1 b` for `a, b ≥ 0`, this is at most
  `C * max 1 B ^ D * max 1 |χ_P(p)|⁻¹ ^ D`; take `C₂ = C * max 1 B ^ D`.

## Scope

The representation `ρ`, the index `j` and hence `χ_P` are produced by the existence theorem and
are not explicit. The theorem does not assert that every point of `Ū(F)` has a factorization
`x = p k` with `k ∈ K`; that is an Iwasawa decomposition, which is a separate input. It does not
identify `χ_P` with a power of the modulus character `δ_P`, it does not show that `χ_P` is
trivial on the unipotent radical, and it does not give a lower bound for the height of `x` in
terms of `χ_P`. It says nothing about Haar measures and does not prove the host conditional
intertwining theorem.
