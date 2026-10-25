# Standard modules of `GL_n(ℝ)` and `GL_n(ℂ)` and their parameters

Author: Worker 35. Definition contribution to task
`91266440-3276-48dc-ab77-8d1c1fa386e8`, revision 1.
This is the third archimedean unit for Shahidi's Theorem 3.1 (1985). It
builds on `Langlands.Representation.Archimedean.GeneralLinear`, and it
attaches Weil-group data to Banach representations of `GL_N(ℝ)`,
`GL_N(ℂ)` and of the pair Levi subgroups. The Weil-group data are lists
of the Library's archimedean blocks (`RealBlock`, `ComplexCharacterData`
from `Langlands.LocalFactor`). The module defines:

- the `K`-finite vectors and the smooth `K`-finite vectors of a
  representation;
- infinitesimal equivalence with a space of functions under right
  translation, that is, an isomorphism of `(𝔤, K)`-modules;
- the smooth principal series of `GL_N(F)` and the standard modules of
  lists of blocks inside it;
- the predicates `HasRealParameter`, `HasComplexParameter` and their pair
  versions: `π` is infinitesimally equivalent to the standard module of
  the blocks.

For a generic irreducible `π` the last predicate says that the Langlands
parameter of `π` is the sum of the blocks (see "Scope of the parameter
predicates" below). Lean proves the submodule and representation axioms,
membership criteria, two evaluation formulas, a range lemma for the block
positions, integrability of the Fourier integrands, and that the
rotations are continuous and lie in `O(N)`. Nothing about the
classification is proved.

## Mathematical content

The namespace is `Langlands.Archimedean`. As in `GeneralLinear`,
`GL_N(F)` is `Langlands.GeneralLinear N F` with model
`matrixModel F N = 𝓘(ℝ, M_N(F))`; smoothness is real smoothness, also
for `F = ℂ`. `E` is a complex normed space and `π : G →* (E →L[ℂ] E)`
is a representation by bounded operators.

### `K`-finite vectors and infinitesimal equivalence

These declarations are generic: `G` is a group with a charted-space
structure modelled by `I` on a real normed space `𝔤`, and `K` is a
subgroup.

- `kFiniteVectors ρ K`, for a linear representation `ρ` of `G` on a
  complex vector space, is the submodule of vectors `v` whose orbit
  `{ρ(k)v : k ∈ K}` spans a finite-dimensional subspace
  (`mem_kFiniteVectors_iff`). It reuses the underlying submodule of
  `FiniteVectors.subrepresentation` for the restriction of `ρ` to `K`.
- `linearRepresentation π` forgets continuity of the operators.
- `kFiniteSmoothVectors I π K` is the intersection of the smooth vectors
  `smoothVectors I π` of `SmoothVectors` with the `K`-finite vectors
  (`mem_kFiniteSmoothVectors_iff`).
- The existing `Whittaker.rightTranslation ℂ G` supplies the
  right regular representation `(R(g)f)(x) = f(xg)` on all functions `G → ℂ`.
- `kFiniteFunctions V K`, for a submodule `V` of functions `G → ℂ`, is
  the submodule of `f ∈ V` that are `K`-finite under right translation.
- `rightDerivative I X f` is the function
  `g ↦ mfderiv I 𝓘(ℝ, ℂ) (h ↦ f(gh)) 1 X`, the derivative of `f` along
  right translation in the direction `X ∈ 𝔤`. For smooth `f` on
  `GL_N(F)` this is `d/dt f(g exp(tX))` at `t = 0`. For a function that
  is not differentiable, Mathlib's `mfderiv` is `0`; the derivative is
  only applied below to smooth functions.
- `IsInfinitesimallyEquivalent I π K V` holds when there is a complex
  linear isomorphism `e` from `kFiniteSmoothVectors I π K` onto
  `kFiniteFunctions V K` such that for every `k ∈ K`, `X ∈ 𝔤` and every
  smooth `K`-finite `v`:
  - `π(k)v` is again smooth and `K`-finite, and `e(π(k)v) = R(k)(e v)`;
  - the Lie derivative `dπ(X)v = lieDerivative I π X v` of
    `SmoothVectors` is again smooth and `K`-finite, and
    `e(dπ(X)v) = rightDerivative I X (e v)`.

  The membership conditions are bundled as the `∃ hv` in the Lean
  statement. They hold for every `v`, because `K·dπ(X)v` lies in
  `dπ(Ad(K)X)` applied to the span of `K·v`. They are part of the
  definition so that `e` can be applied to these vectors.

So `IsInfinitesimallyEquivalent` is an isomorphism of
`(𝔤, K)`-modules between the smooth `K`-finite vectors of `π` and the
`K`-finite functions of `V`, with `K` acting by right translation and
the real Lie algebra `𝔤` by right derivatives. The complexified Lie
algebra then acts by complex-linear extension, so nothing is lost by
using the real Lie algebra.

- `pairFunctions I I' V V'`, for spaces `V` and `V'` of functions on `G`
  and `G'`, is the space of jointly smooth functions `f` on `G × G'`
  (for `I.prod I'`) with every slice `f(·, g')` in `V` and every slice
  `f(g, ·)` in `V'` (`mem_pairFunctions_iff`).

### Principal series

For `F` an `RCLike` field, `|x|_F = ‖x‖^[F:ℝ]` is the usual absolute
value over `ℝ` and its square over `ℂ`.

- `principalSeriesCharacter F N χ a` is
  `∏_{i<N} χ_i(a_i) · |a_i|_F^((N-1)/2 - i)` for `a = (a_0, …, a_{N-1})`
  in `(Fˣ)^N`, where `χ : ℕ → Fˣ → ℂ` gives the function at each
  position.
- `principalSeries F N χ` is the space of real `C^∞` functions `f` on
  `GL_N(F)` with
  `f(diag(a) · u · g) = principalSeriesCharacter F N χ a · f(g)` for
  every `a ∈ (Fˣ)^N`, every upper unipotent `u` (the Library's
  `upperUnipotent N F`) and every `g` (`mem_principalSeries_iff`).
  `diag(a)` is the Library's `Iwasawa.diagonalUnits a`.

When the `χ_i` are characters, this is the smooth principal series
induced from the upper triangular Borel subgroup `B`, with unitary
(normalized) induction, `G` acting by right translation. The factor
`∏ |a_i|_F^((N-1)/2 - i)` is `δ_B(diag(a))^{1/2}`, because the modulus
character of `B` is
`δ_B(diag(a)) = ∏_{i<j} |a_i/a_j|_F = ∏_i |a_i|_F^(N-1-2i)`.

### Real standard modules

The Library's `RealBlock` is either `.character d` for a
`RealCharacterData` `d` (a continuous character of `ℝˣ` with
`d.character x = sgn(x)^ε |x|^t`, `ε = d.parity`, `t = d.exponent`), or
`.induced d` for a `ComplexCharacterData` `d` (a continuous character
of `ℂˣ` with `d.character z = (z/|z|)^m |z|^(2t)`, `m = d.weight`,
`t = d.exponent`). Its rank `RealBlock.rank` is `1` or `2`, and
`realRank ds` is the total rank of a list.

- `realInducedFirstCharacter d` is
  `x ↦ sgn(x)^(|m|+1) |x|^(t + |m|/2)` and `realInducedSecondCharacter d`
  is `x ↦ |x|^(t - |m|/2)`.
- `realPositionCharacter ds p` is the function at the diagonal position
  `p`. The blocks of `ds` occupy consecutive positions in order: a
  character block one position, with its character; an induction block
  two positions, with the first and second characters above. Positions
  past the end get the constant function `1`.
- `realInducedBlockAt ds p` is `some d` when an induction block `d`
  starts at position `p`, and `none` otherwise. `realInducedBlockAt_lt`
  proves that then both positions `p` and `p + 1` are below
  `realRank ds`.
- `rotationGenerator N p` is the real matrix `E_{p+1,p} - E_{p,p+1}`, and
  `blockRotation N p θ = exp(θ (E_{p+1,p} - E_{p,p+1}))` in `GL_N(ℝ)`,
  with inverse `exp(-θ(E_{p+1,p} - E_{p,p+1}))` (`blockRotation_val`).
  Lean proves that it is continuous in `θ` (`continuous_blockRotation`),
  that the generator is antisymmetric
  (`rotationGenerator_mem_skewAdjoint`), and that the rotations lie in
  `O(N) = unitaryCompact ℝ N` (`blockRotation_mem_unitaryCompact`). When
  `p + 1 < N`, the rotation is the rotation by `θ` in the coordinates
  `p, p + 1`, with block `[[cos θ, -sin θ], [sin θ, cos θ]]` there and
  the identity elsewhere. This explicit form is not proved in Lean and
  is not used by any definition.
- `blockFourierCoefficient N p k f g` is
  `∫_0^{2π} f(r_p(θ) g) e^{-ikθ} dθ`, with `r_p(θ) = blockRotation N p θ`.
  `intervalIntegrable_blockFourier` proves that the integrand is
  integrable for continuous `f`.
- `realStandardModule N ds` is the subspace of
  `principalSeries ℝ N (realPositionCharacter ds)` of functions `f` such
  that, for every induction block `d` of weight `m` starting at a
  position `p`, every integer `k` with `|k| < |m|` and every `g`, the
  Fourier coefficient `blockFourierCoefficient N p k f g` vanishes
  (`mem_realStandardModule_iff`).

### Complex standard modules

- `complexPositionCharacter ds p` is the character of the `p`-th block
  of a list of `ComplexCharacterData`, and `1` past the end.
- `complexStandardModule N ds` is
  `principalSeries ℂ N (complexPositionCharacter ds)`.

### Parameter predicates

- `HasRealParameter π ds`, for `π` a representation of `GL_N(ℝ)`:
  `realRank ds = N`, and `π` is infinitesimally equivalent, for the
  model `matrixModel ℝ N` and `K = O(N) = unitaryCompact ℝ N`, to
  `realStandardModule N ds`.
- `HasComplexParameter π ds`, for `π` a representation of `GL_N(ℂ)`:
  `ds` has length `N`, and `π` is infinitesimally equivalent, for
  `K = U(N) = unitaryCompact ℂ N`, to `complexStandardModule N ds`.
- `HasRealPairParameter σ ds₁ ds₂`, for `σ` a representation of
  `GL_m(ℝ) × GL_n(ℝ)`: the ranks are `m` and `n`, and `σ` is
  infinitesimally equivalent, for `pairModel ℝ m n` and
  `K = pairCompact ℝ m n = O(m) × O(n)`, to
  `pairFunctions (realStandardModule m ds₁) (realStandardModule n ds₂)`.
- `HasComplexPairParameter σ ds₁ ds₂` is the same over `ℂ`, with
  `U(m) × U(n)`.

## Instances, universes and scope

The file sets `set_option backward.isDefEq.respectTransparency false`, as
`GeneralLinear` does; it affects elaboration only. The generic
declarations are universe-polymorphic. The real and complex standard
modules are for `GL_N(ℝ)` and `GL_N(ℂ)` themselves, since the
Library's blocks are real or complex.

The definitions require nothing of `π`: it need not be continuous,
irreducible, admissible or generic. In the later statement of
Shahidi's Theorem 3.1 they are combined with
`IsGenericBanachRepresentation` and `IsGenericBanachPairRepresentation`
of `GeneralLinear`. The lists of blocks are arbitrary, in any order,
with weight `0` allowed in induction blocks, as in the Library.

### Scope of the parameter predicates

This subsection explains what the predicates mean. None of it is proved
in Lean.

- **Generic representations.** Let `π` be irreducible, admissible and
  generic. By Vogan's theorem, as Shahidi uses it (1985, p.984 and
  p.1002, citing Vogan [33], Theorem 6.2(f)), `π` is infinitesimally the
  full induced representation `I_M(ν', σ', θ')` from a tempered `σ'`, so
  its standard module is irreducible and `π` is infinitesimally
  equivalent to it. By Knapp's Theorems 1 and 2 (resp. 4 and 5),
  `HasRealParameter π ds` (resp. `HasComplexParameter π ds`) then holds
  exactly when the sum of the Weil representations of the blocks of
  `ds` is the Langlands parameter of `π`. Here the blocks are taken in
  any order, and an induction block of weight `0` is read as the sum of
  its two characters (Derived choices 3 and 4).
- **Non-generic representations.** The predicate is not meant for
  non-generic `π`. For example, the trivial representation of
  `GL_2(ℝ)` has the Langlands parameter `|·|^{1/2} ⊕ |·|^{-1/2}`, but its
  standard module `Ind(|·|^{1/2} ⊗ |·|^{-1/2})` is infinite-dimensional.
  The trivial representation on `ℂ` has a one-dimensional space of
  smooth `K`-finite vectors. The `K`-finite functions of every standard
  module of total rank `2` form an infinite-dimensional space. So no
  linear isomorphism exists, and `HasRealParameter` fails for the trivial
  representation and every list of blocks.
- **Admissible representations.** For admissible `π` every `K`-finite
  vector is smooth (Knapp, p.399), so `kFiniteSmoothVectors` is the
  space `V_K` of `K`-finite vectors, and `IsInfinitesimallyEquivalent`
  is Knapp's infinitesimal equivalence with the standard module.

## Original source correspondence

A. W. Knapp, *Local Langlands correspondence: the archimedean case*, in
*Motives*, Proc. Sympos. Pure Math. 55, Part 2 (1994), 393–410
(literature id `knapp-1994-archimedean-llc`; the registered file is the
whole volume, PDF page = printed page + 10).

- Printed p.399 (PDF 409), §2: `K = O(n)`. A Hilbert-space
  representation is admissible if each irreducible representation of
  `K` occurs with finite multiplicity. `V_K` is the space of `K`-finite
  vectors, those transforming in a finite-dimensional space under `K`;
  each is a `C^∞` vector, and `V_K` is a `(𝔤, K)`-module. "Two
  admissible representations are said to be infinitesimally equivalent
  if their underlying `(𝔤, K)` modules are isomorphic". Footnote 2:
  representations are on complex spaces and jointly continuous.
  (2.1a), (2.1b): the discrete series `D_ℓ` (`ℓ ≥ 1`) of
  `SL^±_2(ℝ) = {|det g| = 1}` is induced from the representation `D_ℓ^+`
  of `SL_2(ℝ)` on holomorphic functions on the upper half-plane with the
  automorphy factor `(bz + d)^{-(ℓ+1)}`, so its lowest `SO(2)`-weight is
  `ℓ + 1`.
- Printed p.400 (PDF 410): building blocks (2.2a) `1 ⊗ |·|^t`,
  `sgn ⊗ |·|^t` for `GL_1(ℝ)` and (2.2b) `D_ℓ ⊗ |det(·)|^t` for
  `GL_2(ℝ)`, `t ∈ ℂ`. (2.3) the block diagonal subgroup `D` of a
  partition of `n` into `1`s and `2`s, `Q = DU` the block upper
  triangular subgroup. (2.4) `I(σ_1, …, σ_r)` is unitary induction from
  `Q`. Theorem 1: under the ordering (2.5), `I(σ_1, …, σ_r)` has a unique
  irreducible quotient `J(σ_1, …, σ_r)`; these exhaust the irreducible
  admissible representations, and part (c) says that they are
  determined by the blocks up to permutation.
- Printed p.402 (PDF 412), (3.3): the irreducible two-dimensional
  representations of `W_ℝ` are classified by `(ℓ, t)` with `ℓ ≥ 1`:
  `φ(re^{iθ})u = r^{2t}e^{iℓθ}u`, `φ(re^{iθ})u' = r^{2t}e^{-iℓθ}u'`,
  `φ(j)u = u'` and `φ(j)u' = (-1)^ℓ u`. The character of `ℂˣ` on `u` is
  `(z/|z|)^ℓ |z|^{2t}`. This is the Library's `ComplexCharacterData`
  with weight `ℓ` and exponent `t`. The Library's induced representation
  `ComplexCharacterData.realInducedRepresentation` acts by
  `z·(v_1, v_2) = (χ(z)v_1, χ(z̄)v_2)` and `j·(v_1, v_2) = (v_2, χ(-1)v_1)`,
  with `χ(-1) = (-1)^m`. For weight `m = ℓ ≥ 1` it is Knapp's `(ℓ, t)` in
  the basis `u = (1, 0)`, `u' = (0, (-1)^ℓ)`; for `m ≤ -1` it is
  isomorphic to `(|m|, t)` (swap the coordinates).
- Printed p.403 (PDF 413), (3.4): `(ℓ, t) ↦ D_ℓ ⊗ |det(·)|^t`, and the
  one-dimensional representations go to `1 ⊗ |·|^t` and `sgn ⊗ |·|^t`;
  (3.5) and Theorem 2: `φ ↦ J(σ_1, …, σ_r)` after reordering by (2.5) is
  the local Langlands correspondence for `GL_n(ℝ)`.
- Printed p.405 (PDF 415), §4: `[z] = z/|z|` and `|z|_ℂ = |z|^2`. (4.1)
  the characters `[·]^ℓ ⊗ |·|_ℂ^t` of `GL_1(ℂ)`, which are the Library's
  `ComplexCharacterData` with weight `ℓ` and exponent `t`. (4.2)
  `I(σ_1, …, σ_n)` is unitary induction from the upper triangular
  subgroup `B`. Theorem 4: Langlands quotients under (4.3), exhaustion,
  and determination up to permutation. (4.4) the characters of
  `W_ℂ = ℂˣ`. Printed p.406 (PDF 416), (4.5) and Theorem 5: the local
  Langlands correspondence for `GL_n(ℂ)`.

F. Shahidi, *Local coefficients as Artin factors for real groups*, Duke
Math. J. 52 (1985), 973–1007 (literature id `shahidi-1985-real-artin`;
PDF page = printed page − 972).

- Printed p.975 (PDF 3), Introduction: the argument relies on "a result
  of Vogan (part f of Theorem 6.2 of [33])".
- Printed p.984 (PDF 12), §2: for an irreducible admissible generic
  Banach representation `σ`, the Langlands quotient "is equal to the
  corresponding induced representation by part f of Theorem 6.2 of
  [33]". In the proof of Proposition 2.2, `σ = I_M(ν', σ', θ')`
  infinitesimally, with `σ'` irreducible tempered.
- Printed p.1002 (PDF 30), end of the proof of Theorem 3.1: for any
  irreducible admissible generic `σ`, choose a tempered `σ'` and `ν'` with
  `σ = I_M(ν', σ', θ')` (Theorem 6.2 of [33]). Shahidi's [33] is D. A.
  Vogan, *Gelfand–Kirillov dimension for Harish-Chandra modules*, Invent.
  Math. 48 (1978), 75–98.

### Derived choices

These points explain the formalization. None is proved in Lean.

1. **Standard modules inside the principal series.** Knapp induces
   `σ_1 ⊗ ⋯ ⊗ σ_r` from the block upper triangular subgroup `Q`. Here the
   standard module is realized inside the principal series from `B` by
   induction in stages. Each `GL_2(ℝ)` block `D_ℓ ⊗ |det|^t` is realized
   as a subrepresentation of a principal series of `GL_2(ℝ)` (choice 2).
   Write `Φ(g)(h) = δ_Q^{-1/2}(h) f(hg)` for `h ∈ D`, so that
   `f(g) = Φ(g)(1)` identifies `Ind_Q^G(Ind_{B∩D}^D χ)` with
   `Ind_B^G χ`. The modulus characters agree because
   `δ_B = δ_{B∩D} · δ_Q` on `B`. Then `f` lies in `Ind_Q^G(⊗σ_j)` if
   and only if `Φ(g)` lies in the subrepresentation `⊗σ_j` of
   `Ind_{B∩D}^D χ` for every `g`. For a `GL_2` block at the positions
   `p, p + 1` this condition reads: for every `h ∈ D`, every `g` and
   every `|k| < ℓ`, `∫ f(h r_p(θ) g) e^{-ikθ} dθ = 0`. It suffices to
   take `h = 1`. Write `h = bκ` with `b ∈ B ∩ D` and `κ` in the
   product of the groups `SO(2)` of the `GL_2` blocks, since
   `GL_2(ℝ) = B_2 · SO(2)` and `GL_1(ℝ) ⊂ B`. The factor `b` only
   multiplies the integral by a character value. The other components
   of `κ` commute with `r_p(θ)` and can be absorbed into `g`. The
   `SO(2)`-component at `p` is a rotation `r_p(φ)`, and it shifts the
   integral by `e^{ikφ}`, by periodicity. This gives the condition in
   `realStandardModule`.
2. **The discrete series block.** Let `d` have weight `m`, put
   `ℓ = |m| ≥ 1`, and let `μ_1`, `μ_2` be the first and second
   characters, so `μ_1 μ_2 = sgn^{ℓ+1} |·|^{2t}` and
   `μ_1/μ_2 = sgn^{ℓ+1} |·|^ℓ`. Since `μ_1/μ_2(x) = x^ℓ sgn(x)`, the
   principal series `Ind(μ_1 ⊗ μ_2)` of `GL_2(ℝ)` is reducible.
   - The homogeneous polynomials of degree `r` in the bottom row
     form a finite-dimensional subrepresentation of the principal
     series with `μ_1/μ_2 = sgn^r |·|^{-(r+1)}`. Dually, here
     (`r = ℓ - 1`) the finite-dimensional representation of dimension
     `ℓ` is a quotient, and the infinite-dimensional constituent is a
     subrepresentation.
   - Since `r(π) = -I_2`, the `SO(2)`-weights `k` of the principal
     series satisfy `k ≡ ℓ + 1 (mod 2)`, each with multiplicity one. The
     quotient has the weights `|k| ≤ ℓ - 1`. So the subrepresentation
     consists of the weights `|k| ≥ ℓ + 1`, that is, of the vanishing of
     the weights `|k| < ℓ`.
   - This subrepresentation is `D_ℓ ⊗ |det|^t`, by the standard
     embedding of the discrete series into the principal series. Its
     lowest weight is `ℓ + 1`, as in Knapp's (2.1b), and its central
     character is `sgn^{ℓ+1} |·|^{2t}`, as for `D_ℓ ⊗ |det|^t`.
   - For `GL_2(ℝ)` alone (`N = 2`, `p = 0`), the condition at `g = 1`
     says that `f` has no right `SO(2)`-weight `|k| < ℓ`. Indeed the
     weight-`k` component `f_k` of `f` lies in the principal series, so
     it is determined by its restriction to `SO(2)`, because
     `GL_2(ℝ) = B · SO(2)`; and `f_k(r(θ)) = e^{ikθ} f_k(1)`, where
     `2π f_k(1)` is the Fourier coefficient at `g = 1`. The condition for
     all `g` follows because the subrepresentation is invariant.

   The central character `sgn^{|m|+1} |·|^{2t}` is the Library's
   `RealBlock.determinant (.induced d)`, `sgn · d.character|ℝˣ`. Putting
   the sign on the first character is a choice:
   `Ind(μ_1 sgn^{ℓ+1} ⊗ μ_2 sgn^{ℓ+1})` is the twist by
   `sgn(det)^{ℓ+1}`, which fixes `D_ℓ ⊗ |det|^t`.
3. **Weight zero.** The Library allows induction blocks of weight `0`,
   whose Weil representation `Ind(|z|^{2t})` is the sum
   `|·|^t ⊕ sgn|·|^t` of two characters (Knapp p.402: the two-dimensional
   representations with `ℓ = 0` are reducible). Then the Fourier
   condition is vacuous. The standard module is the principal series
   `Ind(sgn|·|^t ⊗ |·|^t)`, which is irreducible because
   `μ_1/μ_2 = sgn`. This is the standard module of the sum of the two
   characters.
4. **Order of the blocks.** Knapp orders the blocks by (2.5) (resp.
   (4.3)) so that the Langlands quotient is defined. The predicates take
   the blocks in the given order. Standard modules of the same blocks in
   different orders have the same character, hence the same composition
   factors. If one of them is irreducible, as for generic `π`, all are
   irreducible and isomorphic. So reordering the blocks changes the
   standard module but, for irreducible admissible `π`, not whether the
   predicate holds. Replacing the weight `m` of an induction block by
   `-m` does not change the standard module, because only `|m|` enters;
   on the Weil side the representations of weights `m` and `-m` are
   isomorphic (Knapp (3.2), (3.3)). Replacing a weight-zero induction block by its
   two characters `sgn|·|^t`, `|·|^t`, in this order, gives the same
   standard module.
5. **Smooth `K`-finite vectors.** Knapp's `(𝔤, K)`-module is `V_K` with
   `K` acting by `π` and `𝔤` by the derivative of `π` on smooth vectors.
   Since `K`-finite vectors of admissible representations are smooth,
   `V_K = kFiniteSmoothVectors`. The standard module is realized by
   smooth functions with right translation. Its `K`-finite functions are
   the Harish-Chandra module of the Hilbert-space induced representation,
   because `K`-finite vectors of induced representations are smooth.
6. **Pairs.** For admissible `V` and `V'` (finite `K`-multiplicities),
   the `K × K'`-finite functions in `pairFunctions V V'` are the
   algebraic tensor product `V_K ⊗ V'_{K'}`. The proof sketch: a
   `K × K'`-isotypic component of type `τ ⊗ τ'` has all its slices
   `f(·, g')` in the finite-dimensional `τ`-isotypic part of `V_K`, and
   all its slices `f(g, ·)` in the `τ'`-isotypic part of `V'_{K'}`.
   Conversely, finite sums of products are jointly smooth with slices in
   `V` and `V'`. So the pair predicates say that `σ` is infinitesimally
   the external tensor product `π_1 ⊠ π_2` of representations with the
   parameters `ds₁` and `ds₂`, which is the form of Shahidi's `σ` on the
   Levi subgroup `GL_m × GL_n`.
7. **Orientation and normalization.** The direction of the rotations is
   a convention: changing it replaces `k` by `-k`, which preserves the
   condition `|k| < |m|`. The order of the two characters of an
   induction block is not. With the upper triangular Borel subgroup and
   right translation, `D_ℓ ⊗ |det|^t` is a subrepresentation of
   `Ind(μ_1 ⊗ μ_2)` for `μ_1/μ_2 = sgn^{ℓ+1} |·|^ℓ`, but a quotient of
   `Ind(μ_2 ⊗ μ_1)`. So the Fourier condition cuts out a
   subrepresentation only in the order chosen here. Unitary induction
   (Knapp (2.4), (4.2)) is the factor `δ_B^{1/2}` of
   `principalSeriesCharacter`.
8. **One-dimensional real blocks.** On the Weil side the Library's
   `RealCharacterData.representation` is the character of `ℝˣ` pulled
   back along the abelian coordinate of `W_ℝ`. Knapp's (3.4) assigns
   `1 ⊗ |·|^t` and `sgn ⊗ |·|^t` to the one-dimensional representations.
   Here the character of `ℝˣ` itself is the position character, which is
   the normalization of local class field theory for `ℝ`.

## Relation to other Library units

The blocks and their Weil representations, `L`- and `ε`-factors are
the Library's (`Langlands.LocalFactor.ArchimedeanAttachment`,
`ArchimedeanPresentation`; `RealBlock.representation`,
`realRank`, `RealBlock.determinant`). `Iwasawa.diagonalUnits` is from
`Langlands.Representation.Whittaker.Iwasawa`, and `upperUnipotent`,
`unitaryCompact`, `matrixModel`, `pairModel` and `pairCompact` are as in
`GeneralLinear`. The smooth vectors and Lie derivatives are those of
`SmoothVectors`. This module does not import
`Langlands.Representation.Archimedean.Induction`. The later statement
of Shahidi's Theorem 3.1 combines both: for `σ` with
`HasRealPairParameter σ ds₁ ds₂` (or the complex version), the local
coefficient of `Induction` is to be compared with the gamma factor of
the tensor product of the parameter of `ds₁` and the dual of the
parameter of `ds₂`.
