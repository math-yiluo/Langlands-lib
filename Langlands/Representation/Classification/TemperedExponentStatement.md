# The exponent criterion for temperedness on `GL_n`

Worker 19 states `Langlands.GLTemperedExponentCriterionStatement`. This is a
proposition definition. It asserts no Lean proof. Temperedness is Worker 23's
analytic predicate `T.IsTempered` (matrix coefficients in `L^(2+ε)` modulo the
centre), and the exponents are Worker 23's `T.IsJacquetExponent`. Neither is
defined through the other.

## Objects and quantifiers

The statement quantifies every prime `p`, every `PadicField p` `F` in a field
universe `uF`, every realization `T : F.TopologicalData` of its topology, and
every positive rank `n`. The group is the actual
`GeneralLinear n F.Carrier = GL_n(F)`, with the topology induced by `T`.

The representation carrier `V` is a complex vector space in an independent
universe `uV`. It may be zero, and has no topology or finite-dimensionality
assumption. The representation `ρ` must be admissible for the topology of `T`
(`IsAdmissible ρ`, which includes smoothness). It need not be irreducible or of
finite length.

`ω : F^× →* ℂ^×` is an arbitrary group homomorphism. No continuity or unitarity
is assumed. The hypothesis
`∀ a v, ρ (GeneralLinear.scalar a) v = ω a • v` says that `ρ` is an
`ω`-representation: the scalar matrix `a · 1_n` acts by the number `ω(a)`.

## The equivalence

Under these hypotheses, `T.IsTempered ρ` holds if and only if, for every ordered
block shape `B = (n_1, …, n_k)` of `n`, every character
`χ : (F^×)^k →* ℂ^×` with `T.IsJacquetExponent B ρ χ`, and every
`a = (a_1, …, a_k) ∈ (F^×)^k` with `|a_1| ≤ |a_2| ≤ ⋯ ≤ |a_k|` (`Monotone` in
the index), one has `‖χ(a)‖ ≤ 1`.

Here `|·|` is the published residue-normalized absolute value
`T.normalizedAbs`, with `|ϖ| = q⁻¹`. The inequality is weak, and the
elements with all `|a_i|` equal are not removed.

The two sides mean the following.

- `T.IsTempered ρ` (module `Langlands.Representation.Classification.Tempered`)
  requires `IsTemperedModCenter ρ μ` for every Borel Haar measure `μ` on the
  actual quotient `GL_n(F) ⧸ Z`. That predicate asks for admissibility, a
  `UnitaryCentralCharacter ρ` (a character of the centre with open kernel and
  norm one by which the centre acts), and membership of every descended
  coefficient norm `gZ ↦ |ℓ(ρ(g) v)|`, for `ℓ` in the smooth dual and `v ∈ V`,
  in `L^(2+ε)(μ)` for every real `ε > 0`.
- `T.IsJacquetExponent B ρ χ` (module `Langlands.Representation.Exponents.Jacquet`)
  says that `χ` has open kernel and that, for some `k`, some nonzero vector of
  the normalized Jacquet module of the standard upper block parabolic `P_B` is
  killed by `(a · − χ(a))^k` for every block scalar
  `a = diag(a_1 1_(n_1), …, a_k 1_(n_k))`. The action is the published
  normalized one, `a · [v] = δ_(P_B)(a)^(-1/2) [ρ(a) v]`, with the published
  block modulus `δ_(P_B)(a) = ∏_(i<j) |a_i / a_j|^(n_i n_j)` on block scalars.

There is no separate condition that `ω` be unitary. The one-block shape
`B = (n)` already gives it. There `P_B = GL_n(F)`, the Jacquet module is `V`, the
modulus is trivial and the block scalars are the scalar matrices. So for
`V ≠ 0` the character `a ↦ ω(a_1)` is an exponent (its kernel is open because
`ρ` is smooth). The criterion with `k = 1` then gives `|ω(a)| ≤ 1` for all
`a`, and applying it to `a⁻¹` gives `|ω(a)| = 1`.

## Original sources

- A. J. Silberger, *The Langlands quotient theorem for p-adic groups*, Math.
  Ann. 236 (1978), §3, printed p.98 (PDF page 4; literature ID
  `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
  SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`).
  For an irreducible admissible `π`: "The representation π is tempered if and
  only if the following condition is fulfilled ([4], Lemma 4.5.3): For every
  standard p-pair (P, A) and every χ ∈ X_π(P, A), |χ(a)| ≤ 1 for all a ∈ A^+.
  This condition implies that χ_π is unitary."
- A. J. Silberger, *Introduction to harmonic analysis on reductive p-adic
  groups*, 1979 (literature ID `silberger-1979-harmonic-analysis`, SHA256
  `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`; PDF page =
  printed page + 6). §4.5, p.184: an admissible representation is tempered when
  every one of its matrix-coefficient functions is tempered, that is, satisfies
  the weak inequality of Theorem 4.5.1, pp.183–184. Lemma 4.5.3, pp.185–186, is
  the exponent criterion for each such function: tempered if and only if
  `|χ(a)| ≤ 1` for all `a ∈ A^+`, for every p-pair `(P, A)` and every exponent
  `χ` of its constant term along `P`.
- J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
  d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333 (literature
  ID `waldspurger-2003-plancherel`, SHA256
  `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`; PDF page =
  printed page − 234). This is the form followed here.
  - §I.1, pp.239–242: `+ā_P^(G*)` is the set of combinations
    `Σ_(α ∈ ∆(P)) x_α α` with all `x_α ≥ 0` (p.239). `H_M` is defined with
    `q^(-⟨χ, H_M(m)⟩) = |χ(m)|_F` (p.240). `Ā_0^+` is the set of `a ∈ A_0` with
    `⟨α, H_0(a)⟩ ≥ 0`, that is `|α(a)| ≤ 1`, for every simple root `α`
    (pp.239–240). Formula (5), p.241, gives `mes(KmK) ≍ δ_0(m)^(-1)` on
    `M̄_0^+`, and `σ(g) = log ‖g‖` (p.242).
  - §I.3, p.243: for an admissible `π`, `Exp(π)` is the set of characters `χ` of
    `A_G` with `V_χ ≠ 0`, where `V_χ` is the set of vectors `v` with
    `(π(a) − χ(a))^d v = 0` for all `a` and some `d`. The Jacquet module carries
    `π_P(m) j_P(v) = δ_P(m)^(-1/2) j_P(π(m) v)`.
  - §III.2, p.265: `π` is tempered when every coefficient `f` satisfies
    `|f(g)| ≤ c Ξ(g)(1 + σ(g))^r` for some `c` and `r`.
  - Proposition III.2.2, pp.265–266: for any admissible `π`, the following are
    equivalent: (i) `π` is tempered; (ii) `Re(χ) ∈ +ā_P^(G*)` for every
    semi-standard parabolic `P` and every `χ ∈ Exp(π_P)`; (iii) the same for
    `P = G` and the standard proper maximal parabolics only. Its proof, p.266,
    uses (ii) in the form "|χ(a)| ⩽ 1 pour a ∈ Ā_0^+ ∩ A_M".
- S. S. Kudla, *The local Langlands correspondence: the non-archimedean case*,
  §2.2, printed p.372 (literature ID `kudla-1994-local-langlands-nonarchimedean`,
  SHA256 `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`).
  This is the `L^(2+ε)` definition of temperedness that Worker 23's
  `IsTemperedModCenter` implements. It is not a source of the criterion.

## Translation to the Lean statement (derived)

The statement specializes the sources to complex representations of
positive-rank `GL_n` over finite extensions of `Q_p`. The sources cover
connected reductive groups. The identifications below are standard computations
for `GL_n`. They are explained here and not stated in Lean.

- **Parabolics.** Take the upper triangular Borel subgroup, the diagonal torus
  and the simple roots `α_j = e_j − e_(j+1)`. The standard parabolics are then
  the upper block parabolics `P_B`. The Lean statement uses every standard `P_B`,
  so its condition is implied by Waldspurger's (ii) and implies his (iii).
- **Exponents.** The split centre `A_M` of the block Levi is the group of block
  scalars. Waldspurger's `V_χ` uses a power `d` depending on the vector; for a
  single nonzero vector this is the same as the uniform power in
  `IsGeneralizedEigencharacter`. For admissible `ρ` every such `χ` has open
  kernel: a nonzero vector of `V_χ` is fixed by `A_M ∩ K_M` for some compact open
  `K_M`, and this forces `χ = 1` on `A_M ∩ K_M`. So the open-kernel field of
  `IsJacquetExponent` excludes nothing, and `Exp(ρ_(P_B))` is exactly the set of
  `χ` with `T.IsJacquetExponent B ρ χ`. Waldspurger's normalization of `π_P`
  is the Library's.
- **Chamber.** On a block scalar the simple root between blocks `j` and `j+1`
  takes the value `a_j / a_(j+1)`. So `Ā_0^+ ∩ A_M` is the `Monotone` set
  `|a_1| ≤ ⋯ ≤ |a_k|`. Writing `|χ(a)| = q^(-⟨Re χ, H_M(a)⟩)`, the condition
  `Re(χ) ∈ +ā_P^(G*)` is equivalent to `|χ(a)| ≤ 1` on this set. It includes
  the central elements and their inverses, which give the component `z = 0`
  of `Re(χ)` on `a_G^*`.
- **Silberger's convention.** S78 p.96 defines `A^+` by `⟨α, H(a)⟩ ≥ 0`, which
  is `|α(a)| ≥ 1`, and p.97 takes exponents from the normalized Jacquet module of
  the opposite parabolic `P̄`. A block-reversing permutation transports this to
  the upper Jacquet modules and the `Monotone` chamber. This conversion is
  written out in the published source map `notes/jacquet/source-map.md`,
  subsection "Block form of the exponent conditions (derived)". S78's
  exponents are the characters by which `A` acts on the irreducible
  subquotients of the Jacquet module. For the finite-length Jacquet module of an
  irreducible representation these are its generalized eigencharacters.

## The analytic definition (derived)

Silberger and Waldspurger define temperedness by the weak inequality
`|f| ≤ c Ξ (1 + σ)^r`. The Lean statement uses the `L^(2+ε)` definition. For an
admissible `ω`-representation of `GL_n(F)` the two agree. One direction of the
Lean statement goes from the exponent bound to the weak inequality by
Waldspurger's (iii) ⇒ (i), and then to `L^(2+ε)`. The other goes from `L^(2+ε)`
directly to the exponent bound. The intended route for the two analytic steps
is as follows. It is not formalized here.

The centre `Z` of `GL_n(F)` is the group of scalar matrices, which is Waldspurger's
`A_G`. So `G ⧸ Z` is his `A_G \ G`.

- **Weak inequality implies `L^(2+ε)`.** If `V = 0` both sides hold. Otherwise,
  Waldspurger's (i) ⇒ (ii) at `P = G` makes the exponent `ω` unitary, so `ω`
  defines a `UnitaryCentralCharacter ρ`, and every `|c|` is `Z`-invariant. `Ξ`
  is also `Z`-invariant. Bound `|c|` by `c Ξ(1 + σ)^r` and use the Cartan
  decomposition, with representatives `m` whose `H_0(m)` lies in a fixed
  complement of `a_G`. By Lemma II.1.1, p.251 (`Ξ ≤ C δ_0^(1/2)(1 + σ)^d` on
  `M̄_0^+`) and formula (5), p.241, the integral of `|c|^(2+ε)` is bounded by a
  constant times `Σ_H q^(-(ε/2)⟨2ρ_0, H⟩)(1 + |H|)^(r')`. Here `H` runs over the
  lattice points of the closed positive chamber modulo `a_G`. This series
  converges, because `⟨2ρ_0, H⟩ ≥ c|H|` there. This is the argument of
  Lemma II.1.5, p.252, with the exponent `2 + ε` in place of `2`. The
  coefficients are locally constant, so they are measurable.
- **`L^(2+ε)` implies the exponent bound.** Assume every coefficient is in
  `L^(2+ε)` for every `ε > 0`. If `V = 0` there are no exponents. Otherwise the
  unitary central character agrees with `ω`, so `|ω| = 1`. For an exponent `χ` along `P = P_B`, the first step of
  Waldspurger's proof of (i) ⇒ (ii), p.266 (from §I.2 and Theorem I.4.1, p.245),
  gives `v`, `v̌` and `ε_0 > 0` with `χ(a) = δ_P(a)^(-1/2) ⟨π(a) v, v̌⟩` for
  every block scalar `a` with `|α(a)| < ε_0` for all `α ∈ ∆(P)`. For a compact
  open `K_1`, normal in `K`, that fixes `v` and `v̌`, the double cosets
  `K_1 a K_1 Z` for chamber elements `a` that are distinct modulo `A_M(O) Z` are
  disjoint, by the Cartan decomposition. On each of them `|c_(v,v̌)|` is
  constant, equal to `δ_P(a)^(1/2) |χ(a)|`. Each has measure at least
  `c δ_0(a)^(-1)`, by the coset count of formula (5) divided by `[K : K_1]^2`,
  and `δ_0(a) = δ_P(a)` on block scalars. So `Σ_a δ_P(a)^(ε/2) |χ(a)|^(2+ε)` converges. If `⟨Re χ, H⟩ < 0` at
  some lattice point `H` of the open cone, the terms along the multiples of `H`
  do not tend to zero for small `ε`, which is a contradiction. So `Re χ ≥ 0` on
  the open cone, hence on its closure, and `Re χ` vanishes on `a_G` because
  `|ω| = 1`. This is `|χ(a)| ≤ 1` on the `Monotone` set.

Both steps use the Haar measure only through left invariance and the counting of
cosets in formula (5), so they apply to each Borel Haar measure `μ`. For the
direction from left to right, a Borel Haar measure exists
(`T.exists_isHaarMeasure_centralQuotient`). No Haar uniqueness is needed.

## Further derived choices

- **The `ω`-hypothesis is needed.** Waldspurger's criterion holds for every
  admissible representation. Worker 23's predicate, following Kudla, also
  demands one unitary central character. Without the `ω`-hypothesis the
  statement would be false: for two tempered irreducible representations with
  different unitary central characters, the direct sum satisfies the exponent
  condition but has no single central character. For `V ≠ 0`, `ω` is determined
  by `ρ`.
- **Zero carrier allowed.** For `V = 0` the left side holds with the trivial
  central character, and the right side holds because the Jacquet modules are
  zero and there are no exponents. So no `Nontrivial V` hypothesis is needed,
  unlike the strict square-integrability criterion
  `GLSquareIntegrableExponentCriterionStatement`, whose unitarity condition is
  listed separately.
- **Domain.** S78 states the criterion for irreducible representations and S79
  states it for functions. Waldspurger's form holds for every admissible
  representation, and the Lean statement assumes only admissibility and the
  `ω`-hypothesis.
- **Positive rank.** `0 < n`, as in the other `GL_n` statements of this family.

Illustration, not stated or proved in Lean: along the upper Borel subgroup of
`GL_2`, the Steinberg representation has the single exponent `|a_1 / a_2|^(1/2)`,
which is at most one on `|a_1| ≤ |a_2|`. The trivial representation has
`|a_1 / a_2|^(-1/2)`, which exceeds one when `|a_1| < |a_2|`.

## Not claimed

The definition proves nothing. In particular, none of the following is proved
or assumed:

- Waldspurger's Proposition III.2.2, Silberger's Lemma 4.5.3, or Casselman's
  asymptotic expansion of coefficients;
- the equivalence of the `Ξ` and `L^(2+ε)` definitions of temperedness, or any
  property of Harish-Chandra's `Ξ`;
- that the block scalars exhaust the centre of the block Levi, or that the
  explicit block modulus is the Haar modulus;
- finiteness of the set of exponents, or the decomposition of the Jacquet
  module into generalized eigenspaces;
- independence of the Haar measure in `IsTemperedModCenter`;
- the classification of tempered representations, or the irreducibility of
  tempered induction.

## Lean dependencies

Direct imports are `Langlands.Representation.Classification.Tempered` (for
`T.IsTempered`, Worker 23) and `Langlands.Representation.Exponents.Jacquet` (for
`T.IsJacquetExponent`, Worker 23). Through the latter come the published block
shapes `GeneralLinear.BlockShape` (`Langlands.Group.GL.Blocks`), the normalized
Jacquet module and the block modulus. `IsAdmissible`, `GeneralLinear.scalar`
and `T.normalizedAbs` are published Library definitions.

This pair is authored for the pinned Lean 4.34.0 environment and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
