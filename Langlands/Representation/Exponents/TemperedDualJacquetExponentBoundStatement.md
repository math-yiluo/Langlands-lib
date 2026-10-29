# Weak bounds for opposite Jacquet dual exponents of tempered representations

Authors: Worker 728 (Lean statement and first Markdown draft) and Worker 908
(Markdown revision and source checks).

This module states one closed proposition,
`Langlands.GLTemperedDualJacquetExponentBoundStatement.{uF,uV}`. It is a
proposition definition; the module proves nothing about it. The statement is
the necessity half of the exponent criterion for temperedness on `GL_n`, read
through dual eigenfunctionals on normalized opposite Jacquet quotients. The
field universe `uF` and the representation universe `uV` are independent.

## Objects and quantifiers

The statement quantifies every prime `p` (with `Fact p.Prime`), every
`F : PadicField.{uF} p`, every realization `T : F.TopologicalData` of its
topology (the group topology is `T.topology`), every rank `n` with `0 < n`, every
ordered block shape `C = (n_1, …, n_r)` of `n` (`C : GeneralLinear.BlockShape n`,
`r = C.length`; one block and all blocks of size one are both allowed), and every
`A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)`.

The hypotheses on `A` are exactly two.

- `Representation.IsIrreducible A.ρ`.
- `T.IsTempered A.ρ` (module `Langlands.Representation.Classification.Tempered`):
  for every Borel Haar measure on `GL_n(F) ⧸ Z`, the representation is
  admissible, has a unitary central character, and its descended coefficient
  norms lie in `L^(2+ε)` for every `ε > 0`. No Haar measure is fixed.

No unitarity, square-integrability, cuspidal-support or genericity hypothesis is
made.

The conclusion concerns every `ψ : (Fin r → F^×) →* ℂ^×` with
`T.IsDualJacquetExponent C A ψ` (module
`Langlands.Representation.Exponents.DualJacquet`). This means that `ψ` has open
kernel and that the transpose action `T.splitCentreDualJacquet C A` of the block
scalars, on the full algebraic dual of the normalized opposite Jacquet module
`T.splitCentreOppositeJacquet C A` along `C`, has a nonzero `ψ`-eigenvector.

## The bound

For every block scalar `a = (a_1, …, a_r) ∈ (F^×)^r` with
`|a_1| ≥ |a_2| ≥ ⋯ ≥ |a_r|` (the Lean hypothesis
`Antitone (fun i => T.normalizedAbs (a i))`), one has `‖ψ(a)‖ ≤ 1`.

Here `|·|` is the published residue-normalized absolute value `T.normalizedAbs`,
with `|ϖ| = q⁻¹` for a uniformizer `ϖ`. The inequality is weak, and the constant
tuples (in particular the central elements) are not removed.

## Opposite normalization

Write `m(a)` for the block-scalar matrix `diag(a_1 1_(n_1), …, a_r 1_(n_r))`,
`N̄_C` for the lower block unipotent subgroup and `P̄_C` for the opposite of the
standard upper block parabolic `P_C`. The published block modulus on block
scalars is `δ_(P_C)(a) = ∏_(i<j) |a_i / a_j|^(n_i n_j)`, and
`h(a) = T.leviHalfModulus C (m(a)) = δ_(P_C)(a)^(1/2) = δ_(P̄_C)(a)^(-1/2)`.
`DualJacquet.md` documents the proved formulas

```
ρ_J(a) q(v) = h(a) q(A.ρ(m(a)) v),
(ρ_D(a) φ)(w) = φ(ρ_J(a) w),
```

where `q` is the quotient map onto the `N̄_C`-coinvariants. The transpose action
`ρ_D` has no inverse. So the normalized opposite Jacquet module is Waldspurger's
`π_(P̄_C)`, with `π_P(m) j_P(v) = δ_P(m)^(-1/2) j_P(π(m) v)` at `P = P̄_C`.
By `mem_dualJacquet_eigenspace_iff`, a nonzero `ψ`-eigenvector of `ρ_D`
corresponds to a nonzero functional `φ₀` on `A` that is invariant under `N̄_C`
and satisfies

```
φ₀(A.ρ(m(a)) v) = δ_(P̄_C)(a)^(1/2) ψ(a) φ₀(v).
```

This is Silberger's dual exponent with respect to the standard p-pair `(P_C, A_C)`
(see the sources below).

## Prefix form (derived)

The Lean statement uses only the antitone form. Suppose `T.IsRealPartOf ψ s`
(module `Langlands.Representation.Exponents.Jacquet`), that is,
`‖ψ(a)‖ = ∏_i |a_i|^(s_i)` for all `a`, and write `S_i = s_0 + ⋯ + s_i`. Such a
real vector `s` exists for every `ψ` with open kernel: on `(O^×)^r` the kernel
has finite index, so `‖ψ‖` is trivial there and depends only on the valuations.
For an arbitrary real vector `s` the antitone bound is equivalent to the two
conditions `S_i ≤ 0` for every `i` and `S_(r-1) = 0`.

- Every prefix is nonpositive. The tuple equal to `ϖ⁻¹` on the first `i + 1`
  blocks and to `1` afterwards is antitone and has `‖ψ(a)‖ = q^(S_i)`. The
  Library proves this implication as `ScalarLayer.prefix_nonpos_of_antitone_bound`
  (`Classification/TemperedOppositeJacquetScalarLayerAssembly`).
- The total is nonnegative. The constant tuple `(ϖ, …, ϖ)` is antitone and has
  `‖ψ(a)‖ = q^(-S_(r-1))`. With the previous item, `S_(r-1) = 0`.
- Conversely, write `|a_i| = q^(-m_i)`. The tuple is antitone exactly when
  `m_0 ≤ m_1 ≤ ⋯ ≤ m_(r-1)`. Then `‖ψ(a)‖ = q^(-Σ m_i s_i)`, and Abel summation
  gives `Σ_i m_i s_i = m_(r-1) S_(r-1) − Σ_(i<r-1) (m_(i+1) − m_i) S_i ≥ 0`.

Prefix bounds alone do not give the antitone bound. For `r = 1` and `s_0 = −1`
every prefix is negative, but `‖ψ(ϖ)‖ = q > 1`.

Under the hypotheses of the statement the total vanishes automatically. The
scalar matrix `t 1_n` is the block scalar `(t, …, t)`, on which `h = 1`. By the
source eigen-equation, `ψ(t, …, t)` is the central character of `A` at `t`.
`T.IsTempered` makes that character unitary, so `S_(r-1) = 0`. So for dual
exponents of irreducible tempered representations the antitone form is
equivalent to "every prefix sum `S_i` is `≤ 0`". This remark is not formalized in
this module.

## Sign check for `GL_2` (derived)

Take `n = 2` and `C = (1, 1)`, so `a = diag(a_1, a_2)`, `δ_(P_C)(a) = |a_1/a_2|`
and `h(a) = |a_1/a_2|^(1/2)`. Both opposite Jacquet modules below are
one-dimensional. So the dual of each is one-dimensional with the same
character, and the dual exponent is that character.

- **Trivial character.** The `N̄_C`-coinvariants are `ℂ` with trivial action, so
  `ψ(a) = h(a) = |a_1/a_2|^(1/2)`, with real parts `(1/2, −1/2)`. At the antitone
  tuple `a = (ϖ⁻¹, 1)`, `‖ψ(a)‖ = q^(1/2) > 1`. The bound fails, as it must: the
  trivial character of `GL_2(F)` is not tempered, because its coefficients are
  constant and the volume of `PGL_2(F)` is infinite.
- **Steinberg representation `St_2`.** In normalized induction,
  `1 ⊂ I(ν^(-1/2) ⊗ ν^(1/2))` with quotient `St_2`, where `ν = |·|`. The
  normalized upper Jacquet module of `1` is `δ_(P_C)^(-1/2) = ν^(-1/2) ⊗ ν^(1/2)`,
  and that of the induced representation has semisimplification
  `ν^(-1/2) ⊗ ν^(1/2) + ν^(1/2) ⊗ ν^(-1/2)`. So `St_2` has upper exponent
  `|a_1/a_2|^(1/2)`. Conjugation by the antidiagonal Weyl element exchanges `N_C`
  and `N̄_C` and `a_1, a_2`, and it matches `δ_(P̄_C)` with `δ_(P_C)`. So the
  opposite exponent is `ψ(a) = |a_2/a_1|^(1/2)`, with real parts `(−1/2, 1/2)`.
  When `|a_1| ≥ |a_2|`, `‖ψ(a)‖ = (|a_2|/|a_1|)^(1/2) ≤ 1`. The bound holds, as it
  must, since `St_2` is square-integrable modulo the centre, hence tempered.

The prefix sums are `(−1/2, 0)` for `St_2` and `(1/2, 0)` for the trivial
character, in agreement with the prefix form.

## Relation to the upper `Monotone` convention

The published upper criterion `GLTemperedExponentCriterionStatement`
(`Classification/TemperedExponentStatement`) uses the normalized upper Jacquet
module along the standard parabolic `P_B` and the `Monotone` set
`|a_1| ≤ ⋯ ≤ |a_k|`. Its Markdown gives the upper exponent `|a_1/a_2|^(1/2)` of
`St_2` above. The two conventions are related as follows (derived; not stated in
Lean).

- The positive chamber of `P̄_C` is the negative of that of `P_C`. On block
  scalars the simple roots of `P̄_C` take the values `a_(j+1)/a_j`, so the closed
  chamber condition `|α(a)| ≤ 1` for `α ∈ ∆(P̄_C)` is the antitone condition.
- Conjugation by the block-reversing Weyl element maps `P̄_C` onto the standard
  parabolic `P_(C.reverse)`. It sends the block scalar `a` to `a ∘ rev` and
  transports `δ_(P̄_C)` to `δ_(P_(C.reverse))`. So the normalized opposite Jacquet
  module along `C` is the normalized upper Jacquet module along `C.reverse` with
  the block labels reversed. An antitone tuple `a` gives the monotone tuple
  `a ∘ rev`.
- In the Library, for irreducible admissible `A`, a dual exponent `ψ` along `C`
  is a generalized eigencharacter of the opposite Jacquet module
  (`ScalarLayer.isGeneralizedEigencharacter_of_isDualJacquetExponent`). After
  reversal, `ψ ∘ rev` is an upper exponent along `C.reverse`
  (`ScalarLayer.isJacquetExponent_reverse`). The forward direction of the upper
  criterion at `C.reverse` then gives the present bound. The step `hbound'` of
  `glTemperedOppositeJacquetScalarLayer_of_upperBound` carries out this
  derivation. This module imports neither these results nor the upper criterion.

## Original sources

- A. J. Silberger, *Introduction to harmonic analysis on reductive p-adic
  groups*, 1979 (literature ID `silberger-1979-harmonic-analysis`, SHA256
  `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`; PDF page =
  printed page + 6; formula pages checked in rendered page images).
  - §2.4, p.90: for a p-pair `(P, A)` with opposite `(P̄, A)`, if a nonzero
    `φ ∈ V'` and a quasi-character `χ` of `A` satisfy `ᵗπ(n̄)φ = φ` for all
    `n̄ ∈ N̄` and `ᵗπ(a)φ = δ_(P̄)^(1/2)(a) χ(a) φ` for all `a ∈ A`, then `χ` is a
    *dual exponent* of `π` with respect to `(P, A)`. The same page announces that
    Chapter 3, §§1–2, proves that exponents and dual exponents are the same.
    The published source map `notes/jacquet/source-map.md` locates this
    comparison in Lemmas 3.2.1–3.2.2, Theorem 3.2.4 and Corollary 3.2.5(1),
    pp.120–123.
  - §4.5, Lemma 4.5.3, pp.185–186: a coefficient function `f` is tempered if and
    only if `|χ(a)| ≤ 1` for all `a ∈ A^+`, for every p-pair `(P, A)` and every
    exponent `χ` of `f` along `(P, A)`. The inequality is weak. The paragraph
    before Lemma 4.5.6, p.187, identifies the exponents of a nonzero
    coefficient function of an irreducible admissible tempered `π` with those
    of `π` (by Theorem 3.1.1).
- A. J. Silberger, *The Langlands quotient theorem for p-adic groups*, Math.
  Ann. 236 (1978) (literature ID
  `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
  SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`;
  PDF page = printed page − 94; checked in rendered page images).
  - p.96: `A^+` is the set of `a` with `⟨α, H(a)⟩ ≥ 0`, that is `|α(a)| ≥ 1`, for
    the simple roots of `(P, A)`. For a standard block p-pair of `GL_n` this is
    the antitone set.
  - p.97: the class exponents `𝔜_π(P, A)` are the classes `ω` such that
    `δ_P^(-1/2) ω` is the class of a subquotient of the unnormalized opposite
    Jacquet module `ℋ(P̄)`. So they are the subquotients of `ℋ(P̄)` twisted by
    `δ_P^(1/2)`, which is the normalization used here. The set `𝔛_π(P, A)` of
    exponents consists of their central exponents.
  - p.98: an irreducible admissible `π` is tempered if and only if
    `|χ(a)| ≤ 1` for all `a ∈ A^+`, every standard p-pair `(P, A)` and every
    `χ ∈ 𝔛_π(P, A)` (citing S79, Lemma 4.5.3).

  In Silberger's own convention the Lean statement is therefore the "only if"
  direction for the standard p-pairs `(P_C, A_C)` of `GL_n`, with exponents read
  as dual exponents.
- J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
  d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333 (literature
  ID `waldspurger-2003-plancherel`, SHA256
  `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`; PDF page =
  printed page − 234).
  - §I.1, pp.239–240: for `P ∈ 𝒫(M)`, `+ā_P^(G*)` is the set of
    `Σ_(α ∈ ∆(P)) x_α α` with all `x_α ≥ 0`, where `∆(P)` are the simple roots of
    `A_M` positive for `P`. `H_M` is defined by `q^(-⟨χ, H_M(m)⟩) = |χ(m)|_F`.
  - §I.3, p.243: `Exp(π)` is the set of characters with nonzero generalized
    eigenspace, and the Jacquet module of a semi-standard `P` carries
    `π_P(m) j_P(v) = δ_P(m)^(-1/2) j_P(π(m) v)`.
  - Proposition III.2.2, pp.265–266: for admissible `π`, `π` is tempered if and
    only if `Re(χ) ∈ +ā_P^(G*)` for every semi-standard parabolic `P` and every
    `χ ∈ Exp(π_P)`. The direction (i) ⇒ (ii) applies to `P = P̄_C`, which
    contains the diagonal torus and is therefore semi-standard.

## Translation to the Lean statement (derived)

- **Parabolics and exponents.** The split centre `A_M` of the block Levi is the
  group of block scalars. For irreducible admissible `A` the Library shows that a
  dual exponent is a generalized eigencharacter of the opposite Jacquet module
  (lemma cited above), hence an element of Waldspurger's `Exp(π_(P̄_C))`. The
  statement quantifies over dual exponents only, so it is implied by
  Waldspurger's (i) ⇒ (ii) at `P̄_C`. The open-kernel field of
  `IsDualJacquetExponent` corresponds to Silberger's quasi-characters.
- **Chamber.** With `|χ(a)| = q^(-⟨Re χ, H_M(a)⟩)`, the condition
  `Re(χ) ∈ +ā_(P̄_C)^(G*)` is equivalent to `|χ(a)| ≤ 1` on the set where
  `|α(a)| ≤ 1` for all `α ∈ ∆(P̄_C)`, which is the antitone set. The constant
  tuples and their inverses lie in it; they give the vanishing of the central
  component of `Re(χ)`.
- **Temperedness.** The sources define temperedness by the weak inequality
  `|f| ≤ c Ξ (1 + σ)^r`; the Library uses `L^(2+ε)` modulo the centre for every
  Haar measure. Their agreement for admissible representations with a unitary
  central character is explained in the section "The analytic definition
  (derived)" of `Classification/TemperedExponentStatement.md`; it is not
  formalized there or here.

## Scope

The module contains only the proposition definition. It asserts no proof, adds
no axiom and imports only `Exponents.DualJacquet` and `Classification.Tempered`.
It does not state the converse (sufficiency) direction or the prefix form.
