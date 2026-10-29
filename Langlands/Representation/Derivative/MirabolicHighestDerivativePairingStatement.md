# Highest derivatives of nondegenerate mirabolic pairings

This module states Bernstein–Zelevinsky (1977), Proposition 3.8, for the
actual derivative functors of the Library. Two smooth complex representations
`A` and `B` of the mirabolic group `P_(N+1)` are paired by a form with
determinant covariance that is nondegenerate in `A`. If `k` is the highest
order at which `A` has a nonzero derivative, the statement asserts an
invariant pairing of the order-`k` derivatives of `A` and `B` that is
nondegenerate in the derivative of `A`. The module contains one Prop-valued
definition and proves nothing.

## Source and provenance

The registered original `bernstein-zelevinsky-1977-induced-i`,
I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`, was read
at these places:

- Proposition 3.8, printed p.453 (one-based PDF page 14). For `τ, π ∈ Alg P_n`
  with a `Δ`-pairing `B` of `τ` and `π` that is nondegenerate with respect to
  `τ`, and `τ^(k)` the highest derivative of `τ`, it asserts a `1`-pairing of
  `τ^(k)` and `π^(k)` that is nondegenerate with respect to `τ^(k)`.
- The definition of a `χ`-pairing, end of §3.6, printed p.452 (PDF page 13):
  a bilinear form `B` on `E_1 × E_2` with
  `χ(g) · B(π_1(g)ξ_1, π_2(g)ξ_2) = B(ξ_1, ξ_2)`.
- Nondegeneracy and `Bil`, top of printed p.453 (PDF page 14): `B` is
  nondegenerate with respect to `π_1` when the corresponding morphism from
  `π_1` to the contragredient of the whole twist `χπ_2` is an embedding, and
  `Bil` uses `χ = Δ = Δ_G`. In the source the contragredient sign covers the
  product `χπ_2`, and §1.5, printed p.443 (PDF page 4), notes that the
  contragredient of `θπ` is `θ⁻¹π̃`. So the target of this morphism is
  `χ⁻¹π̃_2`, not `χπ̃_2`.
- Twists of contragredients, §1.5, printed p.443 (PDF page 4): for a character
  `θ` and `π ∈ Alg G`, the contragredient of `θπ` is `θ⁻¹π̃`.
- Derivatives and highest derivatives, §3.5, printed p.452 (PDF page 13):
  `τ^(k) = Ψ⁻(Φ⁻)^(k-1)(τ) ∈ Alg G_(n-k)` for `k = 1, …, n`, and `τ^(k)` is the
  highest derivative when `τ^(k) ≠ 0` and `τ^(m) = 0` for `m > k`.
- The module of a group, §1.7, printed p.444 (PDF page 5): `mod_U σ` is defined
  by `∫ f(σ⁻¹(u)) dμ = mod_U σ · ∫ f dμ`, `mod_G(g)` is the module of
  `u ↦ gug⁻¹`, and `Δ_G = mod_G⁻¹`. The localization functor of §1.8(b) on
  the same page uses the factor `mod_U^(-1/2)`.

The statement and pairing definitions were also checked visually on the PDF
pages. §§3.2–3.4, printed pp.450–452, and Proposition 3.7, printed p.453,
were read for the proof plan only. No applicable erratum was found in the
project literature index or among the registered sources.

The order wrapper `mirabolicDerivativeOfOrder`, the determinant character, and
the encoding of nondegeneracy below are Library packaging of these source
notions; the translations are explained in the following sections.

## The principal declaration

```lean
def MirabolicHighestDerivativePairingStatement.{uF, uV, uW} {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (N : ℕ)
    (A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier))
    (B : SmoothRep.{0, uF, uW} ℂ (mirabolic N F.Carrier))
    (k : ℕ) (hk : 0 < k ∧ k ≤ N + 1),
    Nontrivial ((mirabolicDerivativeOfOrder.{uF, uV} T ψ N k hk).obj A) →
    (∀ (j : ℕ) (hj : 0 < j ∧ j ≤ N + 1), k < j →
      Subsingleton ((mirabolicDerivativeOfOrder.{uF, uV} T ψ N j hj).obj A)) →
    ∀ β : InvariantBilinear.forms A.representation B.representation
        (fun g => ((((T.determinantNorm (N + 1)) g.val : ℝ≥0) : ℝ) : ℂ)),
      (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
      ∃ γ : InvariantBilinear.forms
          ((mirabolicDerivativeOfOrder.{uF, uV} T ψ N k hk).obj A).representation
          ((mirabolicDerivativeOfOrder.{uF, uW} T ψ N k hk).obj B).representation
          (fun _ => (1 : ℂ)),
        ∀ v : (mirabolicDerivativeOfOrder.{uF, uV} T ψ N k hk).obj A,
          (∀ w : (mirabolicDerivativeOfOrder.{uF, uW} T ψ N k hk).obj B,
            γ.val v w = 0) → v = 0
```

It lives in namespace `Langlands.Derivative`, with `GeneralLinear` and
`HarmonicAnalysis` open. It imports the published
`Langlands.Representation.Derivative.Homogeneity`, which supplies
`mirabolicDerivativeOfOrder`, and
`Langlands.Representation.Filtration.InvariantBilinear`, which supplies
`InvariantBilinear.forms`. No definition is copied or redefined.

## Parameters and independent universes

The outer parameters are `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p`
and `T : F.TopologicalData`. The supplied topology `T.topology` is installed
for the whole proposition. Everything else is quantified inside the
proposition:

- every `ψ : UnitaryAdditiveCharacter F.Carrier`; nontriviality of `ψ` is part
  of this Library type, and no further condition on `ψ` is imposed;
- every `N : ℕ`; `mirabolic N F.Carrier` is the actual matrix subgroup
  `P_(N+1)` of `GL_(N+1)`, so the source's `n` is `N+1`;
- every `A : SmoothRep.{0,uF,uV} ℂ (mirabolic N F.Carrier)` and every
  `B : SmoothRep.{0,uF,uW} ℂ (mirabolic N F.Carrier)`;
- every derivative order `k` with `hk : 0 < k ∧ k ≤ N+1`.

The three universe parameters are the field universe `uF` and the carrier
universes `uV` of `A` and `uW` of `B`. The carriers of `A` and `B` are in the
independent universes `Type uV` and `Type uW`; they are not required to be
equal. Each derivative is instantiated in the universe of its own argument:
`mirabolicDerivativeOfOrder.{uF,uV}` for `A` and
`mirabolicDerivativeOfOrder.{uF,uW}` for `B`.

## Actual derivatives and highestness

The published `mirabolicDerivativeOfOrder T ψ N k hk` is a functor from
`SmoothRep ℂ (mirabolic N F.Carrier)` to
`SmoothRep ℂ (GeneralLinear (N+1-k) F.Carrier)`. It is the published
`mirabolicDerivative T ψ (N+1-k) (k-1)`, that is `k-1` successive `Φ⁻`
functors followed by `Ψ⁻`, preceded by the rank transport along
`N = (N+1-k)+(k-1)`. This is the source's `τ ↦ τ^(k)` with values in
`Alg G_(n-k)`, `n = N+1`. No exactness is built into this functor, and none is
assumed here. Write `D_j A` for the object
`(mirabolicDerivativeOfOrder T ψ N j hj).obj A`.

The source's highest derivative condition, `τ^(k) ≠ 0` and `τ^(m) = 0` for all
`m > k`, is stated on carriers:

- `Nontrivial (D_k A)`: the order-`k` derivative of `A` has a nonzero vector;
- for every `j` with `hj : 0 < j ∧ j ≤ N+1` and `k < j`,
  `Subsingleton (D_j A)`: every valid higher derivative of `A` is zero.

Only valid orders `j ≤ N+1` occur, as in the source, where derivatives are
defined for `k = 1, …, n`. The statement does not use the Library's `level`
function, so its numerical totalization plays no role.

No nontriviality or highestness condition on `B` is a premise. Nontriviality
of `D_k B` nevertheless follows from the asserted conclusion. If `D_k B` were
zero, every bilinear form `γ` on `D_k A × D_k B` would vanish identically. Left
nondegeneracy of `γ` would then force every vector of `D_k A` to be zero,
contradicting `Nontrivial (D_k A)`. So the full proposition implies that
`D_k B` is nonzero whenever its hypotheses hold. Highestness of `B` is neither
assumed nor concluded: `B` may have nonzero derivatives at orders above `k`.
The source likewise asserts nothing about `π^(k)` being highest.

## Source pairing and the covariance inversion

`InvariantBilinear.forms ρ σ χ` is the actual submodule of bilinear maps
`β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ` with simultaneous covariance

```
β (ρ g v) (σ g w) = χ g * β v w   for all g, v, w.
```

The source's `χ`-pairing instead satisfies `χ(g) · B(π_1(g)v, π_2(g)w) = B(v,w)`.
Thus a source `χ`-pairing is a Library form with covariance `χ⁻¹`.

The hypothesis of Proposition 3.8 is a `Δ`-pairing on `P_n`, with
`Δ_P = mod_P⁻¹`. For `h ∈ P_n`, `mod_P(h)` is the module of the inner
automorphism by `h`. On `P_n = G_(n-1) ⋉ V_n`, with `G_(n-1)` unimodular and
`G_(n-1)` acting on `V_n ≅ F^(n-1)` by matrix multiplication, this module is
`|det h|`, where `det h` is the determinant of `h` as an element of `GL_n`.
Hence `Δ_P = |det|⁻¹`, and the source hypothesis
`Δ_P(g) · B(τ(g)v, π(g)w) = B(v,w)` becomes

```
β (A g v) (B g w) = |det g| * β v w.
```

This is why the Library covariance is `+1` in `|det|`: the source exponent
`-1` and the inversion between the two conventions cancel. In Lean the
character is `fun g => ((((T.determinantNorm (N + 1)) g.val : ℝ≥0) : ℝ) : ℂ)`,
the residue-normalized absolute value of the determinant of the underlying
matrix `g.val ∈ GL_(N+1)`, coerced from `ℝ≥0ˣ` to `ℂ`. The identification of
`Δ_P⁻¹` with this determinant character is the explanation above of the
source convention; it is not a Lean theorem used or proved here.

The conclusion concerns the target group `GL_(N+1-k)`, which is unimodular,
so the source's `Δ` there is trivial. The source writes the conclusion as a
`1`-pairing. Its Library form has covariance `fun _ => (1 : ℂ)`: an ordinary
invariant form `γ (D_k A g v) (D_k B g w) = γ v w`. It is not a modular
pairing at the target rank, and there is no determinant twist in the
conclusion.

## Nondegeneracy

The source calls a `χ`-pairing nondegenerate with respect to `π_1` when the
corresponding morphism from `π_1` to the contragredient of `χπ_2` is an
embedding. On printed p.453 the contragredient sign covers the whole product
`χπ_2`. By §1.5, printed p.443, this contragredient is `χ⁻¹π̃_2`. The morphism
is `f(v) = (w ↦ B(v,w))`. The covariance `χ(g) · B(π_1(g)v, π_2(g)w) = B(v,w)`
gives `f(π_1(g)v) = χ(g)⁻¹ · π̃_2(g) f(v)`, so `f` intertwines `π_1` with
`χ⁻¹π̃_2`. The smooth contragredient is a subspace of the full linear dual, so
injectivity of `f` says exactly that a vector pairing to zero with every
vector is zero. The character twist on the target does not affect this
injectivity condition. The statement uses this left nondegeneracy on both
sides:

- hypothesis: `∀ v : A, (∀ w : B, β.val v w = 0) → v = 0`;
- conclusion: `∀ v : D_k A, (∀ w : D_k B, γ.val v w = 0) → v = 0`.

The nondegeneracy is not weakened to `β ≠ 0` or `γ ≠ 0`. No nondegeneracy in
the second factor is assumed or asserted. The conclusion asserts the
existence of an actual form `γ` in the covariance-one form space; it does
not state how `γ` is obtained from `β`.

## Boundary ranks

Every `N` and every valid `k` are included.

- `N = 0`: `mirabolic 0 F.Carrier` is `P_1`. The only valid order is `k = 1`.
  By the published `mirabolicDerivativeOfOrder_zero_one`, `D_1` is then the
  functor `Mirabolic.psiMinus T 0` from `P_1` to `GL_0`. The higher-order
  hypothesis is vacuous because no `j` satisfies `1 < j ≤ 1`.
- `k = 1` for general `N`: by the published `mirabolicDerivativeOfOrder_one`,
  `D_1` is `Mirabolic.psiMinus T N`, the source's `Ψ⁻`. Highestness requires
  every derivative of `A` of order `2, …, N+1` to be zero.
- Top order `k = N+1`: the target is `GL_(N+1-(N+1))`. The published
  `mirabolicDerivativeOfOrder_top` identifies the functor, after the target
  transport `generalLinearRankCast T (Nat.sub_self (N+1))` to `GL_0`, with
  `mirabolicDerivative T ψ 0 N` after the source transport along `N = 0+N`.
  The higher-order hypothesis is vacuous, so highestness reduces to
  `Nontrivial (D_(N+1) A)`.

There is no derivative of order zero in this mirabolic statement: `0 < k` is
part of `hk`, as in the source's range `k = 1, …, n`.

## Normalization limitation

The Library derivative functors are normalized by explicit determinant
characters: the published `Mirabolic.psiMinus` and `Mirabolic.phiMinus` twist
the localization quotients by `|det|^(-1/2)` on their output groups. The
source's `Ψ⁻` and `Φ⁻` are normalized by `mod_U^(-1/2)` for the Haar module of
the relevant unipotent subgroup, BZ77 §1.8(b). The published definitions
document that the equality of the Haar module with the determinant norm is
a separate proof obligation that they neither prove nor assume.

This statement is about the Library's determinant-normalized derivatives,
and its hypothesis uses the determinant character instead of `Δ_P⁻¹`. The
normalization is not cosmetic: twisting both factors by a character `c`
multiplies the covariance of every form by `c²`, so a covariance-one conclusion
depends on the normalization actually used. The source proof uses
Proposition 3.7, the canonical filtration of §3.5 and §§3.2–3.4,
all for its Haar-normalized functors. The exact proof of this statement must
prove every such comparison or normalization bridge that it uses, for the
actual Library functors and characters. A source equality or citation does
not supply such a bridge.

## What is assumed and what is not

The only hypotheses are those displayed: the order bounds `hk`, the two
highestness hypotheses on `A`, and the left-nondegenerate determinant-covariant
form `β`. There is no assumption of finite length, admissibility,
irreducibility, finite dimensionality, equality of carrier universes,
highestness for `B`, exactness of any functor, a transfer of pairings, or a
selected family of representations. In particular, the published one-sided
`Langlands.Derivative.Mirabolic.PhiMinusPairingTransferStatement`, which
concerns nonzero unnormalized forms under radical generation, is a different
assertion and is not a hypothesis here.

The statement depends only on the two imported published modules and their
dependencies. It does not import or use any downstream product,
classification or segment result.
