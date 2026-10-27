# Same-model scalar Fourier cutoff for the early JPSS Lemma 5.5

Author: Worker 252.

`Langlands.RankinSelberg.RankOneExtensionScalarCutoffStatement.{uF,uV}` is a
closed proposition definition. It states the one-coordinate Fourier cutoff
used in the proof of JPSS Lemma (5.5). This module supplies no proof.

## Quantifiers and conventions

The proposition quantifies over:

- every prime `p` and every `F : PadicField.{uF} p`;
- every `ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier` for the
  topology of `F.canonicalTopologicalData`. This is the published continuous
  additive character with values in the unit circle, and the structure
  itself requires it to be nontrivial;
- every supplied
  `ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`.
  This is an actual additive Haar measure `ν.val` satisfying the published
  Fourier self-duality predicate for `ψ`. The proposition does not claim
  that such a measure exists;
- every `t k : ℕ`, including `t = 0` and `k = 0`;
- every independent `V : Type uV` with `AddCommGroup V` and `Module ℂ V`;
- every representation `π` of the actual group
  `GeneralLinear ((1 + (t + 1)) + (k + 1)) F.Carrier`, with hypothesis
  `IsSmooth π`;
- every `ℓ : Whittaker.glFunctionals ψ ((1 + (t + 1)) + k) π`, and every
  `f₂ : (Whittaker.coefficientModel π ℓ).toSubmodule`;
- every `χ : HarmonicAnalysis.Quasicharacter F.Carrier`, the existing type
  `ContinuousMonoidHom F.Carrierˣ ℂˣ`;
- every open set `O ⊆ F.Carrier` with `1 ∈ O`.

The Whittaker predecessor rank is `(1 + (t + 1)) + k`. Its successor is
definitionally the ambient rank `(1 + (t + 1)) + (k + 1)`, so `ℓ` is a standard
`ψ`-Whittaker functional on the same `π`. The published smoothness predicate
says that an open subgroup fixes each vector. There is no topology, norm or
finite-dimensionality on `V`, and no irreducibility, admissibility,
Whittaker-type or nonzero-functional premise. A zero `ℓ` and its zero
coefficient model are included.

After `ψ` and `ν`, the proposition installs exactly the topology, the
valuative relation and the local-field certificate of
`F.canonicalTopologicalData`, and the Borel σ-algebra `borel F.Carrier` of that
topology with its `BorelSpace` certificate. This is the measurable space under
which `ν.val` is an `AdditiveHaarMeasure`. The general linear group has
Mathlib's existing topology on matrix units over this field topology. The
units `F.Carrierˣ` have Mathlib's units topology. The absolute value is the
published `normalizedAbsoluteValue F.canonicalTopologicalData`, the absolute
value normalized by the residue cardinality.

## Exact conclusion

There exist a set `U : Set F.Carrier`, two functions
`κ Φ : HarmonicAnalysis.SchwartzBruhat F.Carrier`, and one coefficient
`f₁ : (Whittaker.coefficientModel π ℓ).toSubmodule` in the same model as
`f₂`. Write `B(m,x,a)` for
`rankOneExtensionEmbeddedLowerBlock t k m x a` and `S(u)` for
`rankOneExtensionSmearingUnipotent t k u`. These data satisfy all of the
following.

1. `U` is compact and open, `U ⊆ O`, `1 ∈ U`, `0 ∉ U`, and the normalized
   absolute value of every element of `U` is `1`.
2. `Φ 0 = 0`. For every unit `a`, `Φ a = (χ a)⁻¹` when `(a : F.Carrier) ∈ U`
   and `Φ a = 0` otherwise. Since every nonzero field element is a unit,
   this determines `Φ` completely.
3. For every `b : F.Carrier`,
   `Φ b = HarmonicAnalysis.fourierIntegral ψ ν.val κ b`. The published
   `fourierIntegral` is `∫ x, ψ(x * b) * κ x ∂ν.val.measure`, with the plus
   sign. Both `κ` and `Φ` are actual Schwartz–Bruhat functions, that is,
   locally constant and compactly supported. The Fourier relation is a
   conclusion, not a premise.
4. For every `h` in the whole ambient group, the scalar function
   `u ↦ κ u * f₂(h * S(u))` is integrable for `ν.val.measure`, and `f₁(h)` is
   its Bochner integral. This global formula determines the one coefficient
   `f₁`, including away from the embedded lower blocks.
5. For every `m : GeneralLinear (t + 1) F.Carrier`, every row
   `x : Fin (t + 1) → F.Carrier` and every unit `a`,
   `f₁(B(m,x,a)) = Φ(a) * f₂(B(m,x,a))`.
6. For every `m`, `x` and unit `a` with `(a : F.Carrier) ∈ U`,
   `f₂(B(m,x,a)) = f₂(B(m,x,1))`.
7. Consequently, for every `m`, `x` and unit `a`,
   `f₁(B(m,x,a)) = (χ a)⁻¹ * f₂(B(m,x,1))` when `(a : F.Carrier) ∈ U`, and
   `f₁(B(m,x,a)) = 0` otherwise.

Here `f.val.val` evaluates the actual coefficient-image function. The set
`U` may depend on `f₂`, `χ` and `O`. Conclusion 6 is required only for this
chosen `U`, not for an arbitrary given neighborhood. Conclusion 7 follows
from 2, 5 and 6; it is stated explicitly for later use.

`B(m,x,a)` is the published embedded lower block, `diag([m, 0; x, a], I_(k+1))`.
The row `x` is unscaled, and the scalar entry has zero-based index `t + 1`.
`S(u)` is the published transvection `I + u E_(t+1,t+2)` into the first trailing
coordinate. It is the only smearing direction. The published lemma
`rankOneExtensionEmbeddedLowerBlock_mul_smearing_pairing` computes the
corresponding entry of `B(m,x,a) * S(u)` as `a * u`. That is the plus-sign
pairing of conclusions 3 and 5. The trailing rank `k + 1` is always positive,
so the first trailing coordinate exists. The ambient rank is at least `3`.

The proposition introduces no Jacquet functional, quotient measure,
multiplicative Haar measure, zeta integral or Laurent span. It prescribes no
multiplicative volume for `U`. It does not use the rectangular
`UnequalRankFourierSmearingStatement` as a hypothesis, and it does not assume
any cutoff identity.

## Source and derived scope

The original is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464:

- registered literature ID: `jpss-1983-rankin-selberg`;
- retained file:
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`;
- SHA256:
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

The proof of Lemma (5.5), printed pages 424–427 (one-based PDF pages 59–62),
was rendered and read, including the displayed matrices. No erratum for this
source was found in the project literature index or in the published notes.

In the source, `σ = Ind(σ₁, σ₂)` with `σ₂` a quasicharacter, `m ∈ G_(t₁)`,
`t = t₁ + 1` and `π` a representation of `G_r`. In Lean, `t₁ = t + 1`,
the source rank `t` is `1 + (t + 1)`, `r = (1 + (t + 1)) + (k + 1)`, so
`r - t = k + 1`, and `σ₂` is `χ`. The source's `W₂ ∈ 𝒲(π; ψ)` is `f₂`, and its
`W` is `f₁`. Both lie in the same Whittaker model, here the same
`coefficientModel π ℓ`.

On printed page 426, formula (9) asserts that for `ε > 0` and `W₂` there is
`W` with `W(B(m,x,a)) = W₂(B(m,x,a)) σ₂⁻¹(a)` if `|a - 1| < ε` and `0`
otherwise. The proof takes `φ₁ ∈ 𝒮(F)` with `φ̂₁(a) = σ₂⁻¹(a)` if `|a - 1| < ε`
and `0` otherwise, and sets `W(g) = ∫ φ₁(u) W₂(g S(u)) du`. The display at the
top of printed page 427 then gives `W(B(m,x,a)) = W₂(B(m,x,a)) φ̂₁(a)`, "whence
the relation (9)". The right side of (9) prints the trailing identity block as
`1`, while page 427 prints `1_(r-t)`. Both are read as the rank `r - t`
identity block. In this proposition `κ` is the source's `φ₁` and `Φ` is
`φ̂₁`. Conclusions 2–5 transcribe this construction. The source's derivation
uses `W₂(B(m,x,a) S(u)) = ψ(a u) W₂(B(m,x,a))`, so its `φ̂₁` is the plus-sign
transform matching `fourierIntegral`.

Two parts are derived internal formulations. First, the source's
neighborhood `|a - 1| < ε` is replaced by a compact open `U` inside an
arbitrary open neighborhood `O` of `1`. The conditions `0 ∉ U` and absolute
value one on `U` are stated explicitly; the source obtains them from small
`ε`. Integrability and the global integral formula for `f₁` are stated
explicitly, as is membership of `f₁` in the original coefficient image.

Second, both printed (9) and the display at the top of page 427 keep the
scalar entry `a` inside `W₂`. They do not replace `W₂(B(m,x,a))` by
`W₂(B(m,x,1))`. Conclusions 6 and 7 are a refinement that the source uses
only implicitly. The source deduces `Ψ(s, W, W_f; 0) = Ψ(s, W₂, W₁; 1)` from
(9) and (8). That integral comparison needs `W₂(B(m,x,a))` to be independent
of `a` for `a` near `1`. This refinement chooses `U` small enough for the
given `f₂`, using uniform right smoothness under the scalar diagonal, and it
is not a transcription of formula (9). Printed page 425, formula (7), makes
the analogous smallness choice for the compact section. The normalization of
the multiplicative volume of `U`, needed in that later comparison, is left
to separate statements.

A possible proof, offered only as a route, runs as follows. A continuous
quasicharacter of `F.Carrierˣ` is locally constant, so the cut-off inverse
character on a compact open `U` is Schwartz–Bruhat. Self-duality of `ν`
supplies `κ` as a reflected Fourier transform of `Φ`. The published generic
helper `Langlands.RankinSelberg.Smearing.exists_coefficient_average` gives
conclusion 4. The identity `B(m,x,a) S(u) = (I + a u E_(t+1,t+2)) B(m,x,a)` and
Whittaker covariance give conclusion 5. The factorization of `B(m,x,a)` as
`B(m,x,1)` times the diagonal matrix with `a` at the scalar coordinate, together
with smoothness of a preimage vector of `f₂`, gives conclusion 6. None of these
facts is assumed by the proposition.
