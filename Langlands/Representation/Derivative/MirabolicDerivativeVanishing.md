# Mirabolic representations with vanishing derivatives

Authors: Worker 1024.

This module proves the detection consequence of Bernstein–Zelevinsky,
*Induced representations of reductive p-adic groups I* (BZ77), §3.5: a smooth
representation of the mirabolic group all of whose derivatives vanish is zero.
It also proves the published proposition
`Langlands.Derivative.MirabolicDerivativeDetection`. Both are inputs of the
proof of BZ77 Proposition 3.8 in
`Langlands.Representation.Derivative.MirabolicHighestDerivativePairingProof`.
Throughout, `F` is a p-adic field with topological data `T`, `ψ` is a unitary
additive character, and `uF`, `uV` are independent universes: the field and the
representation space. `mirabolic n F` is `P_(n+1)`, `radical n F` is its
unipotent radical `V_(n+1) ≅ F^n`, and `mirabolicDerivative T ψ n j` is
`Ψ⁻ ∘ (Φ⁻)^j : P_(n+j+1) → GL_n`, with the normalized minus functors of
`MirabolicMinus`.

## Main declarations

```
Langlands.Derivative.Mirabolic.subsingleton_of_forall_mirabolicDerivative T ψ M :
  ∀ Z : SmoothRep.{0, uF, uV} ℂ (mirabolic M F.Carrier),
    (∀ (n j : ℕ) (h : M = n + j),
      Subsingleton ((mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n j).obj Z)) →
    Subsingleton Z

Langlands.Derivative.Mirabolic.subsingleton_of_forall_mirabolicDerivativeOfOrder T ψ :
  ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
    (∀ (k : ℕ) (hk : 0 < k ∧ k ≤ N + 1),
      Subsingleton ((mirabolicDerivativeOfOrder T ψ N k hk).obj A)) →
    Subsingleton A

Langlands.Derivative.Mirabolic.derivativeDetection
  {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
  MirabolicDerivativeDetection.{uF, uV} F T
```

The first states that a smooth representation `Z` of `P_(M+1)` is zero when every
derivative `Ψ⁻ ∘ (Φ⁻)^j`, taken at each splitting `M = n + j` of the rank, is
zero. The second states the same with the derivatives indexed by their order
`k = j + 1`, which is how the Library defines the level. The third has exactly
the type of the published statement `Langlands.Derivative.MirabolicDerivativeDetection`
(module `Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement`):
for every unitary additive character `ψ`, every nontrivial smooth representation
`A` of `P_(N+1)` has `0 < level T ψ A`.

`derivativeDetection` is deliberately not named
`Langlands.Derivative.mirabolicDerivativeDetection`. That exact name belongs to
the module `MirabolicDerivativeDetectionProof` required by the exact proof task
`ed056880-a4dc-4ebf-ad26-9878e508cf6c`, which can state it as a one-line
wrapper of this theorem. The other declarations are listed under "Auxiliary
declarations".

## Provenance

BZ77 §3.5 (printed p. 452) defines the derivatives of a representation of `P_n`
and observes that a representation with all derivatives zero is zero. In the
source this follows from the exact sequences of Proposition 3.2(e) (printed
p. 451), `0 → Φ⁺Φ⁻X → X → Ψ⁺Ψ⁻X → 0`, applied repeatedly. This module does not
use those exact sequences or the plus functors. It iterates the published
one-step result `Langlands.Derivative.Mirabolic.subsingleton_of_psiMinus_phiMinus`
(module `Langlands.Representation.Derivative.MinusVanishing`: on `P_(m+2)`,
`Ψ⁻X = 0` and `Φ⁻X = 0` force `X = 0`) by a descending induction on the rank.
The rank-one case `P_1`, which `MinusVanishing` does not cover, is proved here
directly. The level form is the translation of "nonzero implies some derivative
is nonzero" into the Library's `level`.

## Implemented proof

* `radical_acts_trivially_zero`: `radical 0 F` is a subsingleton group, so each
  `u` equals `1` and acts as the identity.
* `relations_one_eq_bot`: when the radical acts trivially, every generator
  `ρ(u) v - 1(u) v` of the trivial-character relation span is zero, so the span
  is `⊥`.
* `subsingleton_of_psiMinus_zero` (`P_1` boundary): `Ψ⁻ Z` is the coinvariant
  quotient by the trivial-character relations, which are `⊥` on `P_1`. Two
  vectors with equal classes therefore differ by an element of `⊥`
  (`Jacquet.Localization.mk_eq_iff`), so a subsingleton `Ψ⁻ Z` forces `Z` to be
  subsingleton.
* `subsingleton_of_forall_mirabolicDerivative`, by induction on `M`. For
  `M = 0` use the boundary with `n = j = 0`. For `M = m + 1`: `Ψ⁻ Z` is the
  derivative with `(n, j) = (m + 1, 0)`. Every derivative of `Φ⁻_m Z` is a
  derivative of `Z`: after `subst` on `m = n + j`,
  `mirabolicDerivative n j (Φ⁻_(n+j) Z) = mirabolicDerivative n (j + 1) Z` holds
  definitionally, because `phiMinusIterate` applies `Φ⁻` at the largest rank
  first. So the induction hypothesis gives `Φ⁻_m Z = 0`, and
  `subsingleton_of_psiMinus_phiMinus` gives `Z = 0`.
* `subsingleton_rankCast_mirabolicDerivative_congr` moves a vanishing between
  two rank transports `N = n + j` and `N = n' + j'` with `n = n'` and `j = j'`,
  by `subst`.
* `subsingleton_of_forall_mirabolicDerivativeOfOrder`: the order-`(j+1)`
  derivative `mirabolicDerivativeOfOrder N (j + 1)` is, by definition,
  `mirabolicRankCast ⋙ mirabolicDerivative (N + 1 - (j + 1)) j`, and
  `N + 1 - (j + 1) = n` whenever `N = n + j`. The previous item converts the
  hypothesis, and the induction applies.
* `derivativeDetection`: if `level T ψ A = 0`, then `level_eq_zero_iff` makes
  every order-`k` derivative of `A` subsingleton. The previous item makes `A`
  subsingleton, which contradicts `Nontrivial A`.

No normalization bridge is needed: only vanishing of the quotient carriers is
used, and the `|det|^(-1/2)` twists of the normalized minus functors change the
actions, not the carriers.

## Auxiliary declarations

`radical_acts_trivially_zero`, `relations_one_eq_bot`,
`subsingleton_of_psiMinus_zero`, `subsingleton_rankCast_mirabolicDerivative_congr`;
all are in namespace `Langlands.Derivative.Mirabolic`.

## Imports and independence audit

Direct imports: `Langlands.Representation.Derivative.MinusVanishing` and
`Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement`
(which imports `Homogeneity`, `Iteration` and `MirabolicMinus`). The transitive
`Langlands` import closure has 73 public modules besides this one. They cover
groups, local fields and their normalization, harmonic-analysis conductors,
smooth representations and twists, localization and character averaging,
compact orbit means, matrix coefficients, Whittaker characters, and the
elementary Rankin–Selberg lattice and quotient-integral lemmas used by
`MinusVanishing`, plus `Category.Subquotients`. Every imported Lean/Markdown pair
is byte-identical to the Library at `6789e5106aba61566887427750f5444a494d5879`.

Mathematical proof dependencies: the definitions of the minus functors,
derivatives, rank transports and level (`MirabolicMinus`, `Iteration`,
`Homogeneity`); the coinvariant quotient (`Jacquet.Localization`); and the
published, accepted theorem `subsingleton_of_psiMinus_phiMinus` (artifact
`c6026915-8731-45a8-bd21-ef1ac39654b8`, task `2e5183b1-01e9-44fb-b26c-f4521a25c7c7`).
That theorem's own route is direct: vanishing transports the `θ_ψ`-relations to
every coordinate character by Levi conjugation, and character averaging
(`Jacquet.CharacterAveraging`), radical lattice boxes (`MirabolicLatticeBox`)
and finite Fourier inversion kill each vector. No minus-functor exactness (the
published `MinusExactnessStatement` is neither imported nor used), no plus
functor, no `Φ⁺Φ⁻`/`Ψ⁺Ψ⁻` exact sequence, no Haar modulus comparison, and no
consumer result is used.

The Independence exclusions of task `a925b519-9bb9-4927-873e-ad322d41328e` hold.
Neither this module nor its import closure uses: the nonadjacent product
consumer `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`; `TwoSupercuspidalProductStructure`
or parent task `ab61f565-1427-4746-ba77-46097563e962`; any of the excluded
special-head, segment-socle, segment-classification, square-integrability,
exhaustion, existence, coverage, conversion, tempered-uniqueness,
product-irreducibility, socle-commutation or segment Jacquet-formula tasks,
statements or conclusions listed there; Ze80's segment derivative formulas
(§3.5, §9.6), Ze80 4.2, 9.3 or 9.7; or any classification or exhaustion
theorem. A text scan of the 73 imported Lean files finds none of the excluded
declaration names. The only hits are in two imported Markdown files
(`Iteration.md`, `MirabolicMinus.md`), whose independence paragraphs state that
those names are *not* used.
