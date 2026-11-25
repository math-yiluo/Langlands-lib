# A quotient of slow growth of a linked real standard module

Lean module: `Langlands.Representation.Archimedean.RealLinkedQuotientGrowth`
(namespace `Langlands.Archimedean`; helper lemmas in
`Langlands.Archimedean.RealLinkedQuotientGrowth`).

This module defines one statement, `RealLinkedQuotientGrowthStatement`. It proves that this
statement and `RealStandardAnnihilatorGrowthStatement` (module `RealStandardAnnihilatorGrowth`)
together imply `RealLinkedStandardQuotientAnnihilatorStatement` (module
`RealLinkedQuotientAnnihilator`). They therefore imply the Library statement
`RealLinkedLanglandsQuotientNotLargeStatement`. Neither growth statement is proved here.

Notation, as in `RealStandardAnnihilatorGrowth`:

- `𝔤 = ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ` and `U = U(𝔤)`.
- `I(ds) = kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`.
- `φ = envelopingAction (realStandardLie n ds)`.
- `U_d = degreeFiltration ℂ 𝔤 d`.

## The statement

```lean
def RealLinkedQuotientGrowthStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n → IsRealLanglandsOrdered ds →
    ¬ IsRealMoeglinUnlinked ds →
      ∃ W : Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
        IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) W ∧ W ≠ ⊤ ∧
        ∃ C : ℝ, ∀ d : ℕ,
          (Module.finrank ℂ ((degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) d).map
            (LinearMap.llcomp ℂ _ _ _ W.mkQ ∘ₗ
              (envelopingAction (realStandardLie n ds)).toLinearMap)) : ℝ) ≤
            C * ((d : ℝ) + 1) ^ (n * (n - 1) - 1)
```

The hypotheses on `ds` are those of `RealLinkedLanglandsQuotientNotLargeStatement`:

- total rank `n`;
- Langlands order (`IsRealLanglandsOrdered`, non-increasing real parts of the exponents);
- two linked Mœglin data (`¬ IsRealMoeglinUnlinked ds`).

The statement asks for a proper `(𝔤, K)`-submodule `W` of `I(ds)` and a constant `C`. Write
`ψ(u) = mkQ ∘ φ(u) : I(ds) → I(ds) / W`; this is `LinearMap.llcomp ℂ _ _ _ W.mkQ` applied to
`φ(u)`. The requirement is `dim ψ(U_d) ≤ C (d + 1)^(n (n - 1) - 1)` for every `d`.

The kernel of `ψ` is the annihilator of the quotient `I(ds) / W`: `ψ(u) = 0` exactly when `u` maps
`I(ds)` into `W`. So `ψ(U_d) ≅ U_d / (U_d ∩ Ann(I(ds) / W))`, and the statement says that
`U / Ann(I(ds) / W)` has Gelfand–Kirillov dimension at most `n (n - 1) - 1`. Since
`ψ(u) = 0` depends only on the action of `u` on `I(ds) / W`, the statement is about the
`U`-module `I(ds) / W`.

## Provenance

This is an internal statement, introduced for the proof of
`RealLinkedLanglandsQuotientNotLargeStatement`. Mathematically it holds with `W = R`,
the largest proper `(𝔤, K)`-submodule, and the exponent `n (n - 1) - 2`, by the following
facts.

- The Langlands quotient `J = I(ds) / R` of a linked standard module is not large. Its
  Gelfand–Kirillov dimension is at most `dim 𝔫 - 1 = n (n - 1) / 2 - 1`.
- `Dim(U / Ann J) = 2 Dim J` (Vogan 1978, Corollary 4.7, printed p. 84).

The first fact is the content of Vogan 1978, Lemma 6.5 and Corollary 6.6 (printed p. 94), after
rearranging the blocks as in Badulescu–Renard 2010, §2. The statement allows any proper `W` and
the weaker exponent `n (n - 1) - 1`, which leaves room for the proof.

## The reduction

`realLinkedStandardQuotientAnnihilator_of_growth : RealStandardAnnihilatorGrowthStatement →
RealLinkedQuotientGrowthStatement → RealLinkedStandardQuotientAnnihilatorStatement`.

Fix `n` and `ds` satisfying the hypotheses. Take `W` and `C` from the second statement and `c > 0`
from the first. The proof shows that some `u` maps `I(ds)` into `W` and acts nonzero. It argues by
contradiction: assume every `u` with `u · I(ds) ⊆ W` acts by `0`.

1. **Rank at least two** (`two_le_of_not_unlinked`). A block contributes at most as many Mœglin
   data as its rank (one for a character block, one or two for an induced block). So
   `realMoeglinData ds` has length at most `n`. A list of length at most `1` is trivially
   pairwise unlinked, so a linked pair forces `n ≥ 2` and `N = n (n - 1) ≥ 1`.
2. **Equal dimensions.** Let `T = llcomp mkQ : End(I(ds)) → Hom(I(ds), I(ds) / W)`, so that
   `ψ = T ∘ φ`. The assumption says `T(φ u) = 0 → φ u = 0`. Since `φ` and `T` are linear, `T` is
   injective on the range of `φ`. Hence `dim T(φ(U_d)) = dim φ(U_d)`
   (`finrank_map_eq_of_injOn`, proved with `LinearMap.domRestrict` and
   `LinearEquiv.ofInjective`). Since `ψ(U_d) = T(φ(U_d))` (`Submodule.map_comp`),
   `dim φ(U_d) = dim ψ(U_d)` for every `d`.
3. **Comparison of growth** (`not_forall_le`). For every `d`,
   `c (d + 1)^N ≤ dim φ(U_d) = dim ψ(U_d) ≤ C (d + 1)^(N - 1)`. Take `d = ⌈C / c⌉₊`. Then
   `c (d + 1) > C`, so `c (d + 1)^N = c (d + 1) · (d + 1)^(N - 1) > C (d + 1)^(N - 1)`. This is
   a contradiction.

`realLinkedLanglandsQuotientNotLarge_of_growth` composes this with the reduction
`realLinkedLanglandsQuotientNotLarge_of_quotientAnnihilator` (module
`RealLinkedQuotientAnnihilator`). The infinitesimal character
hypothesis of that reduction is supplied by `realStandardLie_hasInfinitesimalCharacter` (module
`RealPrincipalSeriesInfinitesimalCharacter`). So the two growth statements imply
`RealLinkedLanglandsQuotientNotLargeStatement`.

## Suggested proof route for the statement

This route is not part of this module and is recorded only as guidance.

- **Adjacent linked characters.** Suppose two position characters at adjacent coordinates
  `p, p + 1` of the principal series form a linked pair, the first with the larger exponent.
  Take for `W` the functions of `I(ds)` whose Fourier coefficients of weight `|j| < k` along the
  rotations `blockRotation n p` vanish, where `k` is the exponent difference. This `W` is a
  `(𝔤, K)`-submodule, since left and right translations commute. The quotient embeds into a
  module induced from a finite-dimensional representation of the `GL_2` block. In the noncompact
  picture on the opposite unipotent radical, of dimension `n (n - 1) / 2 - 1`, right derivatives
  act on such a module by first-order differential operators with polynomial coefficients.
  Counting these operators gives the bound with exponent `n (n - 1) - 2`. One must also check
  that `W ≠ ⊤`.
- **General case.** Choose a linked pair of blocks at minimal distance in `ds`. The blocks between
  them are then unlinked to both. Isomorphisms of standard modules that swap adjacent unlinked
  blocks make the pair adjacent, keeping its order. The linked pairs of a discrete-series block
  with a character block, or of two discrete-series blocks, may be treated through a linked
  pair of position characters of the principal series.

Sources: D. A. Vogan, Gelfand–Kirillov dimension for Harish-Chandra modules, Invent. Math. 48
(1978), 75–98 (PDF page = printed page − 74). A. I. Badulescu and D. Renard, Unitary dual of
`GL(n)` at archimedean places and global Jacquet–Langlands correspondence, Compos. Math. 146
(2010), §2.
