# Reduction of the regular cuspidal cyclic lift to the spectral comparison (statement)

Module `Langlands.TraceFormula.CuspidalCyclicBaseChangeRegularLiftAnyDegreeReductionStatement`,
namespace `Langlands.TraceFormula`. It contains one proposition definition and no proof:

- `Langlands.TraceFormula.CuspidalCyclicBaseChangeRegularLiftAnyDegreeReductionStatement.{u, uV, uW}`.

The proposition is the implication

`CuspidalCyclicLiftSpectralComparisonStatement.{u, uV, uW} →
  Langlands.BaseChange.RegularNormTraceNonvanishingStatement.{u, u, u} →
  CuspidalCyclicBaseChangeRegularLiftAnyDegreeStatement.{u, uV, uW}`.

In words: the cuspidal cyclic lift with the regular σ-lift identity at the places with one
place above (`CuspidalCyclicBaseChangeRegularLiftAnyDegreeStatement`, module
`Langlands.TraceFormula.CuspidalCyclicBaseChangeRegularLiftAnyDegreeStatement`) follows from
two statements:

- the spectral comparison (`CuspidalCyclicLiftSpectralComparisonStatement`, module
  `Langlands.TraceFormula.CuspidalCyclicLiftSpectralComparisonStatement`): a list of at most one
  cuspidal `T` over `L` with the global properties of the lift, and local identities
  `Σ_j b_j · tr Π_{j,w}(f) = a · tr π_v(f)` at the split places and
  `Σ_j b_j · tr (Π_{j,w}(φ) ∘ A_j) = a · tr π_v(f)` at the places with one place above, with
  `a ≠ 0`;
- the local nonvanishing statement (`RegularNormTraceNonvanishingStatement`, module
  `Langlands.BaseChange.RegularNormTraceNonvanishingStatement`): the character of an irreducible
  admissible representation of `GL_n(F)` is nonzero on some function supported in the regular
  semisimple set, with orbital integrals vanishing at the non-norms and with norm determinants.

The hypotheses and the notation are those of the three statements; their Markdown pages
describe them.

## The universe parameters

The spectral comparison and the target are taken at the same parameters `{u, uV, uW}`: the
universe of the number fields `K`, `L`, of the presentation `D` of `S` and of the presentation
`P` of the lift. The nonvanishing statement, whose parameters `{u, v, uV}` are the universes of
the local field, of the cyclic algebra and of the representation space, is used at a finite
place `v` of `K` for `K_v = v.adicCompletion K : Type u`, `K_v ⊗[K] L : Type u` and the
representation `(D.localComponent v).representation`, whose carrier, a space of functions on the
adelic group of `K`, is in `Type u`. Hence the instance
`RegularNormTraceNonvanishingStatement.{u, u, u}`.

## Why the implication holds

Fix the data of the target and apply the spectral comparison. It gives `k ≤ 1`,
`T : Fin k → CuspidalOperatorRealization L r`, presentations `P j` with the global properties,
and the local identities of its clauses 2 and 3.

1. **The list is not empty.** The place `v₁` splits with cyclic shift action and has a place `w`
   above it. If `k = 0`, clause 2 of the comparison at `v₁` and `w` says
   `0 = a · tr π_{v₁}(f)` for every Schwartz–Bruhat `f` and a Haar measure, with `a ≠ 0`. But
   the character of the irreducible admissible `π_{v₁}` is not zero: on the idempotent of a
   compact open subgroup `J` with `V^J ≠ 0` it is a positive multiple of `dim V^J`. So `k = 1`.
   Put `T := T 0` and `P := P 0`; clauses 1, 2, 3 and 6 of the target are clause 1 of the
   comparison.
2. **Split places (clause 4 of the target).** At a split `v` and `w | v` the comparison gives
   irreducible admissible `Π_w` (the pulled back component of `P` at `w`) and admissible `π_v`
   with `b · tr Π_w(f) = a · tr π_v(f)` for all `f`, with `a ≠ 0`. Two irreducible admissible
   representations with proportional characters, the constant on one side nonzero, are
   equivalent. The proof is that of the linear independence of characters (Bernstein–Zelevinsky
   1976, Proposition 2.19, printed p. 21); its consequence for equal characters is their
   Corollary 2.20 (same page), which is the Library's
   `CharacterSeparation.nonempty_equiv_of_distribution_eq`. On the Hecke algebra of a small
   compact open subgroup `J` the two `J`-fixed spaces are simple modules of finite dimension
   with proportional traces; evaluating at the unit gives `b ≠ 0`, and if the modules were not
   isomorphic, the Jacobson density theorem for their product would give an element acting as
   the identity on the first and as zero on the second, so that `b · dim = 0`.
3. **Places with one place above (clause 5 of the target).** At such a `v`, with `w` the place
   above it, the comparison gives `hπ`, `hP`, a `σv`-intertwiner `A`, `b` and `a ≠ 0` with
   `b · tr (Π_w(φ) ∘ A) = a · tr π_v(f)` on the concordant pairs of `IsRegularSigmaLift`, for all
   Haar measures. The constant of the target is `c := a / b`; it remains to show `b ≠ 0`.
   - The hypotheses of the nonvanishing statement hold for `F := K_v`, `E := K_v ⊗[K] L`,
     `σv := id ⊗ σ` and `n := r + 1 > 0`: `K_v` has characteristic zero, since the number field
     `K` embeds in it; `IsCyclicAlgebra σv l` holds by `cyclicAlgebraBaseChange` (module
     `Langlands.BaseChange.CyclicAlgebraBaseChange`); `π_v` is irreducible by hypothesis.
   - For a Haar measure `μF` on `GL_{r+1}(K_v)`, the nonvanishing statement gives `f` supported
     in the regular semisimple set, with orbital integrals vanishing at the non-norms, with norm
     determinants and with `tr π_v(f) ≠ 0`. Regular transfer (the Library's `regularTransfer`,
     a proof of `RegularTransferStatement`; Henniart–Lemaire 2011, I.2.5, printed pp. 17–18)
     gives, for a Haar measure `μE` on `GL_{r+1}(K_v ⊗[K] L)`, a function `φ` supported in the
     `σv`-regular set and concordant with `f`.
   - For this pair the identity reads `b · tr (Π_w(φ) ∘ A) = a · tr π_v(f) ≠ 0`, so `b ≠ 0`.

   Hence `c = a / b ≠ 0`, and dividing the identity by `b` gives
   `tr (Π_w(φ) ∘ A) = c · tr π_v(f)` on all the pairs of `IsRegularSigmaLift`, for all Haar
   measures: `IsRegularSigmaLift σv l π_v hπ Π_w hP A c`.

This module states the implication and does not prove it.

## Provenance

This is derived content. The decomposition follows the end of the proof of the base change
lift in Arthur–Clozel 1989, Chapter 1, §6.3 (printed pp. 55–57): the global identities (6.2)
(printed p. 55) and (6.3) (printed p. 56), with the fibre of Theorem III.3.1 collapsed because
"on the image of the norm, their local characters coincide" (printed p. 57), are the spectral
comparison; reading them at one place, with the nonvanishing of the characters of the given
local components, is the present implication. Henniart–Lemaire 2011, II.6.13 (printed
pp. 129–130), obtain in the same way a nonzero constant at the distinguished place for
concordant pairs with regular support.

Sources: Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
Formula*, Annals of Mathematics Studies 120, Princeton University Press, 1989 (Library source
`arthur-clozel-1989-base-change`): Chapter 1, §6.3 (printed pp. 54–57); Chapter 3, Theorem 3.1
(printed p. 201). Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mémoires de la SMF 124, 2011: I.2.5 (printed pp. 17–18), II.6.13
(printed pp. 129–130). I. N. Bernstein and A. V. Zelevinsky, *Representations of the group
GL(n,F) where F is a non-archimedean local field*, Russian Math. Surveys 31:3 (1976) (Library
source `bernstein-zelevinsky-1976-representations-gln`): Proposition 2.19 and Corollary 2.20
(printed p. 21).
