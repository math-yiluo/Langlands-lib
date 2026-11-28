# Reduction of the stable cuspidal descent with a trace identity to three statements (statement)

Module `Langlands.TraceFormula.CyclicStableCuspidalDescentTraceIdentityReductionStatement`,
namespace `Langlands.TraceFormula`. It contains one proposition definition and no proof:

- `Langlands.TraceFormula.CyclicStableCuspidalDescentTraceIdentityReductionStatement.{uF, uE, uV, uW}`.

The proposition is the implication

`CyclicStableCuspidalSpectralComparisonStatement.{uF, uE, uV, uW} →
  Langlands.Automorphic.Unramified.WeakBaseChangeFiberNormTraceStatement.{uF, uE, uV, uW} →
  Langlands.BaseChange.TwistedTraceRegularNonvanishingStatement.{uF, max uF uE, uE} →
  CyclicStableCuspidalDescentTraceIdentityStatement.{uF, uE, uV, uW}`.

In words: the weak descent of a `σ`-stable cusp `Π` with the identity
`tr (Π_w(φ) ∘ A) = c · tr π_v(f)` at a place `v` with one place `w` above it
(`CyclicStableCuspidalDescentTraceIdentityStatement`) follows from three statements:

- the spectral comparison at `v` (`CyclicStableCuspidalSpectralComparisonStatement`, module
  `Langlands.TraceFormula.CyclicStableCuspidalSpectralComparisonStatement`): for fixed Haar
  measures, `tr (Π_w(φ) ∘ A) = Σ_i a_i · tr π_{i,v}(f)` over a finite family of cuspidal `π_i`
  of which `Π` is a weak base change;
- the equality of local traces in a fibre (`WeakBaseChangeFiberNormTraceStatement`, module
  `Langlands.Automorphic.Unramified.WeakBaseChangeFiberNormTraceStatement`): two cuspidal
  representations with the same weak base change have the same local traces on test functions
  with determinants in the norm group;
- the nonvanishing of twisted traces on the `σ`-regular set
  (`TwistedTraceRegularNonvanishingStatement`, module
  `Langlands.BaseChange.TwistedTraceRegularNonvanishingStatement`): an irreducible admissible
  representation of `GL_n` over a cyclic algebra with a `σ`-intertwiner has nonzero twisted
  trace on some test function supported in the `σ`-regular set.

## The universe parameters

All four statements are taken at the parameters `{uF, uE, uV, uW}` of the target, except the
nonvanishing statement, whose parameters `{u, v, uW}` are the universes of the local field, of
the cyclic algebra and of the representation space. At `v` these are `F_v = v.adicCompletion F :
Type uF`, `F_v ⊗[F] E : Type (max uF uE)` and the carrier of the local component of `T` at `w`,
a space of functions on the adelic group of `E`, in `Type uE`. Hence the instance
`TwistedTraceRegularNonvanishingStatement.{uF, max uF uE, uE}`.

## Why the implication holds

The argument is steps 6–8 of "Degree at least two" on the page of
`CyclicStableCuspidalDescentTraceIdentityStatement` (Arthur–Clozel 1989, Chapter 1, §6.3(b),
printed p. 57: "By Theorem III.3.1, there are at most ℓ representations on the right-hand side
... On the image of the norm, their local characters coincide. Consequently, we have an equality
at the place `v₃` of the form ... for some constant `c`"), which the spectral comparison leaves
out. Fix the data of the target and write `E_v := F_v ⊗_F E`, `σv := id ⊗ σ`, and `PiV` for
`Π_w` on `GL_n(E_v)`, as in the target.

1. **The comparison.** The spectral comparison gives `k`, cuspidal `S i` over `F` with unitary
   central characters and the class of `T` as weak base change, presentations `D i` with
   irreducible admissible components `π_{i,v}`, admissibility of `PiV`, a `σv`-intertwiner `A`,
   coefficients `a i` and Haar measures `μF⁰`, `μE⁰` with
   `tr (PiV(φ) ∘ A) = Σ_i a i · tr π_{i,v}(f)` for the pairs `(φ, f)` of the target.
2. **The local hypotheses of the nonvanishing statement.** `F_v` has characteristic zero.
   `IsCyclicAlgebra σv l` holds for the `F_v`-algebra `E_v`: base change along the field
   extension `F_v / F` keeps the dimension `l`, the order of `σ` and the fixed algebra
   (`E_v^{σv} = F_v ⊗_F E^σ = F_v`). `PiV` is irreducible because `Π_w` is and
   `GL_n(h) : GL_n(E_v) → GL_n(E_w)` is a group isomorphism, `h` being the bijective
   `w`-component of `finiteTensorMap v` (`w` is the only place above `v`).
3. **A pair with nonzero twisted trace.** The nonvanishing statement, for `F_v`, `E_v`, `σv`,
   `PiV`, `A` and `μE⁰`, gives `φ⁰` supported in the `σv`-regular set with
   `tr (PiV(φ⁰) ∘ A) ≠ 0`. Regular transfer (the Library's `regularTransfer`, a proof of
   `RegularTransferStatement`; Henniart–Lemaire 2011, I.2.5, Proposition, printed p. 18) gives
   `f⁰` concordant with `φ⁰` for `μF⁰`, `μE⁰` and supported in the regular semisimple set.
   Multiplying `f⁰` by the indicator of the open and closed set `det⁻¹(N(E_v^×))` keeps both
   properties, because the orbital integrals of `f⁰` vanish at regular non-norms and the
   determinant of a norm lies in `N(E_v^×)`; this is the cutoff of the module
   `Langlands.BaseChange.SigmaLiftCharacterIdentity.NormDeterminantCutoff`.
4. **Collapse of the sum.** For `(φ⁰, f⁰)` the left side of step 1 is nonzero, so `k ≥ 1`. The
   fibre statement, applied to `S i` and `S 0`, gives `tr π_{i,v}(f) = tr π_{0,v}(f)` for every
   `f` with norm determinants, hence
   `tr (PiV(φ) ∘ A) = c · tr π_{0,v}(f)` with `c := Σ_i a i`, for the measures `μF⁰`, `μE⁰`.
   At `(φ⁰, f⁰)` this shows `c ≠ 0`.
5. **All Haar measures.** Every Haar measure is a positive multiple of a given one:
   `μF = s • μF⁰`, `μE = t • μE⁰`. Concordance for `(μF, μE)` of `(φ, f)` is concordance for
   `(μF⁰, μE⁰)` of `(φ, (s/t) • f)`, and the traces scale by `t` and `s`. So
   `tr_{μE} (PiV(φ) ∘ A) = t · c · tr_{μF⁰} π_{0,v}((s/t) • f) = c · tr_{μF} π_{0,v}(f)`: the
   same `c` serves for all Haar measures (the remark "`c` before the measures" on the page of the
   target).
6. **Conclusion.** `S := S 0` and `D := D 0`, with `A` and `c`, satisfy the target.

This module states the implication and does not prove it.

## Provenance

This is derived content. The decomposition follows the last paragraph of the proof of
Arthur–Clozel 1989, Chapter 1, Theorem 6.2(b) (§6.3, printed p. 57), quoted above: the identity
(6.5) is the spectral comparison, the appeal to Theorem III.3.1 and to the coincidence of the
local characters on the image of the norm is the fibre statement, and the nonvanishing of the
twisted trace of the `σ`-stable local component (used in the source through twisted
pseudo-coefficients) makes the right side nonempty. Henniart–Lemaire 2011, II.6.16–II.6.17
(printed pp. 131–132), follow the same structure over function fields.

Sources: Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
Formula*, Annals of Mathematics Studies 120, Princeton University Press, 1989 (Library source
`arthur-clozel-1989-base-change`): Chapter 1, §6.3 (printed pp. 56–57); Chapter 3, Theorem 3.1
(printed p. 201). Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mémoires de la SMF 124, 2011: I.2.5 (printed pp. 17–18),
II.6.16–II.6.17 (printed pp. 131–132).
