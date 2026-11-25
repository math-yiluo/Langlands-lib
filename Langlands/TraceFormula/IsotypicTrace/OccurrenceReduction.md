# Isotypy and trace factorization from one local occurrence (abstract form)

Module `Langlands.TraceFormula.IsotypicTrace.OccurrenceReduction`. Internal to the reduction of
`GroupSchemeCuspidalIsotypicTraceFactorizationStatement` to one local occurrence.
It gives the abstract form of Flath 1979, Theorem 1 (printed pp. 179–180): the restriction of
an irreducible representation of a product to one factor is isotypic. It also gives the
analytic trace splitting described in the Markdown of the target statement. It does not use a
Hilbert tensor product or the type I property (Getz–Hahn Theorem 3.10.2, Folland
Theorem 7.17); one local occurrence is a hypothesis instead.

## Setting of the main theorems

* `π : A →* (E →L[ℂ] E)` preserves inner products on a complex Hilbert space `E`.
* `ι : Gv →* A`, where `Gv` is Hausdorff, locally compact, totally disconnected and second
  countable with Borel structure, and every orbit `y ↦ π (ι y) x` is continuous.
* `hsplit`: every `a ∈ A` is `ι y * c` with `c` commuting with every `ι y'`.
* `hirr`: `E` has no closed `A`-invariant subspaces other than `⊥` and `⊤`.
* `ρ` is admissible and irreducible, and `j₀ : V → E` is a nonzero map with
  `j₀ (ρ y x) = π (ι y) (j₀ x)`.
* `μ` is a Haar measure on `Gv`.

## Auxiliary results

* `exists_eq_smul_of_commute`: Schur's lemma for admissible irreducible `ρ`, from
  `admissibleSchur_scalarEndomorphism`.
* `exists_ne_zero_of_isIrreducible`, `exists_inner_ne_zero`: an irreducible representation is
  nonzero; a nonzero vector pairs nontrivially with some summand of a family with dense sum.
* `exists_block_lift`: if `T (k x)` is fixed by some open subgroup for every `x`, then
  `P_W ∘ T ∘ k` factors through the occurrence `j` whose closure is `W`. `lift_equivariant`:
  such a lift inherits the (possibly twisted) equivariance of `P_W ∘ T ∘ k`.
* `integral_commute`, `integral_fixed`: an operator commuting with the local action commutes
  with `X x = ∫ fv y • π (ι y) x ∂μ`, and `X` has `K`-fixed values when `fv` is left
  `K`-invariant (left invariance of `μ`).
* `exists_occurrence_decomposition`: the decomposition of `OccurrenceHilbertSum`, indexed by
  `𝒜` with chosen injective occurrences `J P` and with the Hilbert sum stated for the closures
  of their ranges (`IsHilbertSum.mkInternal`).

## Main theorems

* `isotypic_of_occurrence`: every smooth irreducible `ρ'` with a nonzero equivariant map
  `j : V' → E` is isomorphic to `ρ`. Some summand `W` has `P_W (j x₀) ≠ 0`. The values of
  `P_W ∘ j` have open stabilizers, so `P_W ∘ j = J ∘ Ψ` for a nonzero equivariant `Ψ : V' → V`,
  which is bijective because both representations are irreducible.
* `exists_trace_factorization`: there is `C : (E →L[ℂ] E) → ℂ` such that, for every
  Schwartz–Bruhat `fv`, every `X` with `X x = ∫ y, fv y • π (ι y) x ∂μ`, and every `Y` commuting
  with `π (ι y)`, if `X ∘ Y` is trace class then
  `operatorTrace (X ∘ Y) = Character.distribution μ ρ hρ fv * C Y`. Here `C Y = ∑' P, coef Y P`,
  where `coef Y P` is the scalar by which `P_W ∘ Y` acts on the occurrence `J P`; it exists by
  `exists_block_lift` and Schur's lemma. For a compact open `K` with `fv` bi-`K`-invariant
  (`Hecke.TestFunction.commonCompactOpenBiInvariance`), the compression of `X ∘ Y` to the
  summand has trace `coef Y P * tr(H fv on V^K)` by `operatorTrace_compression_occurrence`.
  Here `H fv` is the Hecke action, compared with `X` by `map_integratedAction`. This trace is
  `Character.distribution` by `Character.distribution_eq_subspace`. Finally
  `operatorTrace_eq_mul_tsum` applies.
* `exists_twisted_trace_factorization`: suppose `Θ : A →* A` and `θv : Gv ≃ₜ* Gv` satisfy
  `Θ (ι y) = ι (θv y)`, and `I : E →L[ℂ] E` is injective with
  `I (π a x) = π (Θ a) (I x)`. Then there is a bijective `Av : V →ₗ[ℂ] V` with
  `Av (ρ y w) = ρ (θv y) (Av w)` and a functional `C` such that, for `X`, `Y` as above, if
  `X ∘ Y ∘ I` is trace class then its trace is `twistedDistribution μ ρ hρ Av fv * C Y`. `Av`
  is the lift of `P_W ∘ I ∘ j₀` for a summand `W` with `P_W (I (j₀ v₀)) ≠ 0`; `I` maps vectors
  fixed by `K` to vectors fixed by `θv(K)`. Its kernel and range are subrepresentations, so `Av`
  is bijective. The block of `Y ∘ I` on each summand lifts to `β` with the same twisted
  equivariance, so `β ∘ Av⁻¹` commutes with `ρ` and `β = c • Av`. The trace computation is as in
  the untwisted case, with `twistedDistribution_apply` and `FiniteRankEnd.trace_eq_subspace`.
