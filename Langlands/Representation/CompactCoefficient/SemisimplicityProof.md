# Semisimplicity of smooth representations with compact coefficients: proof

The theorem `Langlands.compactCoefficientSemisimplicity` proves the published
proposition `Langlands.CompactCoefficientSemisimplicityStatement.{uG, uV} G μ`
of `Langlands.Representation.CompactCoefficient.SemisimplicityStatement`. It
takes exactly the statement's binders: a Hausdorff, locally compact, totally
disconnected, σ-compact topological group `G` with its Borel structure, and a
regular left Haar measure `μ` that is also right invariant. The universes `uG`
of the group and `uV` of the carrier stay independent. The conclusion holds for
every `A : SmoothRep.{0, uG, uV} ℂ G` with
`HasCompactSmoothDualCoefficients A.representation`, with no further
assumption on `A`.

## What the proof actually uses

The proof is elementary. It does not use Schur's lemma, formal degrees, the
projectors of Bernstein–Zelevinsky (1976), Section 2.43, or Theorem 2.42. The
closing theorem applies the general result
`Langlands.CompactCoefficientSemisimplicity.isSemisimpleRepresentation_of_compactCoefficients`
to `A.representation` and its smoothness `A.isSmooth`. That result needs only
a group that is a Hausdorff, locally compact, totally disconnected topological
group with a Borel structure, and a left Haar measure `μ`
(`Measure.IsHaarMeasure`). The hypotheses `SigmaCompactSpace G`,
`Measure.Regular μ` and `Measure.IsMulRightInvariant μ` of the statement are
accepted by the closing theorem but are not used. The representation is any
smooth complex representation `ρ` whose smooth-dual coefficients
`g ↦ ℓ (ρ g v)` all have compact support; the carrier has no topology.

The route is as follows. For a vector `a₀` outside a subrepresentation `M`, a
smooth functional `ℓ` vanishing on `M` gives an intertwiner
\[
  S(v) = \int_G \ell(\rho(g^{-1})v)\,\rho(g)a_1\,d\mu(g)
\]
of `ρ` that kills `M`. Here `a₁` is a vector built from `a₀` and lies in every
subrepresentation that contains `a₀`. A positivity computation shows that
`S a₁ ∉ M`. A Zorn argument then shows that the irreducible subrepresentations
span `ρ`, and Mathlib turns this into complemented subrepresentations.

## Smooth separating functionals

Fix a compact open subgroup `K`. The project's `Compact.averageMap ρ hρ K hK`
sends a vector to the normalized sum over its finite `K`-orbit.

- `averageMap_apply_rho`: replacing `v` by `ρ k v` with `k ∈ K` does not change
  the orbit, so it does not change the average.
- `averageMap_mem`: the average of a vector of a subrepresentation `N` lies in
  `N`, because it is a scalar multiple of a finite sum of orbit vectors
  (`finsum_induction`).

`exists_smooth_dual_separating` takes a subrepresentation `N` and a vector
`a ∉ N`. It returns a functional `ℓ` in the algebraic dual that is a smooth
vector of `ρ.dual`, vanishes on `N` and satisfies `ℓ a ≠ 0`. Smoothness of `ρ`
gives an open subgroup `U` fixing `a`. The published
`Hecke.TestFunction.commonCompactOpenBiInvariance`, applied to the empty family
of test functions, gives a compact open subgroup `K ≤ U`. Mathlib's
`Submodule.exists_le_ker_of_notMem` gives a linear functional `λ` that vanishes
on `N` with `λ a ≠ 0`. The proof takes `ℓ = λ ∘ averageMap`. It is fixed by
`K` under the dual action by `averageMap_apply_rho`, and it vanishes on `N` by
`averageMap_mem`. Finally `ℓ a = λ a`, because `a` is `K`-fixed and the
published `Compact.averageMap_id` applies.

## Test functions and the integrated action

- `coefficientTest ρ hρ hc hℓ` is the complex-linear map sending `v` to the
  test function `g ↦ ℓ (ρ g v)` in `SchwartzBruhat G`. The published
  `Hecke.orbitMap_locallyConstant` gives local constancy, and the hypothesis
  `HasCompactSmoothDualCoefficients ρ` gives compact support.
- `conjTest f` is the pointwise complex conjugate of a test function.
- `integratedAction_mem`: the published integrated action
  `Hecke.integratedAction μ ρ hρ f` preserves every subrepresentation `N`. If
  the image of `v ∈ N` were outside `N`, a functional `L` vanishing on `N`
  would separate it. The published `Hecke.integratedAction_dual` computes
  `L` of the image as `∫ f g * L (ρ g v) dμ`, whose integrand is zero.
- `eq_zero_of_integral_conj_mul_self`: if `F : G → ℂ` is continuous with
  compact support and `∫ conj (F g) * F g dμ = 0`, then `F` is identically
  zero. The integrand is the real function `‖F g‖ ^ 2`
  (`integral_complex_ofReal`). Its integral is positive if `F x ≠ 0` for some
  `x`, by `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`. This
  uses that `μ` is finite on compacts and positive on nonempty open sets.

## The separating intertwiner

`coefficientIntertwiner μ ρ hρ hc hℓ b` is the intertwiner `ρ → ρ` sending `v`
to `Hecke.integratedAction μ ρ hρ (inversion (coefficientTest … v)) b`, that is,
to `∫ ℓ (ρ g⁻¹ v) • ρ g b dμ`. Replacing `v` by `ρ h v` replaces the test
function by its left translate by `h`. The published
`Hecke.integratedAction_leftTranslate`, which uses left invariance of `μ`,
turns this into `ρ h` applied to the output.

`exists_intertwiner_separating` takes a subrepresentation `M` and a vector
`a₀ ∉ M`, and produces an intertwiner `S` and a vector `a₁` such that

1. `S v = 0` for all `v ∈ M`;
2. `a₁` lies in every subrepresentation containing `a₀`;
3. `S a₁ ∉ M`.

Let `ℓ` be a smooth separating functional for `M` and `a₀`. Put
`c g = ℓ (ρ g a₀)` and `a₁ = ∫ conj (c y) • ρ y a₀ dμ(y)`, which is the
integrated action of `conjTest c` on `a₀`. Property 2 is
`integratedAction_mem`. Let `S` be the coefficient intertwiner with `b = a₁`.
If `v ∈ M`, then all coefficients `ℓ (ρ g v)` vanish, so the test function is
zero and `S v = 0`; this is property 1.

For property 3, `Hecke.integratedAction_dual` gives
\[
  k(g) := \ell(\rho(g)a_1) = \int_G \overline{c(y)}\,c(gy)\,d\mu(y).
\]
Left invariance of `μ` (`integral_mul_left_eq_self`, substituting
`y ↦ g y`) together with `integral_conj` gives
`ℓ (ρ g⁻¹ a₁) = conj (ℓ (ρ g a₁))`. Suppose `S a₁ ∈ M`. Then
`ℓ (S a₁) = 0`, and `Hecke.integratedAction_dual` together with this symmetry
rewrites it as `∫ conj (k g) * k g dμ = 0`. The function `k` is the
coefficient test function of `a₁`, so it is continuous with compact support.
Positivity gives `k 1 = 0`, that is `∫ conj (c y) * c y dμ = 0`. Positivity
applied to `c` gives `c 1 = ℓ a₀ = 0`, contradicting the choice of `ℓ`.

## The lattice argument

`sSup_atoms_eq_top_of_separating` holds for a representation of any monoid on a
vector space over any field. Its hypothesis is the conclusion of
`exists_intertwiner_separating` for every `M` and `a₀ ∉ M`, and its conclusion
is that the supremum `s` of the atoms of `Subrepresentation ρ` is `⊤`.
Arbitrary suprema and infima of subrepresentations are those of the published
complete lattice `Langlands.Subrepresentation.instCompleteLattice`
(`Langlands.Representation.SubrepresentationLattice`), computed on the
underlying submodules.

Suppose `s ≠ ⊤` and pick `a₀ ∉ s`. Zorn's lemma (`zorn_le_nonempty₀`) gives a
subrepresentation `M` that is maximal among those `N` with `s ≤ N` and
`a₀ ∉ N`. The family contains `s`. For a chain, the supremum is computed on
submodules as a directed union (`Submodule.mem_sSup_of_directed`), so it does
not contain `a₀`. Apply the hypothesis to `M` and `a₀` to get `S` and `a₁`.
Let `Z` be the infimum of all subrepresentations containing `a₀`, so `a₁ ∈ Z`,
and let `I` be the image of `Z` under `S`, a subrepresentation.

- `I ≠ ⊥`, because `S a₁ ∈ I` and `S a₁ ≠ 0` (it is not in `M`).
- Every `J < I` is `⊥`. The preimage `N = S⁻¹ J` is a subrepresentation
  containing `M`, since `S` kills `M`. If `a₀ ∈ N`, then `Z ≤ N`, so
  `I ≤ J`, which is impossible. Otherwise `N` is in the Zorn family above
  `M`, so `N ≤ M` by maximality. Any `x ∈ J` has the form `S z` with
  `z ∈ Z`. Then `z ∈ N ≤ M`, so `x = 0`.

Hence `I` is an atom, so `I ≤ s ≤ M`, which contradicts `S a₁ ∈ I` and
`S a₁ ∉ M`.

`isSemisimpleRepresentation_of_sSup_atoms_eq_top` transfers this along Mathlib's
order isomorphism `Subrepresentation.subrepresentationSubmoduleOrderIso`.
Its target is the lattice of submodules of `ρ.asModule` over the monoid algebra
`k[G]`.
Order isomorphisms preserve atoms (`OrderIso.isAtom_iff`), suprema and `⊤`, so
the atoms of the submodule lattice of `ρ.asModule` also have supremum `⊤`.
Mathlib's `complementedLattice_of_sSup_atoms_eq_top` then gives a complemented
submodule lattice, that is `IsSemisimpleModule` (`isSemisimpleModule_iff`).
`Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`
converts this back to `ρ.IsSemisimpleRepresentation`.

## Relation to the source

Bernstein–Zelevinsky (1976), Theorem 2.44(b), p.28, deduces the final sentence
from the finite-irreducible splitting of Theorem 2.44(a) and the projectors of
Section 2.43, which rest on Theorem 2.42. The implemented proof does not follow
that route, and it does not prove Theorem 2.42, Lemma 2.40, the projector
statements or `Langlands.CompactCoefficientSplittingStatement`. Its lattice step
is the equivalence of conditions (b) and (c) of Lemma-Definition 2.7, in the form
of Mathlib's `complementedLattice_of_sSup_atoms_eq_top`.

## Exact target and dependencies

The target is statement artifact `d30de5de-45af-4026-83f3-e1169a1cf940`,
`Langlands.CompactCoefficientSemisimplicityStatement`, in the current Library
module `Langlands.Representation.CompactCoefficient.SemisimplicityStatement`;
the proof leaves that pair and its imports unchanged. The proof task is
`d5a1f78e-156e-40a1-bf22-b80779eda1ce`, revision 1. The module imports the
published modules `Langlands.Representation.Compact.ProjectionProof`,
`Langlands.Representation.Hecke.IntegratedConvolution`,
`Langlands.Representation.Hecke.CommonInvarianceProof` and
`Langlands.Representation.SubrepresentationLattice`. It was compiled in
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings.

Authored by Worker 261.
