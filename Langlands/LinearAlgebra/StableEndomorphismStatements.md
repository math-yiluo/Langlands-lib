# Stable endomorphisms of arbitrary complex vector spaces

This module introduces two transparent proposition predicates and the exact
statement targets for David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix C.II, Definition and
Lemma (i)–(iv), printed pages 276–278 / PDF pages 282–284. It contains no
proofs of these targets.

The governing registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 648 read the text and visually inspected all three cited PDF pages,
including both commutative diagrams.

## Existing constructions and hypotheses

Every carrier is an existing complex vector space, represented by
`V : Type uV`, `[AddCommGroup V]` and `[Module ℂ V]`. Endomorphisms are
`Module.End ℂ V`; arrows between distinct carriers are actual complex-linear
maps. `LinearMap.ker` and `LinearMap.range` are the existing submodules of the
appropriate carriers. `IsCompl` is the lattice complement relation on actual
submodules: their intersection is zero and their sum is the whole space.
Thus the direct sum in part (i) is an internal decomposition, without
introducing a replacement space or an abstract splitting certificate.

The only imports are Mathlib's submodule range module (which also imports
kernels), complex scalars, and lattice disjointness/complementarity. Powers
use the existing endomorphism monoid, whose multiplication is composition
and whose identity is the identity linear map. There is no new scalar,
linear-map, exact-sequence, or submodule framework.

No finite-dimensionality, countability, topology, chain condition, or
nontriviality is assumed. In particular, the zero vector space is allowed.
The scalars are exactly `ℂ`; no general-field extension is asserted.
The carriers `A : Type uA`, `B : Type uB`, and `C : Type uC` have independent
universes. The one-space targets use the independent universe `uV`.
Each theorem target binds its carriers, structures and maps internally,
so a proof successor can name the complete proposition.

## Declaration correspondence

All declarations below are in the namespace
`Langlands.LinearAlgebra.StableEndomorphism`. They are `def` declarations
returning `Prop`.

| Declaration | Exact content and source correspondence |
| --- | --- |
| `Stable t` | Definition, printed276/PDF282: `ker t = ker (t ^ 2) ∧ range t = range (t ^ 2)`. Both equalities are required. |
| `EventuallyStable t` | Same definition: `∃ n : ℕ, 0 < n ∧ Stable (t ^ n)`. The witness exponent is positive, as in the source's `ℕ*`. |
| `StableIffIsComplStatement` | Lemma (i), printed276/PDF282, proof on printed277/PDF283: for every actual endomorphism `t`, `Stable t ↔ IsCompl (ker t) (range t)`. |
| `StableOfRightExactStatement` | Lemma (ii), printed276/PDF282, proof on printed277/PDF283: assume `range phi = ker psi`, surjectivity of `psi`, the two commuting-square equalities, and stability of `fA` and `fB`; conclude stability of `fC`. The visually inspected rows are `A → B → C → 0`. There is no injectivity premise on `phi`. |
| `StableOfLeftExactStatement` | Lemma (iii), printed277/PDF283, proof continuing on printed278/PDF284: assume injectivity of `phi`, `range phi = ker psi`, the same commuting-square equalities, and stability of `fB` and `fC`; conclude stability of `fA`. The visually inspected rows are `0 → A → B → C`. There is no surjectivity premise on `psi`. |
| `PowerKernelRangeMonotonicityStatement` | Monotonicity clause of Lemma (iv), printed277/PDF283 and its opening proof on printed278/PDF284: `k ↦ ker (t ^ k)` is monotone and `k ↦ range (t ^ k)` is antitone. This elementary clause is stated without eventual stability, an explicitly isolated strengthening that follows from composition of powers alone. No stabilization conclusion is asserted without eventual stability. |
| `AdjacentStabilizationStatement` | Lemma (iv), same source pages: under `EventuallyStable t`, at every `k : ℕ` the two adjacent equalities are equivalent; if either equality holds, both chains are constant from `k` onward. The two equalities concern the actual submodules at exponents `k` and `k + 1`, and constancy quantifies over every `m ≥ k`. |
| `FirstStabilizationIndexStatement` | Lemma (iv), same source pages: under `EventuallyStable t`, there exists `k₀ : ℕ` such that both chains are constant for every `m ≥ k₀`, and both adjacent equalities fail for every `j < k₀`. This exposes the common first index, rather than merely an unspecified eventual threshold. |
| `StableEndomorphismStatement` | Internal aggregate of the preceding six closed theorem targets, in their table order. Its provenance is this packaging of Lemma (i)–(iv); it introduces no additional mathematical hypothesis or conclusion. |

The commuting-square equalities are exactly
`fB.comp phi = phi.comp fA` and `fC.comp psi = psi.comp fB`.
The rows use the same maps above and below, so these are the full diagram
conditions. Exactness is expressed at `B` by the actual submodule equality,
and at the displayed end by the corresponding injectivity or surjectivity.

The aggregate uses universe parameters in the order `uV uA uB uC`.
For a future proof `h : StableEndomorphismStatement.{uV, uA, uB, uC}`,
the named targets are available by conjunction projection:

| Target | Projection |
| --- | --- |
| `StableIffIsComplStatement.{uV}` | `h.1` |
| `StableOfRightExactStatement.{uA, uB, uC}` | `h.2.1` |
| `StableOfLeftExactStatement.{uA, uB, uC}` | `h.2.2.1` |
| `PowerKernelRangeMonotonicityStatement.{uV}` | `h.2.2.2.1` |
| `AdjacentStabilizationStatement.{uV}` | `h.2.2.2.2.1` |
| `FirstStabilizationIndexStatement.{uV}` | `h.2.2.2.2.2` |

## Exponent zero and the first common index

In part (iv), write `N_k = ker (t ^ k)` and `I_k = range (t ^ k)`.
All chain indices range over `ℕ`, including zero. Since `t ^ 0` is the
identity, `N_0 = ⊥` and `I_0 = ⊤`. The positive witness in
`EventuallyStable` does not impose positivity on the first stabilization
index. In particular, for an invertible endomorphism that first index is
zero; the zero vector space also stabilizes at zero.

The constancy clause for `k₀` includes `m = k₀ + 1`, hence gives both
adjacent equalities at `k₀` by symmetry. The strict earlier inequalities
then make `k₀` the least index at which either adjacent equality holds.
The adjacent-equality target also states directly that every such equality
forces both chains to stay constant. Together these record the common
first-index assertion, without an externally supplied threshold.

The final paragraph of the source proof, printed278/PDF284, repeats `I_k`
where it compares the two chains. The targets formalize the coherent
common-index assertion in the lemma's statement; they do not reproduce that
prose typo.

## Errata check

On 26 October 2026 Worker 648 checked the
[author's current book page](https://perso.pages.math.cnrs.fr/users/david.renard/).
It links the corrected 2026 French edition and separately labels its
[correction list](https://perso.pages.math.cnrs.fr/users/david.renard/erratumlivre.pdf)
as errata for the 2010 edition. No separate 2026 errata link was displayed.
The freshly downloaded correction list has the same SHA256 as the retained
registered source `renard-2010-corrections-complements`:
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.
Its PDF pages 18–19 were read for the appendix corrections.

PDF19 corrects the old printed320 proof to use
`ker fC ∩ Im fC` and the old printed321 image formula to use `N_(k+2)`.
Both corrections are already present in the governing 2026 printed278/PDF284.
They do not change the present theorem targets. The older correction list
is supplementary evidence and is not substituted for the 2026 source.
No project `notes/errata/renard-2026-representations-groupes-reductifs-padiques.md`
was present at preparation time.

## Proof status, implementation leads and separate obligations

These declarations specify propositions; they supply no substantive proof
of parts (i)–(iv). Compilation and proposition inspection check elaboration
and types, not the truth of the stated mathematical results.

Source inspection of the prepared Mathlib suggests `LinearMap.iterateKer`
and `LinearMap.iterateRange` for monotonicity and
`Module.End.ker_pow_constant` for propagation of a kernel equality. These
are implementation leads, not checked proofs of this family.
The Artinian/Noetherian eventual-stabilization theorems and the Library's
finite-dimensional compact-compression results have stronger hypotheses
and do not establish these arbitrary-dimensional targets.

Three separate obligations remain with the parent Renard program:

1. The source extends its terminology to endomorphisms of `B`-modules for
   a possibly noncommutative complex algebra under the book's global
   nonunital-action conventions. An adapter over the actual nonunital
   module construction is still required. Ordinary unital `[Module B V]`
   instances do not discharge it.
2. The source proof of (iv), printed278/PDF284, constructs the quotient
   spaces `E_k = N_(k+1) / N_k` and `F_k = I_k / I_(k+1)`, the maps induced
   by `t` and `t ^ k`, their stated kernels and images, and the exact sequence
   `0 → E_(k+1) → E_k → F_k → F_(k+1) → 0`.
   Those auxiliary construction and assertion obligations are not
   supplied or imported here. A later proof of the final targets may take
   another route without claiming to discharge these source assertions.
3. The final proposition of C.II, printed279/PDF285, on finite generation
   of the actual endomorphism localization remains separate. It depends
   on Appendix A localization, not on specialized Jacquet coinvariants.
