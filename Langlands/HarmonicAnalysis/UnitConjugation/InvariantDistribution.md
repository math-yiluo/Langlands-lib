# Conjugation-invariant distributions on an algebra and the spaces `J(ω)`

The module `Langlands.HarmonicAnalysis.UnitConjugation.InvariantDistribution` defines the
conjugation action of the unit group `Aˣ` of a topological ring `A` on `A`, the saturation of a
subset under it, the conjugation-invariant distributions on `A`, and Harish-Chandra's space
`J(ω)` of invariant distributions supported in the closure of the saturation of `ω`.

## Setting

`A : Type v` with `[Ring A] [TopologicalSpace A] [IsTopologicalRing A]`. The case in view is a
finite-dimensional associative algebra over a nonarchimedean local field `F` with its module
topology (`IsModuleTopology F A`), which is a topological ring by Mathlib's
`IsModuleTopology.isTopologicalRing`. Then `Aˣ` is the group of `F`-points of the algebraic
group `GL₁(A)`, whose Lie algebra is `A` with the commutator bracket, and the adjoint action of
`u ∈ Aˣ` is `X ↦ u X u⁻¹`. Distributions are the Library's `Distribution A`, the algebraic
complex dual of the Schwartz–Bruhat space `SchwartzBruhat A` of locally constant compactly
supported functions; on a totally disconnected space every linear functional on `C_c^∞` is a
distribution, so no continuity condition enters.

## Definitions

- `conjugationHomeomorph u : A ≃ₜ A`, `X ↦ u X u⁻¹` (`conjugationHomeomorph_apply`), with
  inverse `X ↦ u⁻¹ X u` (`conjugationHomeomorph_symm_apply`). It is Mathlib's conjugation
  action of the units, `conjugationHomeomorph u X = ConjAct.toConjAct u • X`
  (`conjugationHomeomorph_eq_smul`), and it is an action: `conjugationHomeomorph_one`,
  `conjugationHomeomorph_mul`, `conjugationHomeomorph_symm`.
- `conjugationSaturation ω = ⋃ u, conjugationHomeomorph u '' ω`, the set `ω^G` of all conjugates
  of elements of `ω` (`mem_conjugationSaturation_iff`), containing `ω`
  (`subset_conjugationSaturation`), monotone in `ω` (`conjugationSaturation_mono`).
- `IsConjugationInvariant D`: `Distribution.pushforward (conjugationHomeomorph u) D = D` for
  every unit `u`. By `isConjugationInvariant_iff` this says `D (f ∘ Ad u) = D f` for every
  Schwartz–Bruhat function `f` (the composite written with the Library's
  `Hecke.TestFunction.pullback`).
- `conjugationInvariant`: the complex subspace of `Distribution A` of invariant distributions
  (Harish-Chandra's `J`); membership is `IsConjugationInvariant` (`mem_conjugationInvariant_iff`).
- `invariantSupportedIn ω = conjugationInvariant ⊓ Distribution.supportedOn (closure
  (conjugationSaturation ω))`: Harish-Chandra's `J(ω)`. The support condition is the Library's
  annihilator condition `Distribution.supportedOn`: `D f = 0` for every test function `f`
  vanishing on `cl(ω^G)` (`mem_invariantSupportedIn_iff`). `invariantSupportedIn_mono`: `J(ω)`
  grows with `ω`.
- `mem_invariantSupportedIn_iff_support`: when `A` is Hausdorff, locally compact and totally
  disconnected (as a finite-dimensional space over a nonarchimedean local field is), the support
  condition is Harish-Chandra's `Supp(T) ⊆ cl(ω^G)` for the Library's topological support
  `Distribution.support` (Renard's definition, `Distribution/TopologicalSupport.lean`); the proof
  is `Distribution.support_subset_iff_mem_supportedOn` for the closed set `cl(ω^G)`.

## Source and conventions

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15),
Introduction:

- printed p. 1 (PDF p. 16): `G` acts on its Lie algebra `g` by `x.X = Ad(x)X`; for a
  distribution `T` on `g`, `ˣT` is the distribution `f ↦ T(fˣ)` with `fˣ(X) = f(x.X)`; `T` is
  `G`-invariant if `ˣT = T` for all `x`, and `J` is the space of invariant distributions. Here
  `pushforward (conjugationHomeomorph u) D` is `f ↦ D(f ∘ Ad u) = ᵘD(f)`, so the invariance
  condition is the same.
- printed p. 2 (PDF p. 17): for `ω ⊆ g`, `ω^G = ⋃_{x ∈ G} Ad(x)ω`, and `J(ω)` is the space of
  `T ∈ J` with `Supp(T) ⊆ cl(ω^G)`.

The definition allows any subset `ω`. Harish-Chandra's Theorem 4.4 (printed p. 2, PDF p. 17)
takes `ω` compact.

## Scope

The definitions apply to topological rings: no finiteness, semisimplicity or local compactness
is assumed. The support comparison `mem_invariantSupportedIn_iff_support` assumes that `A` is
Hausdorff, locally compact and totally disconnected.
