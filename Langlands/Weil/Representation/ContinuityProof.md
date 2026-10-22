# Proof of continuity and finite inertia image

`Langlands.Weil.representationContinuity.{uW,uV}` proves exactly the unchanged
published proposition `Langlands.Weil.RepresentationContinuity.{uW,uV}` from
`Langlands.Weil.Representation.Continuity`. It proves all five equivalences for
an arbitrary topological group with an open, compact, nonarchimedean subgroup
and a finite-dimensional normed complex representation. The group and carrier
universes are independent. No Hausdorff condition is imposed on the group or
inertia subgroup. The proof includes the zero-dimensional carrier.

## Implemented proof

### The small-subgroup estimate

`eq_one_of_small_submonoid` proves the needed estimate in any real normed
algebra. If a submonoid `S` satisfies `‖a - 1‖ ≤ 1/2` for every `a ∈ S`, then
every element of `S` equals one. The noncommutative ring identity

`2 • (a - 1) = (a * a - 1) - (a - 1) * (a - 1)`

and the triangle and submultiplicative norm inequalities give

`(3/2) * ‖a - 1‖ ≤ ‖a * a - 1‖`.

Induction, using closure under squaring, improves the uniform bound to
`‖a - 1‖ ≤ (2/3)^n` for every natural number `n`. The limit of these real
powers is zero, so norm separation gives `a = 1`. This proof does not assume
`NormOneClass`, a nontrivial algebra, finite dimension, completeness, a spectral
theorem, or a no-small-subgroups theorem.

For `open_kernel_of_continuous_nonarchimedean_representation`, the representation
operators form a monoid homomorphism into the complex continuous endomorphisms,
regarded as a real normed algebra. Continuity makes the inverse image of the
radius-1/2 ball around the identity a neighborhood of one. Nonarchimedeanness
supplies an open subgroup in this neighborhood. Its image submonoid satisfies
the estimate, so it lies in the representation kernel. A subgroup containing
an open subgroup is open. Compactness is not needed for this step.

### Kernel topology and finite range

`continuous_of_open_kernel` factors an arbitrary monoid homomorphism through
the discrete quotient by its open kernel. This proves continuity into any
topology on the target. `representation_continuous_of_open_kernel` applies the
same quotient argument directly to the continuous-linear-map presentation of
the representation operators, without changing their operator-norm topology.

`open_kernel_iff_open_restriction_kernel` relates the full kernel to its
restriction to an open subgroup. Restriction preserves openness by continuity
of the subtype map. Conversely, the subtype map is open, so the image of the
open restricted kernel is an identity neighborhood contained in the full
kernel. A subgroup which is an identity neighborhood is open. This requires
neither normality of the chosen open subgroup nor compactness.

`finite_range_of_open_kernel` uses compactness to make the discrete quotient
by the open kernel finite. The homomorphism range is contained in the finite
range of the quotient lift. `open_kernel_of_finite_range_of_closed` proves the
converse without compactness: the quotient lift injects into the finite range,
so the kernel has finite index; a closed finite-index subgroup is open.
An open subgroup is closed, giving the complete equivalence recorded in
`open_inertia_kernel_iff_finite_range_and_closed`. Closedness remains an
explicit hypothesis in the finite-image converse.

### Assembly of the five clauses

1. Mathlib's `continuous_clm_apply` gives operator continuity if and only if
   every orbit map is continuous, using finite dimension of the source vector
   space.
2. Continuous evaluation of continuous linear maps gives joint continuity.
   Conversely, composing the joint action with `w ↦ (w,v)` gives each orbit
   map, and the first clause recovers operator continuity.
3. Restrict operator continuity to inertia and apply the small-subgroup
   argument. In the reverse direction, the open restricted kernel gives an
   open full kernel, hence operator continuity through the discrete quotient.
4. Combine the third clause with the equivalence of open full and restricted
   kernels.
5. Apply the compact finite-range/closed-kernel equivalence to the restricted
   homomorphism.

## Reusable interface

All declarations below are in `Langlands.Weil` in this module:

- `open_kernel_of_continuous_nonarchimedean_representation` requires only a
  nonarchimedean topological group and continuous finite-dimensional complex
  operators; it gives an open kernel.
- `finite_range_of_open_kernel` applies to any monoid homomorphism from a
  compact topological group.
- `open_inertia_kernel_iff_finite_range_and_closed` is the exact restricted
  finite-image criterion, with the necessary closedness condition.
- `continuous_compact_nonarchimedean_representation_finite_range` has explicit
  carrier arguments `K : Type uW` and `V : Type uV`, with instances
  `[Group K] [TopologicalSpace K] [NonarchimedeanGroup K] [CompactSpace K]`,
  `[NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]`, and a
  representation `ρ : Representation ℂ K V`. It sends
  `Continuous (fun k => (ρ k).toContinuousLinearMap)` to `(Set.range ρ).Finite`.
  There is no separation hypothesis on `K`. This is the whole-group case of
  the finite-inertia consequence, implemented directly from the same open
  kernel and compact quotient helpers used in the main theorem.

## Provenance and scope

The original-source correspondence is that of the unchanged statement:

- Guy Henniart, *Representations du groupe de Weil d'un corps local* (1980),
  sections 2.1 and 2.5, printed pages 158–159, retained PDF pages 5–6.
  Literature ID `henniart-1980-weil-representations`; SHA-256
  `451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`.
  Section 2.1 supplies the open inherited inertia topology; section 2.5 uses
  triviality on an open inertia subgroup and the resulting finite quotient.
- John Tate, *Number theoretic background* (1979), section 2 opening and
  section 2.1, printed page 9, retained PDF page 18; section 4.1.2(a), printed
  page 20, retained PDF page 29. Literature ID
  `tate-1979-number-theoretic-background`; SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  Tate defines continuity into the usual complex general linear group, invokes
  absence of small subgroups, and later formulates the open inertia kernel
  condition for the Weil part of a Weil–Deligne representation.

These original pages were read directly. The explicit norm estimate, quotient
proofs, and orbit/joint-continuity reformulations are internal derivations
implementing the target, rather than transcriptions of a literature proof.
The finite-image converse with closed kernel is the target's derived
supplement. No source claims that arbitrary finite image implies continuity.

The proof uses no degree map, Frobenius lift, irreducibility, normality of
inertia, or finite image of the full representation. The complex topology is
unchanged. No norm/module-topology or bundled-predicate adapters are redefined.
The compact-group helper is intended for the separate unramified-reduction
and finite-image-extension proof tasks. Compilation alone does not establish
semantic acceptance or Library publication.

## Development validation

The proof module compiles without errors or warnings. Private development checks
assigned the entire unapplied closing constant both to the published target
and to its fully expanded five-clause telescope, with independent universes.
A second unapplied assignment checked the complete compact-group helper type.
The Lean service's Lake build and declaration inspection succeeded. Both the
main theorem and compact-group helper depend only on `propext`,
`Classical.choice`, and `Quot.sound`. These checks precede, and do not replace,
formal exact-target validation and independent semantic review of the candidate.
