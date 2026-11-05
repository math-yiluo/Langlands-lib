# Wall-reflection generation and galleries for locally finite arrangements

This is an internal generic geometry prerequisite for affine Weyl chamber
simple transitivity. Worker 455 supplied the initial definition and statement
design. It uses the published interfaces imported from
`Langlands.Geometry.Building.AffineWeylGroups`, including the existing
`IsCoroot`, `affineReflection`, `affineWeylGroup` and `facetRel`.
The vector space `V : Type uV` and its affine torsor `A : Type uA` have
independent universe levels. The only ambient instances are
`AddCommGroup V`, `Module ℝ V` and `AddTorsor V A`; the torsor is nonempty
and no origin is chosen.

For a set of affine functionals `Ψ : Set (A →ᵃ[ℝ] ℝ)`, the Prop-valued
structure `AffineRootSystem.IsLocallyFiniteReflectionArrangement Ψ` has
exactly five fields:

- `derivativeRoots Ψ` spans the whole algebraic dual `Module.Dual ℝ V`.
- Every `ψ ∈ Ψ` has nonzero linear part.
- The set `derivativeRoots Ψ` is finite.
- Every `ψ ∈ Ψ` admits a vector `v` with the existing `IsCoroot Ψ ψ v`.
  Explicitly, `ψ.linear v = 2`, and
  `η - η.linear v • ψ ∈ Ψ` for every `η ∈ Ψ`.
- For every `x : A` and every function
  `bound : Module.Dual ℝ V → ℝ`, the set of `ψ ∈ Ψ` with
  `|ψ x| ≤ bound ψ.linear` is finite. The bound is arbitrary and need
  not be positive.

These premises allow finite real reflection arrangements satisfying the same
spanning and preservation conditions, including noncrystallographic examples.
Integral root-coroot pairings, infinite parallel families and reducedness are
not required. All five fields remain premises of the statement.

`reflectionSeparates Ψ s x y` means that `s` is an actual coroot reflection
for a root of `Ψ` whose values at `x` and `y` have negative product.
Concretely, it requires witnesses `ψ ∈ Ψ`, `v : V` and
`hv : IsCoroot Ψ ψ v` such that `s = affineReflection ψ hv.1` and
`ψ x * ψ y < 0`. Thus equality of separating reflections is equality of
actual affine automorphisms. Proportional roots defining the same reflection
do not create distinct separating elements. The definition quantifies all
coroots already used by `affineWeylGroup`.

`wallReflections Ψ x` consists of actual reflections `s` such that exactly
`s` separates `x` from `s x`: first `reflectionSeparates Ψ s x (s x)`
holds, and every `t` satisfying `reflectionSeparates Ψ t x (s x)` equals
`s`. The intended geometric interpretation at a regular point is reflection
across an adjacent chamber wall. That interpretation belongs to the later
geometry proof. The definition itself is a set of affine automorphisms
defined by this separation and uniqueness condition.

`AffineReflectionGalleryGeometryStatement` asserts, for each arrangement
satisfying the five premises and each regular `x`, the conjunction of:

1. `Subgroup.closure (wallReflections Ψ x) = affineWeylGroup Ψ`.
   Here `Subgroup.closure` means the algebraically generated subgroup of
   `A ≃ᵃ[ℝ] A`; it is not a topological closure.
2. For every regular `y : A`, there exists
   `w : Subgroup.closure (wallReflections Ψ x)` such that
   `facetRel Ψ ((w : A ≃ᵃ[ℝ] A) x) y`.
   This is equality of the signs of all root values at `w x` and `y`,
   using evaluation of the actual affine automorphism.

A point is regular here precisely when `∀ ψ ∈ Ψ, ψ x ≠ 0`.
Generation and chamber transport are conclusions; there are no additional
action, transitivity or freeness assumptions. The target does not assert
uniqueness of the transporting element. The empty arrangement is included
in rank zero: when `V` is zero-dimensional its dual is trivial, the five
premises hold for `Ψ = ∅`, and its nonempty torsor has one point.
Nonreduced root sets are allowed, with separation counted by reflections.
This file defines the proposition and its supporting notions; both
geometric conclusions remain unproved.

The definitions and statement are internally formulated from the published
affine-root interfaces. The motivating source is the gallery geometry behind
Kaletha–Prasad (2023), Remark 1.3.16 and Lemma 1.3.17, but this stronger
nonintegral, finite-arrangement formulation is a separate internal prerequisite.
It is not attributed as a literal assertion of that book. A later proof must
establish its geometric claims. The affine-root-system consumer must itself
derive all the arrangement premises from its unchanged axioms before applying
the proved statement.

Sources read for this provenance and convention comparison:

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  Remark 1.3.16, printed p.19/PDF p.50 (chambers and walls), and
  Lemma 1.3.17, printed p.21/PDF p.52 (chamber simple transitivity).
  Registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
- Kaletha–Prasad, *Corrections and additions* (1 November 2024),
  PDF p.2 (the infinite-fibre condition in corrected AR 4), and pp.3–4,
  especially p.4 (the facet equivalence by hyperplanes and open sides).
  Registered as `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
