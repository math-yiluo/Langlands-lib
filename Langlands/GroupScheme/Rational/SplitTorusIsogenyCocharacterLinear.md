# Cocharacter conclusions from an inverse up to an integer

Author: Worker 1444.

This internal supporting module constructs scalar-extension equivalences from
integer quasiinverses and proves the corresponding four conclusions for actual
split-torus cocharacters. It does not construct a quasiinverse from an isogeny.
The geometric input to the final theorem is a homomorphism in the reverse
direction whose two composites are multiplication by the same nonzero integer.

## Linear constructions

For additive commutative groups `M` and `N`, use their canonical integer module
structures. The maps `f : M →ₗ[ℤ] N` and `g : N →ₗ[ℤ] M` have an integer
`n ≠ 0` with `g ∘ₗ f = n • id` and `f ∘ₗ g = n • id`.
All declarations in this paragraph are in
`Langlands.GroupScheme.SplitTorusIsogeny`.

- `injective_of_left_quasiInverse` uses only the first composite and the
  torsion-freeness of `M`: equality after `f` gives equality after multiplication
  by `n`, which can be cancelled.
- `finite_cokernel_of_right_quasiInverse` assumes that `N` is finitely generated
  over `ℤ` and uses only the second composite. Every class in `N / range f` is
  killed by `n`, because `n • y = f (g y)`. The quotient is finitely generated
  and torsion, so Mathlib's `Module.finite_of_fg_torsion` makes its underlying
  type finite.
- `baseChange_bijective_of_quasiInverse` extends both composite identities to
  any characteristic-zero field `K`. The integer `n` has nonzero image in `K`.
  Cancellation proves injectivity and `(n : K)⁻¹ • g_K y` is a preimage of `y`.
  No finite-generation or torsion-freeness hypothesis is needed for this step.
- `scalarExtensionEquivOfQuasiInverse` packages this bijective scalar extension
  as a `K`-linear equivalence. Its forward map is exactly `f.baseChange K`, as
  stated by `scalarExtensionEquivOfQuasiInverse_apply`.

## Actual cocharacter lattices

For a field `k : Type u` in an arbitrary universe and an actual commutative group
scheme `T` over `Spec k`, `IsSplitTorus.exists_cocharacterCoordinates` transports
`T` along a split presentation and composes the published
`cocharacterLattice.congr` with `splitTorus.cocharacterLatticeEquiv`. It produces
some finite `I : Type u` and an integer-linear equivalence between the actual
lattice `cocharacterLattice T` and `I → ℤ`. The finite index type may be empty.
This yields `IsSplitTorus.finite_cocharacterLattice` and
`IsSplitTorus.torsionFree_cocharacterLattice` by transporting these properties
from the finite function module. Coordinate choices are used to establish these
properties; they do not replace the actual cocharacter lattice or its maps.

`SplitTorusIsogeny.cocharacter_isogeny_conclusions_of_quasiInverse` takes actual
homomorphisms `f : A ⟶ T` and `g : T ⟶ A` of commutative group schemes, splitness
of both tori, and the identities `f ≫ g = n • 𝟙 A` and `g ≫ f = n • 𝟙 T` for
`n : ℤ` with `n ≠ 0`. It proves the conjunction of:

1. injectivity of the published `RealTorusSpace.cocharacterMapInt f`;
2. finiteness of its actual quotient cokernel;
3. bijectivity of its base change to `ℚ`;
4. bijectivity of the published `RealTorusSpace.cocharacterMapReal f`.

The proof computes the two composites on an actual cocharacter `ν` by category
associativity and bilinearity of composition. The identities become `n • id`
on the actual lattices. The generic linear lemmas give the four conclusions.
The argument imposes no restriction on the characteristic or perfection of `k`
and does not use surjectivity on rational points.

## Provenance and scope

These constructions and lemmas are internal algebraic deductions from the
published split-torus and lattice interfaces. The motivation is the elementary
lattice step of the derived route recorded in the paired documentation for
`Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacter`. No external
source theorem is asserted here. In particular, the hypotheses of the last
lemma include the reverse homomorphism and both composite equalities; this
module alone does not prove `SplitTorusIsogenyCocharacterStatement`.
