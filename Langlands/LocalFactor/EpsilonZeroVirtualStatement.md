# The modified local constant on exact virtual representations

`Langlands.LocalFactor.EpsilonZeroVirtualStatement` states the unique
multiplicative extension of Deligne's modified constant `ε₀` from genuine
continuous representations to the actual continuous exact Grothendieck group.
It also states Haar scaling, Haar independence in dimension zero,
additive-character scaling with fixed Haar measure, and induction in dimension
zero and arbitrary integer dimension. These are propositions, not proofs or
axioms. No extension or local-constant system is chosen.

## Objects and specification

The module imports `EpsilonZeroStatement`. Its genuine value is the existing
definition

`ε₀(A, ψ, μ, s) = ε(A ⊗ ω_s, ψ, μ) det(-q_E^(-s) Φ | A^I)`.

Here `A` is an actual finite-dimensional continuous complex representation of
the Weil subgroup of a finite intermediate field `E` in the fixed algebraic
closure of a finite p-adic field `F`. Inertia, its invariant subspace, geometric
Frobenius, the spectral norm character, and the residue cardinality are the
existing arithmetic constructions. The imported genuine value is independent
of the supplied geometric Frobenius lift. The spectral parameter is in `ℂ`,
with the unshifted Deligne convention.

`NonabelianSystem.Assignment F` is reused as a function type only: it takes the
actual field, nontrivial unitary additive character, regular additive Haar
measure, and exact virtual class to a complex unit. It does not by itself
impose the ordinary epsilon-system axioms.

`EpsilonZero.IsVirtualExtension F e ε hε s ε₀` specifies that an assignment:

- takes sums of exact virtual classes to products;
- agrees, as a complex number, with the genuine value above on every
  continuous representation, for every geometric Frobenius lift over its
  intermediate field.

The exact virtual group already imposes isomorphism and short exact sequence
relations. This is not merely a group completion of split direct sums.
Agreement uses `EpsilonZero.genuineClass`, the actual map into that quotient.
The codomain `ℂˣ` supplies nonvanishing; no arbitrary value at zero or at a
negative class can be introduced. The existing elementary
`NonabelianSystem.value_zero` and `value_neg` apply to its additive relation.
None of the Haar, character-scaling or induction laws is included in the
extension predicate.

## The statement

For every prime, p-adic field `F`, reciprocity family `e`, ordinary assignment
`ε` satisfying the published `IsSystem F e ε`, and every `s ∈ ℂ`, the main
statement asserts both of the following:

1. There exists exactly one assignment satisfying `IsVirtualExtension`.
   Uniqueness concerns the full function on all intermediate fields,
   characters, measures and exact virtual classes at this fixed `s`.
2. Every such extension satisfies five laws:
   - positive Haar scaling:
     `ε₀(x, ψ, c μ) = c^(dim x) ε₀(x, ψ, μ)`, for `c > 0`;
   - equality for any two regular Haar measures whenever `dim x = 0`;
   - additive-character scaling with the same Haar measure:
     `ε₀(x, ψ(a·), μ) = det x(w) ω_s(w)^(dim x) |a|^(-dim x) ε₀(x, ψ, μ)`,
     for a nonzero scalar `a` and a Weil element `w` mapping to it under
     the supplied reciprocity;
   - degree-zero induction:
     `ε₀,E(Ind x, ψ, μ_E) = ε₀,L(x, ψ ∘ Tr_{L/E}, μ_L)`;
   - arbitrary-degree induction:
     `ε₀,E(Ind x, ψ, μ_E) = λ^(dim x) ε₀,L(x, ψ ∘ Tr_{L/E}, μ_L)`.

The first and fourth laws reuse the existing predicates
`NonabelianSystem.HaarScalingRelation` and `InductionRelation`. In particular
the fourth law quantifies the actual dimension-zero kernel and permits
independent Haar measures on both fields. The second law is
`EpsilonZero.DegreeZeroHaarIndependence`; it compares arbitrary measures,
not just a supplied rescaling.

The third law is `EpsilonZero.VirtualAdditiveCharacterScaling`. It uses the
published exact virtual determinant character, which sends a difference of
genuine classes to the quotient of their determinant characters. Its norm is
the actual normalized absolute value on the intermediate field.
`CommonClosureSpectral.character F E s` is `ω_s`. Both exponents use the
integer virtual dimension, including negative values. Evaluating the determinant
at every Weil lift of `a` makes the reciprocity convention explicit without
choosing an inverse or assuming the scaling law in the system specification.
The factor `ω_s(w)^(dim x)` is the contribution of the spectral twist to the
determinant; at `s = 0` it is one.

The fifth is `EpsilonZero.VirtualInductionCorrection`. Its `λ` is the actual
ratio from the ordinary assignment at spectral parameter zero:

`λ = ε_E(Ind 1_L, ψ, μ_E) / ε_L(1_L, ψ ∘ Tr_{L/E}, μ_L)`.

The class `1_L` is the published continuous trivial character class; induction
and the trace character are the existing common-closure constructions. Both
`dim x` and its power are integer-valued, so negative virtual dimensions use
inverse powers. The correction is retained in every nonzero dimension.

Existence of the ordinary epsilon system is not asserted here; the theorem is
universally conditional on a supplied system, as is the imported genuine
formula. Existence of the modified virtual extension is a conclusion, not a
hypothesis. Its laws are also conclusions: the statement does not assume the
genuine additivity theorem or a virtual epsilon-zero system.

## Source and derivation

The source is Pierre Deligne, *Les constantes des équations fonctionnelles
des fonctions L* (1973), literature ID `deligne-1973-local-constants`,
SHA-256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`.
The retained original PDF pages 48 and 49 (printed pp.548–549) were read,
including visual inspection of the displayed formulas.

- (5.1) defines the genuine modified value by multiplying ordinary epsilon
  by the determinant of negative geometric Frobenius on inertia invariants.
- (5.2), printed p.548, states additivity for both constants and their
  extension to virtual representations. The existence and uniqueness
  formulation here makes that extension explicit on the published exact
  quotient. Uniqueness follows mathematically because genuine representation
  classes generate the quotient.
- (5.3), printed p.548, states independence of Haar measure in virtual
  dimension zero and the more precise positive-scaling law for both constants.
- (5.4), printed p.548, changes the additive character with Haar measure fixed,
  using the determinant and the negative virtual-dimension power of the
  normalized absolute value. Applied to the spectral twist, its determinant
  is `det x(w) ω_s(w)^(dim x)`.
- (5.6.1) and (5.6.2), printed p.549, state respectively degree-zero induction
  and the same lambda correction for arbitrary virtual dimension, explicitly
  including `ε₀`. Taking the trivial class recovers the stated ordinary
  epsilon ratio for `λ`.

This is a derived statement packaging: the source's virtual extension is
expressed by an existence-and-uniqueness proposition rather than selecting
one by an unproved existence result. The version at every `s` applies the
source laws to `x ⊗ ω_s`. This twist preserves virtual dimension and commutes
with induction. On a formal difference `[A] - [B]`, multiplicativity gives
the quotient of the genuine values; the genuine Haar, character-scaling and
induction laws then give the exponent `dim A - dim B`. The exact determinant
descends through short exact sequences and sends subtraction to quotient.
These observations explain the source correspondence and are not Lean proofs
in this module.

The scope is finite extensions of `ℚ_p`, complex coefficients, continuous
representations with carrier universe `max uF uV`, and one fixed common
closure. There is no assertion of comparison across closures, characteristic
positive fields, archimedean modified constants, or a new conductor formula.
No self-dual measure or half shift is introduced.
