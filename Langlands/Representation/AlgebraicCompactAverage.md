# Compact averaging for algebraically locally finite representations

Author: Worker 94. This is an internal construction from `Langlands.Analysis.FiniteSpanIntegral`, Mathlib's invariant submodule, and translation invariance of scalar integration. It attributes no theorem to an external source.

For a complex representation `ρ` of a topological group `G`, `HasFiniteContinuousOrbits ρ` means that every orbit `g ↦ ρ g v` has finitely generated complex span and that composing it with every algebraic complex linear functional is continuous. The group and two representation spaces in the naturality theorem may have independent universes. No topology is chosen on a representation space.

For compact `G` equipped with its Borel measurable structure and a finite measure `μ`, `average ρ hρ μ : V →ₗ[ℂ] V` integrates each orbit by finite-span integration. Its additivity and complex homogeneity follow by applying algebraic linear functionals and using the corresponding scalar integral identities. `dual_average` characterizes its value under every algebraic linear functional.

When multiplication on `G` is measurable and `μ` is left invariant, `average_mem_invariants` proves that every average lies in the actual invariant submodule `ρ.invariants`, which quantifies over all elements of `G`. The proof applies a linear functional after `ρ k`, uses the representation law to translate the integrand by left multiplication by `k`, and uses left invariance of scalar integration. No connectedness assumption is imposed. The definition `averageToInvariants` restricts the codomain of this actual average to that submodule.

For a probability measure, `average_fixed` is the identity on fixed vectors: their scalar orbit integrals are constant integrals. With both normalization and left invariance, `averageToInvariants_fixed` therefore makes the restricted average a linear retraction. Finally `average_natural` proves that averaging commutes with every equivariant algebraic complex linear map between two representations satisfying the finite-continuous-orbit hypothesis. Its proof compares scalar integrals using the equivariance identity; it requires no continuity hypothesis on the map between representation spaces.

The finite-orbit and scalar-continuity hypotheses remain explicit. This module does not verify them for the actual Cartan symmetric algebras or choose their invariant measure. It establishes no full-group invariant restriction finiteness, PBW comparison, central generation, admissibility, or automorphic differential growth result.
