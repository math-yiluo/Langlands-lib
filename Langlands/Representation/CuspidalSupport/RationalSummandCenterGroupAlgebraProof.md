# Renard VI.4.4, Proposition: proof

Author: Worker 5102.

`rationalSummandCenterGroupAlgebra : RationalSummandCenterGroupAlgebraStatement.{uF, uV}`
proves the published statement of Renard's VI.4.4 Proposition, in its published
derived form, at arbitrary universes uF and uV, with its premises unchanged.

For π irreducible and cuspidal, ρ an irreducible smooth representation of
H⁰ = `rationalCommonNormKernel G` with an injective H⁰-map into Res π,
I = ind_{H⁰}^G ρ and T = ⋂ ker ω over the unramified ω with π ⊗ ω ≅ π, there is a
ℂ-algebra isomorphism e : ℂ[T ⧸ (H⁰ ∩ T)] ≃ center(End I). For every t ∈ T,
ψ = e(class of t) satisfies:

- every ψ(f_w) vanishes at every g with g t ∉ H⁰;
- ψ ≫ φ = ω(t) φ for every unramified ω and every
  φ : I → `rationalUnramifiedTwist G ω (rationalInertiaBaseLift G π)`.

The proof is one line:
`rationalSummandCenterGroupAlgebra_of_finiteRestriction rationalNormKernelFiniteRestriction`.

- `rationalNormKernelFiniteRestriction` (module
  `RationalNormKernelFiniteRestrictionProof`, Worker 4361) is the published
  unconditional proof of VI.3.2(ii), `RationalNormKernelFiniteRestrictionStatement`.
- `rationalSummandCenterGroupAlgebra_of_finiteRestriction` (module
  `NormalHeckeHomDetection`) derives the Proposition from it through Worker 1826's
  `NormalHecke.exists_algEquiv_center_quotient`. In that result, the center is the group
  algebra of the radical of the grading of End(I) by G(F)/H⁰. The radical is identified
  with T/(H⁰ ∩ T) through the twist-detection hypothesis `hiso`, and ψ_t acts on maps
  into π ⊗ ω by ω(t) through the twist law of `NormalHeckeTwist`. Both `hcyc` and `hiso`
  are proved in `NormalHeckeHomDetection` without VI.4.1. The twist clause is applied to
  the homomorphism underlying the unramified character ω, whose kernel is open and
  contains H⁰.

No premise is added, and admissibility, finite dimensionality, VI.4.1 and finiteness of
X(G)(π) are not used.

Source: David Renard, *Représentations des groupes réductifs p-adiques* (registered
source `renard-2026-representations-groupes-reductifs-padiques`), VI.4.4, Proposition,
printed pp.158–159 / PDF pp.164–165. The statement replaces Renard's normalization
ψ_g(g⁻¹) = ρ_T(g⁻¹) by the action ψ ≫ φ = ω(t)·φ, as its Markdown explains. The
implemented proof does not follow Renard's computation (VI.4.3.2), (VI.4.4.7). It is
described in `NormalHeckeHomDetection.md` and `NormalHeckeCenter.md`.
