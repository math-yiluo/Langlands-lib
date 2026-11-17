# Twisted conjugation, centralizers, orbital integrals and the twisting operator

Module `Langlands.TraceFormula.TwistedOrbital`, namespace `Langlands.TraceFormula`.
These definitions are generic in the group and twist. They supply the group and
measure objects for later simple trace formula statements.

## Sources and scope

Getz–Hahn, *An Introduction to Automorphic Representations* (2024), §18.5,
printed pp. 486–488 (PDF pp. 493–495), equations (18.30)–(18.33), defines
twisted conjugation, its centralizer, the twisted orbital integral and inverse
pullback on `L²`. The paragraph after (18.33) gives the kernel as
`K_f(g, θ(h))`. Source ID: `getz-hahn-2024-automorphic-representations`.
The October 2026 errata, p. 4, §18.5, corrects only the cross-reference at the
end of the section to §19.4; it leaves these formulas unchanged. Source ID:
`getz-hahn-2024-errata-2026-10`.

The book assumes a finite-order automorphism of a reductive group over a number
field. Its (18.32) uses the quotient
`(A_G^θ \ C_γ^θ(𝔸_F)) \ (A_G \ G(𝔸_F))`, with compatible quotient measures.
The present module extracts the generic group construction on
`C_δ^θ \ G`. It supplies neither those adelic groups and split central quotients
nor a comparison with them. Group endomorphisms suffice for its algebraic part;
finite order, reductivity, topology and discreteness are unnecessary there.

For the untwisted convention, Deligne–Kazhdan–Vignéras, *Représentations des
algèbres centrales simples p-adiques*, in the 1984 volume *Représentations des
groupes réductifs sur un corps local*, §A.1, printed pp. 41–44 (PDF pp. 45–48),
gives the sum `Σ_γ f(x⁻¹ γ y)` on p. 42 and the conjugacy orbital integral on
p. 44. Source ID: `bdkv-1984-representations-local-field`. That source also
uses central quotients and compatible measures; here the untwisted objects
are obtained by specializing the generic definitions to the identity.

## Definitions and conventions

The algebraic definitions use any group `G` and any `F` with
`[FunLike F G G] [MonoidHomClass F G G]`. Thus `θ : F` can be a monoid
endomorphism, an automorphism, or a continuous automorphism. The function
`twistedConj` and the conjugacy predicate and class need only the underlying
function. All coset spaces reuse `QuotientIntegration.LeftQuotient H`, whose
points are the cosets `H * x`, representing `H \ G`.

- `twistedConj θ x δ = x⁻¹ * δ * θ x`. The element `x` acts on `δ` from the
  right: acting first by `x` and then by `y` acts by `x * y`
  (`twistedConj_one`, `twistedConj_mul`). `twistedConj_apply` unfolds the formula.
- `twistedCentralizer θ δ : Subgroup G` is `{x | x⁻¹ * δ * θ x = δ}`.
  `mem_twistedCentralizer` records membership. For `θ = MonoidHom.id G`,
  `twistedCentralizer_id` identifies it with `Subgroup.centralizer {δ}`.
- `IsTwistedConjugate H θ δ δ' : Prop` means
  `∃ h ∈ H, h⁻¹ * δ * θ h = δ'`. `twistedClass H θ δ : Set G` is the set of
  such `δ'`; `mem_twistedClass` expands its membership. No arithmetic or
  geometric structure is imposed on `H` or `G`.
- `twistedOrbitFunction θ δ f`, for any target type of `f`, descends
  `x ↦ f (x⁻¹ * δ * θ x)` using `QuotientIntegration.descend` to
  `LeftQuotient (twistedCentralizer θ δ)`. `twistedConj_left_mul` proves its
  invariance under left multiplication by the twisted centralizer, and
  `twistedOrbitFunction_mk` evaluates it on a representative.
- `twistedOrbitalIntegral θ δ ν f : ℂ` is
  `∫ q, twistedOrbitFunction θ δ f q ∂ν`, with a supplied measurable space
  and measure `ν` on that quotient. `orbitalIntegral δ ν f` abbreviates
  the case `θ = MonoidHom.id G`, with integrand `f(x⁻¹ * δ * x)`.
- `twistedKernel Γ θ f x y : ℂ` is
  `∑' γ : Γ, f (x⁻¹ * γ.val * θ y)`. It is invariant under left translation
  of `x` by `Γ` (`twistedKernel_left_mul_left`), and under left translation
  of `y` by `Γ` when `hθ : ∀ γ ∈ Γ, θ γ ∈ Γ`
  (`twistedKernel_left_mul_right`). Neither identity needs summability.
- `twistedKernelDiagonal Γ θ hθ f : LeftQuotient Γ → ℂ` descends
  `x ↦ twistedKernel Γ θ f x x` by those two invariances.
  `twistedKernelDiagonal_mk` evaluates it on representatives.
- `twistOperator Γ θ hθ ν hν : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν` uses
  `θ : G ≃ₜ* G` on a group with a topological space,
  `hθ : ∀ x, θ x ∈ Γ ↔ x ∈ Γ`, and a supplied measure on `LeftQuotient Γ`.
  Set `θ̄ = QuotientIntegration.quotientAutomorphism Γ θ hθ`.
  The hypothesis `hν` says that `θ̄.symm` preserves `ν`. The operator is the
  continuous linear map underlying
  `Lp.compMeasurePreservingₗᵢ ℂ θ̄.symm hν`.
  `twistOperator_coeFn` states the almost-everywhere identity
  `I_θ φ(q) = φ(θ̄⁻¹(q))`; `norm_twistOperator_apply` states `‖I_θ φ‖ = ‖φ‖`.

All measures are explicit and no normalization is built in. The orbital
integral uses Mathlib's total Bochner integral, which is zero for a
nonintegrable integrand. The kernel uses Mathlib's unconditional `tsum`, which
is zero for a nonsummable complex family. The module assumes neither
integrability nor summability. Compatibility with Haar and subgroup measures,
measurability, convergence, integral-kernel identities, ellipticity and trace
formulas require separate hypotheses or results. No such results are asserted
here.

## Implemented API proofs and provenance

The elementary lemmas are internal consequences needed for these definitions.
The right-action laws use multiplicativity of `θ`. The centralizer subgroup
laws expand the stabilizer equation, and the inverse case uses `map_inv` and
group cancellation. Its identity-twist comparison rewrites the stabilizer
equation as commutation with `δ`. The orbit integrand is unchanged on `c * x`
because the inner factor `c⁻¹ * δ * θ c` is `δ`; `descend` then gives the
function on the existing quotient.

The first kernel invariance reindexes by left multiplication by `γ` in `Γ`.
For the second, put `t = θ(γ) ∈ Γ` and reindex by right multiplication by
`t⁻¹`. Both use `Equiv.tsum_eq`, which applies even to nonsummable families.
The diagonal descends by composing these invariances. The twisting operator's
almost-everywhere formula and norm equality are Mathlib's
`Lp.coeFn_compMeasurePreserving` and `Lp.norm_compMeasurePreserving`.
The generalization from the source's finite-order adelic setting to the
explicit group and measure parameters is an internal abstraction.
