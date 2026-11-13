# Normalized induction from a cocompact closed subgroup and duality

Author: Worker 142.

The theorem `Langlands.Renard.CompactRepresentation.compactQuotientNormalizedInductionDuality`
proves the unchanged published proposition
`Langlands.Renard.CompactRepresentation.CompactQuotientNormalizedInductionDualityStatement`.
It covers every Hausdorff locally compact nonarchimedean group `G`, every closed
subgroup `P` with compact left quotient `P\G`, and smooth complex coefficient
representations in an independent carrier universe. It supplies a positive
smooth square root of the relative modular character. For every positive smooth
square root, it proves natural compatibility of normalized compact induction
with smooth contragredients and compatibility with every supplied model of the
hermitian contragredient. No admissibility or unimodularity hypothesis is added.
The source assertion is Renard 2026, IV.2.1, (IV.2.1.1)–(IV.2.1.2), printed p.97 /
PDF p.103, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The proof uses three derived helper modules. `RelativeHalfModulus` constructs
the positive smooth square root and identifies the positive-unit relative
modulus with the published complex modular character. `RelativeQuotientMeasure`
constructs a measure on the top subgroup of `G`, positive on every open identity
neighborhood, whose integrals of locally constant functions covariant by that
relative modulus are integrable and right invariant. A Borel measurable
structure is installed locally to apply this construction; it adds no hypothesis
to the target. `CompactInductionIntegralDuality` identifies compact and smooth
induction when `P\G` is compact and transfers the published conditional
smooth-induction duality using the identity coefficient map and section.

For any allowed normalizing character `χ`, its square identity supplies the
nonnegative scalar covariance required by the integral-duality theorem. The
constructed measure discharges that theorem's positivity, integrability and
invariance assumptions. Thus, for every smooth coefficient object `A`, there is
an equivariant linear equivalence
`F_A : (i A)̃ ≃ i(Ã)` characterized by the integral of the coefficient pairing.
The internal `exists_naturalCompactIntegralDuality` chooses these equivalences
and constructs a natural isomorphism by `NatIso.ofComponents`. To check its
naturality, it applies `F_A`'s inverse and tests the resulting smooth functionals
on every compact induced function. The two integral formulas then reduce to the
same pointwise coefficient pairing, since induced maps are postcomposition and
contragredient maps are pullback. This argument works on all smooth objects.

For the hermitian clause, the supplied antilinear equivariant coefficient
bijection `e : σ ≃ₗ⋆[ℂ] τ̃` also intertwines the two `χ`-twisted actions: positivity
makes each scalar `χ(p)` real, so complex conjugation fixes it. The internal
`postcomposeSmoothConjugate` sends an induced function `f` to `e ∘ f`, preserving
its original uniform open right stabilizer and its covariance.
`smoothInducedConjugateEquiv` uses postcomposition by `e.symm` for the inverse;
its additive, antilinear and inverse laws follow pointwise.
`compactInducedConjugateEquiv` transports this equivalence through the
compact-to-smooth comparisons. Quotient compactness ensures compact quotient
support, and pointwise postcomposition commutes with right translation.
Finally, composing this antilinear map `i σ ≃ₗ⋆[ℂ] i(τ̃)` with `F_τ.symm` gives
the required antilinear equivariant bijection `i σ ≃ₗ⋆[ℂ] (i τ)̃`.

The naturality and postcomposition constructions in this module are internal
proof infrastructure. The implemented argument uses the existing integral
duality theorem and does not require a separate choice of a hermitian-dual
functor. The target statement and all its existing imports are unchanged.
