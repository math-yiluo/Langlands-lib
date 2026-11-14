# Finiteness of the actual integral polarized automorphism group

`Langlands.AbelianScheme.PolarizedAutomorphismFinitenessStatement` is a
Prop-valued target asserting that the actual subgroup
`polarizedAutGroup ... lam` is finite whenever `lam` satisfies the existing
geometric `IsPolarization` predicate on an actual abelian scheme over
`Spec Ω`, for an algebraically closed characteristic-zero field `Ω`.

The subgroup's elements are actual integral automorphisms `f : A ≅ A`
whose constructed dual satisfies `f^vee ∘ lam ∘ f = lam`.
The target universally quantifies over the existing dual construction's
explicit prerequisites and choices: pullback-tensor preservation,
composition, unit coherence, associativity, unitor comparison, symmetry,
Picard-zero pullback and universal base change, the Mumford Picard-zero
statement, dual representability and geometry, and an inverse Poincare
bundle with evaluation. `Ω : Type u`, the schemes, the dual and all
bundles retain the construction's universe `u`. No positive-dimension
restriction is imposed.

The input polarization is the existing actual isogeny together with its
ample Mumford presentations on geometric fibres. Finiteness, finite
order, Rosati positivity, and a supplied abstract automorphism group are
absent from the target's hypotheses. The target does not assert any of
its explicit construction prerequisites unconditionally.

`polarizedAut_isOfFinOrder` is a proved conditional consequence of this
target: given a proof of `PolarizedAutomorphismFinitenessStatement` and
the geometric data, each element of the actual subgroup has finite
order. It installs exactly the target's resulting `Finite` instance and
uses the general finite-group theorem `isOfFinOrder_of_finite`.
`polarizedAut_exists_pow_eq_one` gives a positive natural exponent `n`
with `f ^ n = 1` in the integral subgroup and the same equation for its
image under the published `polarizedAutRationalization` bridge.
The latter follows by mapping the integral power equation through that
group homomorphism. These helpers do not prove the finiteness target.

The exact original-source correspondence for finiteness is J. S. Milne,
*Abelian Varieties*, 1986 article, corrected author revision January 2,
2022, Proposition 17.5(a), printed and one-based PDF p.37, registered
source `milne-abelian-varieties-1986-author-2022`. That proposition is
stated over an arbitrary field; the present target restricts to the
algebraically closed characteristic-zero scope needed by the consumer.
Its proof places the integral automorphisms in a discrete integral
endomorphism lattice intersected with a compact level set of the
positive Rosati trace form. The cited ingredients are Theorem 17.3,
pp.35–36, and finite rank of integral Hom from Theorem 12.5, p.21.
These pages and the complete registered author errata snapshot
`milne-abelian-varieties-1986-errata-2026-10-25` were read; the snapshot
says all listed corrections are incorporated in the retained version.

The finite-order helpers are internal consequences of part (a) and
functorial rationalization. They do not formalize Proposition 17.5(b)'s
torsion-level rigidity criterion. No finiteness of the entire rational
polarization-preserving self-isogeny group is claimed. The reduction of
a rational self-isogeny to an isogenous integral model remains in
Task 5946.
