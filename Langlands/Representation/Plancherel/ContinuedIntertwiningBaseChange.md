# Independent intertwiner continuations after a change of base representation

## Source and provenance

This is a derived comparison for Waldspurger, *La formule de Plancherel pour
les groupes p-adiques (d'après Harish-Chandra)*, IV.1, printed pp.276–278
(PDF pp.42–44), registered as `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

The source fixes the compact section carrier independently of the unramified
parameter on p.276. On p.277 it requires the actual representative naturality
square, conjugates actual induced operators by compact restriction, and
continues a rational operator to the nonzero locus of its whole-operator
denominator. The integral definition and the separate convergence/rationality
theorem follow on pp.277–278.

The present comparison combines these conventions with parameter translation
and uniqueness of rational continuation. It treats two independently supplied
original families, regions and continuation data. It is not a separately
numbered theorem of the article, and does not establish IV.1.1.

## General translated continuation comparison

Write `X` for the actual unramified character space of `L(F)`, and write
`tτ(χ) = τ * χ`. Here `F` is an arbitrary nonarchimedean local field, `L` is a
connected reductive group scheme over `F`, the topology on its rational points
is supplied, and its rational valuation-image projection is continuous.
The field and the four linear-space universes are independent. No
finite-dimensionality assumption is used.

`rationalOperatorContinuationData_translation_natural` takes continuation
data `p` and `q` for linear-operator families on possibly different subsets
`Ω` and `Λ` of `X`, fixed linear maps `S` and `T` between their source and
target spaces, and a nonempty ambient open subset

`D ⊆ tτ ⁻¹' Ω ∩ Λ`.

Assume the original square holds for every `χ ∈ D`:

`B(χ) ∘ S = T ∘ A(τ * χ)`.

Then the independently continued operators satisfy the same square at every
parameter in

`tτ ⁻¹' p.regularRegion ∩ q.regularRegion`.

The proof applies the imported
`rationalOperatorContinuationData_natural` to `p.translation τ` and `q`.
Translation pulls back the chosen denominator and polynomial numerator of
`p`; it does not choose replacement continuation data. The two independent
denominators remain explicit through their exact regular regions. The common
open set is contained in both regions by the supplied continuation data.

## Actual character chart and restriction

For this part let `G` be a nonarchimedean topological group, `M` an actual
subgroup, `H` a topological group, `e : H ≃ₜ* M` a topological group
equivalence, and `ν` a family of norm characters on `H`. Let `χM` denote the
induced group homeomorphism on actual unramified characters, and let `νM`
be the norm characters transported to `M`. The two canonical smooth
representations `A` and `B` of `M` have independent carrier universes.

Fix a character `τ` and an actual representation equivalence

`a : A.twist (χM τ) ≃ B`.

`transportedBaseTwistEquiv e ν τ χ a` identifies

`A.twist (χM (τ * χ)) ≃ B.twist (χM χ)`.

It first identifies the inducing actions using multiplicativity of `χM`
and commutativity of the character group, by `equivOfRepresentationEq`,
and then applies `productBaseTwistEquiv`. Both use the original vector
carriers. `transportedBaseTwistEquiv_apply` proves that its vector map
is exactly `v ↦ a v`.

For normalized induction let `P = M U` be an actual semidirect subgroup
decomposition, with `U` and `P` closed, a supplied unimodular-modulus
condition on `U`, and a continuous Levi projection. Assume `G` is locally
compact. Supply a compact open subgroup `K`, a factorization `G = P K`,
and continuity of every norm character. The theorem
`unramifiedLeviInductionCompactEquiv_transportedBaseChange` says that
restriction of the actual induced map at the corresponding translated
parameters is the fixed map

`C_P = compactInductionBaseChangeEquiv ... (χM τ) a`.

This compact map is independent of `χ` and sends each compact value
`f(k)` to `a(f(k))`. The proof uses subtype and function extensionality;
the resulting equality of vector values is definitional.
`unramifiedLeviInductionCompactEquiv_symm_transportedBaseChange` gives the
inverse restriction identity by applying target restriction and cancelling
its inverse.

Supply a second decomposition `P' = M U'` with the same hypotheses and
compact subgroup. For any two actual ambient intertwiners at the
corresponding parameters,
`compactIntertwiningOperator_transportedBaseChange_iff` proves equivalence
between their ambient square and their compact square through `C_P`
and `C_P'`. Its forward implication substitutes the inverse restriction
identity, uses the assumed ambient square and then restricts the target.
Its reverse implication tests the compact square on the restriction of an
arbitrary ambient input and uses target restriction injectivity.

## Independent actual intertwiner continuations

Now take `H = L(F)` with the field and group-scheme hypotheses above, and
an actual topological group equivalence `e : L(F) ≃ₜ* M`. All ambient
subgroup, compact factorization, modulus and continuity hypotheses from
the restriction comparison remain explicit.

Let `JA` and `JB` be arbitrary families of actual normalized-induction
intertwiners on `Ω` and `Λ`. Let `p` and `q` be independent rational
continuation data for their compact conjugates. Supply a nonempty ambient
open `D ⊆ tτ ⁻¹' Ω ∩ Λ` and assume the actual original square through
`transportedBaseTwistEquiv` for every parameter in `D`.

`continuedCompactIntertwiner_baseChange` concludes, for every parameter
in `tτ ⁻¹' p.regularRegion ∩ q.regularRegion`, that

`q.continuedOperator(χ) (C_P f) = C_P' (p.continuedOperator(τ * χ) f)`.

Its proof turns the assumed original ambient square into a compact
square using the preceding equivalence, applies the general translated
continuation comparison and evaluates the resulting linear-map equality.

`continuedInductionIntertwiner_baseChange` proves the corresponding
square for the actual continued ambient intertwiners. The `JA`
continuation uses the nonempty ambient open `tτ '' D` contained in `Ω`;
openness follows from the translation homeomorphism. The `JB`
continuation uses `D`. Thus no extra original-open hypotheses are needed.
The proof uses `continuedInductionIntertwiner_compact` to identify both
compact conjugates with their supplied continued operators, and reflects
the compact square back to the actual ambient induction spaces.
The implementation raises the recursion-depth limit locally to handle
the expanded actual-induction types; the proof uses only kernel-checked
equalities and the imported continuation constructions.

## Scope and remaining obligations

This unit preserves arbitrary field characteristic and independent field,
ambient-group and inducing-carrier universes. It does not introduce a
competing representation framework or restrict to split groups.
The actual topological Levi identification and the structural induction
hypotheses are supplied; their realization for every reductive group is
not asserted.

The original families, both rational continuation data and the original
ambient square are premises. This unit does not prove convergence or
rationality of standard integrals, nor identify the continued families
with standard integrals. The fixed ordinary compact maps retain dependence
on the chosen `a`, including its scalar ambiguity. No stabilizer or orbit
descent, parabolic independence, generic irreducibility, positivity,
nonvanishing, global `j` or `mu`, or Plancherel conclusion is claimed.
