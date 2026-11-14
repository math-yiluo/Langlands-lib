# Reduction of the irreducibility of generic standard modules for `GL_n(ℂ)`

Worker 376 wrote this module for task `d3d2a4fc-0566-4045-b7c0-9ee47ceb167b` (Task 6311). That
task's target is the Library's `Langlands.Archimedean.ComplexGenericStandardInjectiveStatement`
(S2, module `Langlands.Representation.Archimedean.ComplexGenericParameterReduction`). S2 says:
for every list `ds` of `n` complex characters in the Langlands order, every surjective
intertwining map `A` from the `U(n)`-finite functions of the standard module of `ds` onto an
irreducible admissible generic `(𝔤𝔩_n(ℂ), U(n))`-module is injective.

This module defines *large* modules and states three results, each with its own source. It
proves that together they imply S2. It also proves that the first two alone imply the
Library's `ComplexGenericStandardParameterStatement`. All declarations are in the namespace
`Langlands.Archimedean`. The Lean names `IsComplexGKModule`, `IsIrreducibleGKModule`,
`IsAdmissibleGKModule`, `IsComplexGenericGKModule`, `HasComplexStandardParameter`,
`kFiniteFunctions`, `complexStandardModule` and `unitaryCompact` are the Library's; see
`GKModule.md` and `StandardModule.md`. `IsComplexLanglandsOrdered` and
`IsComplexStandardIntertwining` are defined, and their conventions explained, in
`ComplexGenericParameterReduction.md`.

Throughout, `𝔤 = ℂ ⊗[ℝ] 𝔤𝔩_n(ℂ)` is the complexification of the real Lie algebra `𝔤𝔩_n(ℂ)`.
Its Lie algebra structure is Mathlib's base change of the commutator bracket on matrices.
`U = UniversalEnvelopingAlgebra ℂ 𝔤` is its universal enveloping algebra. For a Lie algebra map
`π : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ V`, `UniversalEnvelopingAlgebra.lift ℂ π : U →ₐ[ℂ] Module.End ℂ V`
is the algebra map that extends `π`; we write `π̃` for it. `Z = Subalgebra.center ℂ U` is the
center of `U`.

## Definition: `IsComplexLargeGKModule n π`

For `π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V`, `IsComplexLargeGKModule n π`
says: every `u ∈ U` with `π̃ u = 0` lies in `Submodule.span U S`, where
`S = {z | z ∈ Z ∧ π̃ z = 0}`. `U` acts on itself by left multiplication, so this span is the
left ideal `U · S`. Its generators are central, so it is a two-sided ideal. Every element of
`U · S` kills `V`. So the definition says exactly

  `Ann_U(V) = U · (Z ∩ Ann_U(V))`.

Provenance. Vogan calls an irreducible `(𝔤, K)`-module `X` *large* if its annihilator is the
minimal primitive ideal (`provided-01cbf718…`, Vogan 1978, Definition 6.1, p. 89). Kostant
writes the same condition as `U_V = U Z_χ` (Kostant 1978, Theorem 3.9, (3.9.7), p. 142). Here
`χ` is the infinitesimal character of `V` and `Z_χ = ker χ`, and `U Z_χ` is the minimal
primitive ideal with infinitesimal character `χ` (Kostant 1978, Theorem 3.9: "`U_V` is
necessarily a minimal primitive ideal. That is, … (3.9.7) `U_V = U Z_χ`"). If `Z` acts on `V`
by a character `χ`, and `V ≠ 0`, then `Z ∩ Ann_U(V) = ker χ`. In that case the Lean definition
is exactly Kostant's (3.9.7) and Vogan's Definition 6.1. For a module without an infinitesimal
character the Lean condition is still meaningful but is not compared with the sources. Every
module to which this file applies the definition is irreducible and admissible. Such a module
has an infinitesimal character, because `Z` preserves its finite-dimensional `U(n)`-isotypic
components (`U(n)` is connected, so `Ad(U(n))` fixes `Z`), and by Schur's lemma.

Mathlib's `Subalgebra.center ℂ U` is the set of elements of `U` that commute with every
element of `U`. Mathlib's `Submodule.span U S`, for `U` viewed as a module over itself, is the
set of finite sums `∑ uᵢ zᵢ` with `uᵢ ∈ U` and `zᵢ ∈ S`.

## Statement K: `ComplexGenericLargeStatement`

For every `n`, every complex vector space `V`, every `ρ` and every `π`: if
`IsComplexGKModule n ρ π`, `IsIrreducibleGKModule ρ π`, `IsAdmissibleGKModule ρ` and
`IsComplexGenericGKModule n π`, then `IsComplexLargeGKModule n π`.

Sources: Kostant 1978, Theorem D (p. 104) = Theorem 3.9 (p. 142); Matumoto 1987, the
definition of `Wh*` (p. 221) and Corollary 5 (p. 223), which restates Kostant's Theorem D. Both
are in the folder `provided-01cbf718…`. Kostant's Theorem 3.9 reads: let `U` be the enveloping
algebra of a complex semisimple Lie algebra, and let `V` be a `U`-module with infinitesimal
character `χ`. If either `V` or its full dual `V'` has a nonzero Whittaker vector, then
`U_V = U Z_χ`. Matumoto writes the Whittaker vectors of the dual directly:
`Wh*(M) = {w ∈ M* | w(X·v) = ψ(X) w(v) for all v ∈ M and X ∈ 𝔫}`.

How the Library's genericity matches these sources. `IsComplexGenericGKModule n π` gives a
nonzero linear functional `ℓ : V →ₗ[ℂ] ℂ` (an element of the full algebraic dual) and complex
numbers `aᵢ ≠ 0` with `ℓ(π(1 ⊗ X) v) = i·Re(∑ᵢ aᵢ X_{i,i+1}) ℓ(v)` for every strictly upper
triangular `X`. Both sides are complex linear in the first tensor factor. So `ℓ ∈ Wh*(V)` for
the complexification `𝔫 = ℂ ⊗[ℝ] 𝔫(ℂ)` of the real Lie algebra of strictly upper triangular
complex matrices, and the character `ψ(z ⊗ X) = z · i·Re(∑ᵢ aᵢ X_{i,i+1})`. Under the
isomorphism `ℂ ⊗[ℝ] 𝔤𝔩_n(ℂ) ≅ 𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`, `z ⊗ X ↦ (zX, z X̄)`, the subalgebra `𝔫`
becomes the nilradical `𝔫(ℂ) × 𝔫(ℂ)` of the Borel subalgebra `𝔟 × 𝔟`. Since
`Re w = (w + w̄)/2`, `ψ` becomes `(Y, W) ↦ (i/2)(∑ᵢ aᵢ Y_{i,i+1} + ∑ᵢ āᵢ W_{i,i+1})`. All
`aᵢ` are nonzero, so `ψ` is nonzero on every simple root space of both factors: it is
nonsingular in Kostant's and Matumoto's sense. `𝔤 ≅ 𝔤𝔩_n × 𝔤𝔩_n` is reductive rather than
semisimple. Its center acts on an irreducible admissible module by scalars, so Kostant's
theorem for the semisimple part `𝔰𝔩_n × 𝔰𝔩_n` gives the conclusion for `𝔤`. Proving K means
carrying out these steps (including the existence of the infinitesimal character) and
formalizing Kostant's Theorem 3.9.

## Statement V1: `ComplexLargePrincipalSeriesStatement`

For every `n`, `V`, `ρ` and `π`: if `IsComplexGKModule n ρ π`, `IsIrreducibleGKModule ρ π`,
`IsAdmissibleGKModule ρ` and `IsComplexLargeGKModule n π`, then there is
`ds : List ComplexCharacterData` with `HasComplexStandardParameter n ρ π ds`. That is,
`ds.length = n` and there is an injective intertwining map from the `U(n)`-finite functions of
`complexStandardModule n ds` into `V`.

Source: Vogan 1978, Theorem 6.2, (a) ⇒ (f), p. 89 (folder `provided-01cbf718…`). The theorem
is for a quasisplit linear reductive group `G` with abelian Cartan subgroups. `GL_n(ℂ)`, as a
real group, is such a group, with maximal compact subgroup `U(n)`, minimal parabolic subgroup
`P = B` (upper triangular) and Cartan subgroup `MA` = the diagonal torus. (f) says that a large
irreducible `X` is infinitesimally equivalent to `Ind_{P'}^G(δ' ⊗ ν' ⊗ 1)`, for a cuspidal
parabolic subgroup `P' = M'A'N' ⊇ P` and a limit of discrete series `δ'` of `M'`. For a complex
group, `M'` has a compact Cartan subgroup only when its semisimple part is trivial. So
`P' = B` and `δ'` is a character of `M = U(1)^n`. Hence `X` is infinitesimally equivalent to a
principal series `I(σ₁, …, σ_n)` of characters `σᵢ = [z]^{lᵢ} |z|_ℂ^{tᵢ}` (Knapp's (4.1)–(4.2);
`knapp-1994-archimedean-llc`, p. 405). `ComplexGenericParameterReduction.md` explains why the
Library's `complexStandardModule n ds` is the same principal series as Knapp's. An
infinitesimal equivalence is an isomorphism of Harish-Chandra modules. It is therefore an
injective (indeed bijective) intertwining map from the `U(n)`-finite functions of the standard
module into `V`, which is `HasComplexStandardParameter`.

## Statement V2: `ComplexStandardSurjectionInjectiveStatement`

For every `n`, `V`, `ρ`, `π`, `ds` and `A : kFiniteFunctions (complexStandardModule n ds)
(unitaryCompact ℂ n) →ₗ[ℂ] V`: if `IsComplexGKModule n ρ π`, `IsIrreducibleGKModule ρ π`,
`IsAdmissibleGKModule ρ`, there is `ds'` with `HasComplexStandardParameter n ρ π ds'`,
`ds.length = n`, `IsComplexLanglandsOrdered ds`, `A` is surjective, and
`IsComplexStandardIntertwining n ρ π ds A`, then `A` is injective.

Source: Knapp 1994, Theorem 4 (a) and (c), p. 405 (PDF page 415), due to Želobenko and
Naimark. (a): if `Re t₁ ≥ ⋯ ≥ Re t_n`, then `I(σ₁, …, σ_n)` has a unique irreducible quotient
`J(σ₁, …, σ_n)`. (c): `J(σ)` and `J(σ')` are infinitesimally equivalent if and only if `σ'` is
a permutation of `σ`. This is the uniqueness half of the Langlands classification. The order
hypothesis cannot be dropped (see the `GL_2(ℂ)` example in
`ComplexGenericParameterReduction.md`).

An informal argument, as a guide for the proof task. Let `X = V`. `X` is irreducible and
receives an injective intertwining map from `I(ds')`. The image is a nonzero invariant subspace,
so `X ≅ I(ds')` and `I(ds')` is irreducible. Let `σ''` be the Langlands-ordered rearrangement
of `ds'`. Principal series whose parameters differ by a permutation have the same composition
factors. (This holds because their global characters agree; it is standard but not in a
registered source.) So `I(σ'')` is irreducible and isomorphic to `X`, and
`J(σ'') = I(σ'') ≅ X`. `A` is surjective, so `X` is an irreducible quotient of `I(ds)`, and by
(a) `X ≅ J(ds)`. By (c), `ds` is a permutation of `σ''`. Hence `I(ds)` has the same composition
factors as `I(ds')`, so it is irreducible. The kernel of `A` is then a proper invariant
subspace, so it is `0`. Another route compares `U(n)`-multiplicities: the Langlands quotient
contains the minimal `U(n)`-type of `I(ds)`, so `ds` and `ds'` have the same weights `lᵢ` up
to permutation; then `I(ds)` and `I(ds')` have equal finite `U(n)`-multiplicities, and the
surjection `A` is injective on each isotypic component.

## Statement and proof of the reduction

`ComplexGenericStandardInjectiveReductionStatement` (universe `uV`) is the proposition

  `ComplexGenericLargeStatement → ComplexLargePrincipalSeriesStatement →
    ComplexStandardSurjectionInjectiveStatement → ComplexGenericStandardInjectiveStatement`.

`complexGenericStandardInjectiveReduction` proves it. Take the hypotheses of S2 for `n`, `V`,
`ρ`, `π`, `ds` and `A`. K, applied to the GK-module, irreducibility, admissibility and
genericity hypotheses, shows that `π` is large. V1 then gives a list `ds'` with
`HasComplexStandardParameter n ρ π ds'`. V2, applied to this, to `ds.length = n`, to the
Langlands order of `ds`, to the surjectivity of `A` and to the intertwining property of `A`,
gives that `A` is injective.

## The first two statements alone

`complexGenericStandardParameter_of_large` proves that `ComplexGenericLargeStatement` and
`ComplexLargePrincipalSeriesStatement` together imply the Library's
`ComplexGenericStandardParameterStatement` (module
`Langlands.Representation.Archimedean.GKModule`). That statement concludes, for every
irreducible admissible generic module, that there exists `ds` with
`HasComplexStandardParameter n ρ π ds`. The proof applies K and then V1. This route does not
use the Langlands classification (`ComplexLanglandsQuotientStatement`) or V2. It is recorded
here because S2 itself is only used to prove that statement, in
`complexGenericParameterReduction`.

## Scope

None of K, V1 or V2 is proved here; each needs a separate proof task. Like S1 and S2, they
are stated for the Library's algebraic `(𝔤, K)`-modules and its `complexStandardModule`. Their
truth relies on identifying `kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)`
with the Harish-Chandra module of the classical principal series. The prerequisites that
the Task 6311 contract lists are covered as follows. The passage from algebraic Whittaker
functionals to genericity in the sense of the sources is K, in the form "generic ⇒ large".
The irreducibility of a standard module with generic Langlands quotient is V1 together with
V2, which is the route of Vogan 1978 cited by Jacquet 2009 (p. 9, "For an algebraic proof of
these results, see [24]") and Casselman–Shahidi 1998 (p. 562). Jacquet's own argument, through
uniqueness of continuous Whittaker functionals, is not used: algebraic Whittaker functionals on
a large irreducible module are not unique (Kostant 1978, Theorem 6.8.1, p. 182, stated for
connected quasi-split semisimple groups: their space has dimension `|W|`, `W` the little
Weyl group, which is `S_n` for `GL_n(ℂ)`).
