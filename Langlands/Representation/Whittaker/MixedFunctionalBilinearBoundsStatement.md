# Separate-group functional-factor and finite-exception assembly statements

This internal statement family generalizes the same-group assembly theorems of
`Langlands.Representation.Whittaker.FunctionalBilinearBounds`
(`InvariantBilinear.length_le_one_of_unique_functional_factors`,
`InvariantBilinear.exists_exception_length_le_one_of_unique_functional_factors`,
`InvariantBilinear.exists_exception_length_le_one_of_functional_equiv`) and of
`Langlands.Representation.Whittaker.FiniteLengthBilinearBounds`
(`InvariantBilinear.exists_exception_length_le_one_of_finiteLength`) to
bilinear covariance spaces on two representations of independent groups,
with arbitrary mixed tests. No original-literature assertion is transcribed
and no external source is cited: the statements are derived assembly steps
for the unequal-rank Rankin–Selberg uniqueness work, where the two
representations live on different groups.

The module defines five Prop-valued `def` statements in namespace
`Langlands.MixedBilinear` and proves none of them. The conjunction
`FunctionalFactorAssemblyStatement` is the exact target intended for one
separate proof contribution.

## Imported constructions

The covariance spaces are the published mixed spaces of
`Langlands.Representation.Filtration.MixedBilinear`, with argument order
`forms a b χ ρ σ` and `length a b χ ρ σ`. For a group `G`, a group `H`, a test
type `I`, arbitrary functions `a : I → G`, `b : I → H` and weights
`χ : I → ℂ`, the space `forms a b χ ρ σ` consists of the bilinear forms `B`
with

```text
∀ i v w, B (ρ (a i) v) (σ (b i) w) = χ i * B v w,
```

and `length a b χ ρ σ : ℕ∞` is its actual `Module.length ℂ`. The test maps
need no homomorphism property and `I` may be empty. No second notion of mixed
covariance is introduced.

Filtrations are the actual `ObjectRepFiltration A m` over the first group and
`ObjectRepFiltration B n` over the second group, with their actual
`gradedRepresentation`. Each representation keeps its own ambient-group
filtration; nothing is restricted to a common group.

The functional conditions are the existing Whittaker notions of
`Langlands.Representation.Whittaker.Algebraic`. Below, `FA(C)` abbreviates

```text
Whittaker.HasFunctional (N := U) (θ := θ) C.ρ
```

for a representation `C` of `G`, a subgroup `U : Subgroup G` and a character
`θ : U →* ℂˣ`; `FB(D)` abbreviates the same proposition for a representation
`D` of `H`, with `U' : Subgroup H` and `θ' : U' →* ℂˣ`. `HasFunctional` means
existence of a nonzero element of `Whittaker.functionals`. These are prose
abbreviations only; the Lean statements spell out `Whittaker.HasFunctional`
and introduce no new predicate.

## Universes and quantifier shape

The groups `G : Type uG`, `H : Type uH`, the test type `I : Type uI`, the
parameter type `S : Type uS`, the spectral type `Z : Type uZ`, and the
representation carriers `A : Rep.{uV} ℂ G`, `B : Rep.{uW} ℂ H` all have
independent universes. Every statement universally quantifies inside its
definition over the groups, the test type and all remaining data; none has
outer term parameters. The universe parameter lists are

- `UniqueFunctionalFactorsLengthBoundStatement.{uG, uH, uI, uV, uW}`;
- `UniqueFunctionalFactorsFiniteExceptionStatement`,
  `FunctionalEquivFiniteExceptionStatement`,
  `AdmissibleSecondFiniteLengthExceptionStatement` and
  `FunctionalFactorAssemblyStatement`, each `.{uG, uH, uI, uS, uZ, uV, uW}`.

The coefficient field is `ℂ` throughout.

## Pair control

For fixed `C`, `D`, a parameter map `χ : S → I → ℂ` and `s : S`, the
statements 2–4 use the following *pair-control* proposition, written out in
Lean at each use:

```text
(length a b (χ s) C.ρ D.ρ ≠ 0 → FA(C) ∧ FB(D)) ∧
(FA(C) → FB(D) → length a b (χ s) C.ρ D.ρ ≤ 1).
```

The first conjunct is detection: nonzero *module length* of the actual mixed
form space forces both functional conditions. It does not refer to a
separately supplied nonzero form or functional. The second conjunct is a
conditional length bound for pairs carrying both functionals. Pair control is
always a *hypothesis* of these statements. This module neither proves pair
control for any pair, nor proves any full unequal-rank uniqueness theorem.

## 1. Unique functional positions

`UniqueFunctionalFactorsLengthBoundStatement` quantifies over groups
`G`, `H` (with `Group` instances), `I`, subgroups and characters
`U, θ, U', θ'`, representations `A : Rep.{uV} ℂ G`, `B : Rep.{uW} ℂ H`,
`m n : ℕ`, filtrations `f : ObjectRepFiltration A m`,
`g : ObjectRepFiltration B n`, tests `a : I → G`, `b : I → H`, and one fixed
weight `η : I → ℂ`. Writing `Aᵢ = f.gradedRepresentation i` and
`Bⱼ = g.gradedRepresentation j`, its hypotheses are, in order,

```text
hA      : ∃! i : Fin m, FA(Aᵢ)
hB      : ∃! j : Fin n, FB(Bⱼ)
hdetect : ∀ i j, length a b η Aᵢ.ρ Bⱼ.ρ ≠ 0 → FA(Aᵢ) ∧ FB(Bⱼ)
hbound  : ∀ i j, FA(Aᵢ) → FB(Bⱼ) → length a b η Aᵢ.ρ Bⱼ.ρ ≤ 1
```

and its conclusion is `length a b η A.ρ B.ρ ≤ 1`. The statement is purely
algebraic: there is no topology, smoothness, simplicity, admissibility or
finite-length premise, and the graded factors need not be simple or nonzero.
Unique existence counts actual graded positions, so isomorphic repeated
factors are distinct positions.

## 2. Finite exceptions with unique positions

`UniqueFunctionalFactorsFiniteExceptionStatement` quantifies over the same
data as statement 1 except that the fixed weight is replaced by a parameter
family: types `S`, `Z`, a spectral map `z : S → Z` and weights
`χ : S → I → ℂ`. It keeps `hA` and `hB` and replaces `hdetect`, `hbound` by
the pairwise finite-exception premise

```text
∀ i j, ∃ E : Finset Z, ∀ s : S, z s ∉ E → pair-control Aᵢ Bⱼ s.
```

It concludes

```text
∃ E : Finset Z, ∀ s : S, z s ∉ E → length a b (χ s) A.ρ B.ρ ≤ 1.
```

Quantifier order: each pair's exceptional set is chosen after the pair
`(i, j)` and before the parameter `s`; the final exceptional set is chosen
before `s` and before any bilinear form. No algebraicity, periodicity,
injectivity or surjectivity is assumed on `z` or `χ`. A proof is expected to
take the union over actual graded positions with the published
`InvariantBilinear.gradedExceptionSet` and its avoidance lemma
`InvariantBilinear.not_mem_pair_of_not_mem_gradedExceptionSet`, which are
independent of any ambient group.

## 3. Functional equivalences supply the positions

`FunctionalEquivFiniteExceptionStatement` quantifies over groups `G`, `H` with
`Group`, `TopologicalSpace` and `IsTopologicalGroup` instances, the test
type `I`, and then, in order,

```text
U   : Subgroup G,  hU  : Jacquet.Localization.IsLimitOfCompactSubgroups U
θ   : U →* ℂˣ,     hθ  : IsLocallyConstant (fun u : U => (θ u : ℂ))
U'  : Subgroup H,  hU' : Jacquet.Localization.IsLimitOfCompactSubgroups U'
θ'  : U' →* ℂˣ,    hθ' : IsLocallyConstant (fun u : U' => (θ' u : ℂ)).
```

For all `A`, `B`, `m`, `n`, `f`, `g`, `a`, `b`, `S`, `Z`, `z`, `χ` it assumes

```text
IsSmooth A.ρ
IsSmooth B.ρ
eA : Whittaker.functionals U θ A.ρ ≃ₗ[ℂ] ℂ
eB : Whittaker.functionals U' θ' B.ρ ≃ₗ[ℂ] ℂ
```

and the pairwise finite-exception premise of statement 2, and draws the same
conclusion as statement 2. The unique-position hypotheses are *not* retained:
in a proof they come from smoothness, the one-dimensional total functional
spaces and exactness of functionals, as in the published
`Whittaker.existsUnique_hasFunctional_factor`, applied separately over `G` and
over `H`. The supplied filtrations need not have simple factors.

## 4. Finite length with an admissible second factor

`AdmissibleSecondFiniteLengthExceptionStatement` keeps the topological group,
compact-limit and locally constant character data of statement 3, in the same
order, and then assumes compact-open cofinality for the second group only:

```text
hH : ∀ L : OpenSubgroup H, ∃ K : OpenSubgroup H, IsCompact (K : Set H) ∧ K ≤ L.
```

For all `A : Rep.{uV} ℂ G`, `B : Rep.{uW} ℂ H`, `a`, `b`, `S`, `Z`, `z`, `χ`
it assumes, in order,

```text
hA    : IsSmooth A.ρ
hB    : IsAdmissible B.ρ
hfinA : IsFiniteLength (MonoidAlgebra ℂ G) A.ρ.asModule
hfinB : IsFiniteLength (MonoidAlgebra ℂ H) B.ρ.asModule
eA    : Whittaker.functionals U θ A.ρ ≃ₗ[ℂ] ℂ
eB    : Whittaker.functionals U' θ' B.ρ ≃ₗ[ℂ] ℂ
```

and the uniform irreducible-pair premise: for all `C : Rep.{uV} ℂ G` and
`D : Rep.{uW} ℂ H`,

```text
IsSmooth C.ρ → IsAdmissible D.ρ →
Representation.IsIrreducible C.ρ → Representation.IsIrreducible D.ρ →
∃ E : Finset Z, ∀ s : S, z s ∉ E → pair-control C D s.
```

It concludes

```text
∃ E : Finset Z, ∀ s : S, z s ∉ E → length a b (χ s) A.ρ B.ρ ≤ 1.
```

No filtration is supplied: a proof chooses actual simple filtrations with
`ObjectRepFiltration.ofFiniteLength`, obtains smoothness of the first graded
factors from `ObjectRepFiltration.isSmooth_gradedRepresentation`, and must
derive admissibility of the second graded factors, for instance by
`isAdmissible_of_injective` along the inclusion of the upper filtration step
followed by `Unramified.SphericalExistence.isAdmissible_of_surjective hH` along
the actual graded projection. The compact-open cofinality hypothesis is there
for that admissibility transfer. The pair premise asks for admissibility of
`D`, not mere smoothness, and the statement asserts no implication from
smooth irreducibility to admissibility. The first group need not satisfy
compact-open cofinality and the first representation need not be
admissible. Each pair's exceptional set is chosen after `C`, `D` and before
`s`; the final set is chosen before `s` and every bilinear form.

## Bundle and scope

`FunctionalFactorAssemblyStatement` is definitionally

```text
UniqueFunctionalFactorsLengthBoundStatement.{uG, uH, uI, uV, uW} ∧
  UniqueFunctionalFactorsFiniteExceptionStatement.{uG, uH, uI, uS, uZ, uV, uW} ∧
    FunctionalEquivFiniteExceptionStatement.{uG, uH, uI, uS, uZ, uV, uW} ∧
      AdmissibleSecondFiniteLengthExceptionStatement.{uG, uH, uI, uS, uZ, uV, uW}
```

with every constituent fully quantified over its own data. The algebraic
graded-sum bounds this assembly relies on are separate targets of
`Langlands.Representation.Filtration.MixedBilinearBoundsStatement`; the
concrete unequal-rank test adapter, the source irreducible-pair rigidity
lemma that would supply pair control, and the full unequal-rank uniqueness
theorem all remain separate work.
