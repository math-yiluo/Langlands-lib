# Reduction of the exact-stabilizer prime branch of Proposition 4.8

Module `Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerPrimeBranchReductionStatement`.
Statements only (Prop-valued definitions); nothing is proved here.

## Statements

- `Proposition48ExactStabilizerPrimeBranchReductionStatement.{uF, uV}`: twelve
  named interfaces imply the published target
  `Proposition48ExactStabilizerPrimeBranchStatement.{uF, uV}` (module
  `HarrisProposition48ExactStabilizerBranchStatement`, unchanged).
- `Proposition48ExactStabilizerPrimeBranchReductionTCStatement.{uF, uV}`: the
  same interfaces, with `WeakInductionConjugateInverseSelfDualTCStatement` in
  place of `WeakInductionConjugateInverseSelfDualStatement`, imply
  `Proposition48ExactStabilizerPrimeBranchTCStatement.{uF, uV}`.

The premises of the targets themselves (Theorem 1.2, rigidity, isobaric
invariance, B2, B3, B4, restricted B7, the bridge, in their general or TC forms)
stay premises of the targets; the reductions add the twelve interfaces in front.
Universes: `uF` is the local-field universe of `Proposition48Problem`, `uV` the
carrier universe; the number fields of the problems are in `Type`, so the
general interfaces are used at field universe `0`.

The interfaces, in the order of the implication:

| # | Declaration | Module (task) |
|---|---|---|
| 1 | `Proposition48MackeyFibreStatement.{uF}` | `HarrisProposition48MackeyTransportStatement` (Task 7823) |
| 2 | `Proposition48MackeyConstituentGaloisConjugateStatement.{uF, uV}` | same |
| 3 | `Proposition48MackeyChildTransportStatement.{uF, uV}` | same |
| 4 | `Proposition48PrimeInducedParameterStagesStatement.{uF}` | same |
| 5 | `Proposition48PrimeInductionStagesStatement.{uF, uV}` | same |
| 6 | `Proposition48InducedParameterRegularAlgebraicStatement.{uF}` | same |
| 7 | `WeakInductionConjugateInverseSelfDualStatement.{uV, 0, 0}` (TC form in the TC reduction) | same |
| 8 | `ArithmeticComapUnitaryCentralCharacterStatement.{0, 0}` | `CuspidalArithmeticTransportStatement` (Task 7823) |
| 9 | `ArithmeticComapSupercuspidalComponentStatement.{0, 0, uV}` | same |
| 10 | `ConjugateSelfDualUnitaryCentralCharacterStatement.{0}` | `HarrisAuxiliaryConjugatePairStatement` (Task 7822) |
| 11 | `ConjugateSelfDualSupercuspidalConjPlaceStatement.{0, uV}` | same |
| 12 | `SplitPlaceNeConjPlaceStatement.{0}` | same |

Task 7823 is `dadd0ec0-1d72-4bdd-a5e6-c74dc98712b9`; Task 7822 is
`364f76f1-154a-4269-9b0b-4cd6dc277a09` (published by the singleton
decomposition, Task 7786).

## Sources

Harris (1998), Proposition 4.8, proof of the prime orbit, printed p.203
(`math_9611226v1.tex` lines 1646–1664, registered source
`harris-1998-local-langlands`); operator plan note
`operator-external-inputs-plan-2026-11-16`, `external-inputs-plan.tex`,
Section 4.8, lines 859–912: Remark 4.2 (lines 859–894), the prime branch
(line 908), the infinity type (lines 910–911);
operator ruling R2 (`/home/taskhub/pilot/correspondence/a79e2e832569567a8582b3c994f2fc1b.md`)
and the ruling on the bridge
(`/home/taskhub/pilot/correspondence/89b70579f7465ae3994e304e80cf284b.md`).

Harris's argument: with `q = [D : E]` Mackey classes, `A` is a principal
homogeneous space under `Gal(D/E)`, the constituent `Π(e)` of a base point and
its conjugates `α^j(Π(e))` make up the restriction, `Π = AI_{D/E} Π(e)` is the
unique representation base changing to their sum, its component at the
auxiliary place is supercuspidal by Henniart–Herb because the conjugate
components are distinct, and `Π` weakly induces `ξ`. The reductions are derived
statements, not clauses of Harris. The route follows this prime-orbit argument
with distinctness supplied by `HasDistinctMackeyComponents` (claim (2) of
Remark 4.2, in the form of B6) instead of general position. Under R2 the
children carry complex-place parameters, and restricted B7(2) gives the
output's parameters without assuming algebraicity. The separate bridge
`CuspidalComplexParameterBridgeTCStatement` is used through interface 6, in
the Library's `ArchimedeanGL.IsRegularAlgebraicCharacter` normalization.

## Proof route (not formalized here)

Fix `Q`, `D` with `Q.IsAuxiliaryExactStabilizerValid`, `Q.IsPrimeCyclicStep D`,
`Nat.card (Q.MackeyIndex D) = [D : E] = ℓ`, `Q.HasDistinctMackeyComponents D`,
and the children's solutions. Write `n = [E' : E]`. Validity
(`IsAuxiliaryExactStabilizerValidAtParity (n - 1)`) supplies
`IsSplitImaginaryQuadratic Q.p Q.K₀`, `IsNormalClosure Q.E Q.E' Q.L`,
`(Q.p : 𝓞 Q.E) ∈ Q.Ps.v.asIdeal`, `HasUniquePlaceAbove Q.L Q.Ps.v`,
`HasUniquePlaceAbove Q.L (conjPlace Q.E Q.Ps.v)`,
`IsAlgebraicAfterTwist (n - 1) Q.ξ`, `IsRelativelyRegular Q.E Q.ξ` and
`IsConjugateInverse Q.ξ`. `IsPrimeCyclicStep D` supplies `IsGalois Q.E D`,
`IsCyclic (D ≃ₐ[Q.E] D)` and the primality of `ℓ`; a generator `σ` of
`Gal(D/E)` has order `ℓ = Nat.card (D ≃ₐ[Q.E] D)`, so `σ ^ i ≠ 1` for
`0 < i < ℓ`. The compactness instance on `AdeleQuotient D` is
`compactSpace_adeleQuotient D` (a `Prop`, so all instances agree). Here
"unitary" means that the specified realization has a unitary central character
(`HasUnitaryCentralCharacter`).

1. **Fibres.** Interface 1 (with `IsNormalClosure`, `IsPrimeCyclicStep D` and
   the cardinality hypothesis) gives `D ≤ Q.conjugateField 1` and: two
   elements of `Gal(L/E)` have the same double coset iff they agree on `D`.
2. **The child of `1`.** The hypothesis for `a = 1` gives `R`, `ν`, `S`, `T` with
   `Q.IsAuxiliaryMackeyChild D 1 R`, `R.IsUntwistedSolution ν S T` (so `S`
   weakly induces `R.ξ`, is conjugate self-dual and supercuspidal at `R.Ps.v`)
   and `R.HasInducedComplexPlaceParameters S.isoClass`. Unfolding the child
   (`IsAuxiliaryMackeyChild` is `IsMackeyChild` of the paddings, which change
   only `P` and `χ`, so fields, characters and `Ps` are those of `Q` and `R`)
   gives `e : R.E ≃+* D`, `e' : R.E' ≃+* Q.mackeyField D 1` with the two
   compatibilities that interface 3 asks for, and
   `(finitePlaceEquiv e.symm R.Ps.v).asIdeal.LiesOver Q.Ps.v.asIdeal`. The
   other children are not used.
3. **The constituent over `D`.** `T₀ := S.arithmeticComap e.symm`, a cuspidal
   realization over `D` of the rank of `S`. Interface 3 (first clause, from
   `S` weakly inducing `R.ξ`): `T₀.isoClass` is a Mackey constituent of `1`.
   Interface 10 over the CM field `R.E` makes `S` unitary; interface 8 (with
   `e.symm`) makes `T₀` unitary. Interface 9 gives `T₀` a supercuspidal
   component at `w₀ := finitePlaceEquiv e.symm R.Ps.v` (the class
   `IsoClass.arithmeticComap e.symm S.isoClass` is `T₀.isoClass` by the `rfl`
   lemma `arithmeticComap_isoClass`). `w₀` lies above `Q.Ps.v` (step 2) and is
   the only place of `D` there (Library `finitePlacesAbove_subsingleton`,
   `HarrisUniquePlace.lean`, from `HasUniquePlaceAbove Q.L Q.Ps.v` and the
   scalar tower `Q.E ⊆ D ⊆ Q.L`). Interface 11 over `R.E` makes `S`
   supercuspidal at `conjPlace R.E R.Ps.v`, and interface 9 moves this to
   `wc := finitePlaceEquiv e.symm (conjPlace R.E R.Ps.v)`. This place lies
   above `conjPlace Q.E Q.Ps.v`: with the algebra `Q.E → R.E` given by
   `e.symm ∘ algebraMap Q.E D`, `R.Ps.v` lies above `Q.Ps.v`
   (`finitePlaceEquiv_liesOver`, `HarrisProposition48StabilizerComparison.lean`,
   along `e`), so `conjPlace R.E R.Ps.v`, which is by definition
   `finitePlaceEquiv (complexConj R.E).toRingEquiv R.Ps.v`, lies above
   `conjPlace Q.E Q.Ps.v` (`conjPlace_liesOver`, which rests on
   `complexConj_algebraMap`, both in `HarrisDatumCharacterRealizationProof.lean`),
   and `finitePlaceEquiv_liesOver` along `e.symm` moves this to `D`. It is the
   only place of `D` there, by `finitePlacesAbove_subsingleton` and
   `HasUniquePlaceAbove Q.L (conjPlace Q.E Q.Ps.v)`.
   Interface 3 (second clause, from `R.HasInducedComplexPlaceParameters
   S.isoClass`) gives, at every complex place `u` of `D`, a parameter `ds` of
   `T₀.isoClass` at `u` that is, up to order, the Langlands sum over the places
   of `Q.mackeyField D 1` above `u` of parameters of the Mackey character of `1`.
4. **Trivial Galois stabilizer.** Let `σ' ∈ Gal(D/E)`, `σ' ≠ 1`.
   Since `L/E` is normal (`IsNormalClosure`), `σ'` extends to some
   `τ ∈ Gal(L/E)` (Mathlib `AlgEquiv.liftNormal`, `AlgEquiv.restrictNormalHom_surjective`),
   so `((σ' x : D) : L) = τ x` for `x ∈ D`. As `σ' ≠ 1`, `τ` and `1` do not
   agree on `D`, so their double cosets differ (step 1). If
   `T₀.isoClass.IsGaloisStable σ'`, then `galoisConj σ' T₀.isoClass = T₀.isoClass`
   (Library `isGaloisStable_iff`), and interface 2 (with `a = 1`, `τ * 1 = τ`)
   makes `T₀.isoClass` a Mackey constituent of `τ`. Then
   `HasDistinctMackeyComponents` with `a = 1`, `a' = τ`, `T = U = T₀` (unitary,
   step 3), the place `w₀` and, twice, a presentation `P` of `T₀` (it exists by
   `hasSupercuspidalComponent_iff`, step 3) says that the component of `P` at
   `w₀` differs from itself, a contradiction. This is the hypothesis of
   restricted B7(2) (all `σ' ≠ 1`) and, with `σ' = σ ^ i`, `0 < i < ℓ`, that
   of B2.
5. **The class `Π` (B2).** `CyclicRegularInductionStatement` (B2) with
   `F = Q.E`, `E = D`, the generator `σ`, a character `η` with norm kernel
   (proved in the Library: `cyclicNormKernelCharacter`,
   `CyclicNormKernelCharacterProof.lean`, for the cyclic Galois extension
   `D/E`), the unitary `T₀` and step 4 gives a cuspidal class `Π` over `E` with
   `IsWeakInductionOf Π T₀.isoClass`. Let `S_Π` be a realization with
   `S_Π.isoClass = Π` (classes are quotients of realizations); B4, restricted
   B7 and interface 10 take realizations.
6. **Weak induction of `ξ`.** Interface 5 (`D ≤ conjugateField 1`, `Π` weak
   induction of the Mackey constituent `T₀.isoClass` of `1`).
7. **Conjugate self-duality.** Interface 7, with the rigidity premise of the
   target, `IsConjugateInverse Q.ξ` from validity and step 6.
8. **Supercuspidal at `Q.Ps.v` (B4).** `CyclicWeakInductionSupercuspidalStatement`
   with `F = Q.E`, `E = D`, the prime degree, `σ`, `v = Q.Ps.v` and its unique
   place `w₀`, `S_Π`, `T₀`, a presentation `P` of `T₀` supercuspidal at `w₀`
   (`hasSupercuspidalComponent_iff`), and for `0 < i < ℓ` the realization
   `U := T₀.arithmeticComap (σ ^ i).toRingEquiv.symm`, whose class is
   `galoisConj (σ ^ i) T₀.isoClass` by definition (so
   `T₀.isoClass.IsGaloisConjugate (σ ^ i) U.isoClass` by
   `isGaloisConjugate_galoisConj`). `U` is unitary by interface 8 and
   supercuspidal by interface 9 at `finitePlaceEquiv (σ ^ i).toRingEquiv.symm w₀`,
   which lies above `Q.Ps.v` (`finitePlaceEquiv_liesOver`, `σ ^ i` being an
   `E`-algebra map) and so equals `w₀`; a presentation `P_U` of `U`
   supercuspidal at `w₀` exists by `hasSupercuspidalComponent_iff`. Its
   component at `w₀` differs from that of `P` by `HasDistinctMackeyComponents`
   for `a = 1` and a lift `τ` of `σ ^ i` (step 4: different double cosets;
   interface 2: `U.isoClass` is a Mackey constituent of `τ`).
9. **The auxiliary conjugate pair.** Interface 10 over `E` makes `S_Π` unitary
   (step 7); interface 11 makes `Π` supercuspidal at `conjPlace Q.E Q.Ps.v`
   (steps 7, 8); interface 12 (`IsSplitImaginaryQuadratic Q.p Q.K₀`,
   `(Q.p : 𝓞 Q.E) ∈ Q.Ps.v.asIdeal`) gives `Q.Ps.v ≠ conjPlace Q.E Q.Ps.v`.
10. **Parameters (restricted B7(2)).** Clause (2) of
    `RestrictedCyclicWeakBaseChangeComplexPlaceStatement` with `F = Q.E`,
    `E = D` (prime cyclic step), `v₀ = Q.Ps.v` distinct from its conjugate
    (step 9), and the unique places `w₀`, `wc` (step 3) applies to the
    unitary realizations `S_Π` and `T₀`, supercuspidal at both places of their
    respective pairs (steps 3, 8, 9). With non-stability of `T₀.isoClass` under
    every `σ' ≠ 1` (step 4) and weak induction (step 5), it gives: for every complex
    place `v` of `E`, enumeration `en` of the places of `D` above `v` and lists
    `ds w` that are parameters of `T₀.isoClass` at the places `w`, `Π` has
    the parameter `complexPlaceLanglandsSum v en ds`. Take `en` from the
    `Fintype` instance of `InfinitePlacesAbove D v` and choose `ds w` by step 3
    at `u = complexPlaceAbove v w`; the data of step 3 are exactly the
    hypothesis of interface 4, which shows that the same list satisfies
    `Q.IsInducedComplexPlaceParameter v`. So
    `Q.HasInducedComplexPlaceParameters Π`.
11. **Regular algebraicity.** Interface 6, with the bridge premise of the target
    and `IsAlgebraicAfterTwist (n - 1) Q.ξ`, `IsRelativelyRegular`,
    `IsConjugateInverse` from validity, and step 10.
12. Steps 6, 11, 7 and 8 give `Q.IsSolution Π`, and with step 10
    `Q.HasParameterSolution`.

The TC reduction is the same, using the TC forms of rigidity (in interface 7),
B2 and B4. These TC forms add only `[NumberField.IsTotallyComplex F]` for the
base field `F = Q.E`; the instance comes from the CM structure of `Q.E`
(Mathlib's instance `IsCMField.isTotallyComplex`). No total complexity of `D`
is needed. Restricted B7, the bridge and interfaces 1–6 and 8–12 are the same
in both reductions.

**Premises of the target not used by this route:** Harris's Theorem 1.2
(`Harris1998Theorem12CuspidalStatement`), isobaric invariance
(`Proposition48IsobaricInvarianceStatement`, TC form in the TC target) and the
orbit lift B3 (`CyclicRegularOrbitLiftStatement`, TC form in the TC target);
rigidity is used only through interface 7. The Galois invariance of the whole
family of child constituents, which the target's Markdown sketches through
rigidity and isobaric invariance, is not needed: only the child of the trivial
double coset is used, and its conjugates are controlled by interface 2 and
`HasDistinctMackeyComponents`.

## Obligations named by the target's Markdown

The target's Markdown (section "Why the branches should hold") sketches the
prime branch and lists what its proof "must establish, not assume". Where each
is met:

| Obligation (target's Markdown) | Where it is met |
|---|---|
| unitary central character of the child's constituent `S_a` | interface 10 over `R.E` (Task 7822), moved to `D` by interface 8 (Task 7823) |
| unitary central character of `Π` | interface 10 over `Q.E` (Task 7822), after step 7 |
| supercuspidality at `conjPlace Q.E Q.Ps.v` | interface 11 (Task 7822) for `Π`; for `T₀`, interface 11 over `R.E` with interface 9 |
| `Q.Ps.v ≠ conjPlace Q.E Q.Ps.v` | interface 12 (Task 7822) |
| unique places of `D` above both places | proved in the Library: `finitePlacesAbove_subsingleton`; their existence from the child (step 2) with `finitePlaceEquiv_liesOver`, `conjPlace_liesOver` (step 3) |
| transport of `S_a` and its parameters from `R.E` to `D` | interfaces 3, 8, 9 (Task 7823) |
| permutation identities (Mackey's formula for the induced parameters) | interface 4 (Task 7823), with interface 3 at the `D` level |
| Galois translates of the constituent, trivial stabilizer for restricted B7(2) | step 4: interface 2 (Task 7823) and the target's hypothesis `HasDistinctMackeyComponents`; deriving that hypothesis from B6 is the separate `Proposition48ExactStabilizerDistinctnessStatement` (proof task 7784, `164e0acf-5a60-4650-a62a-c82f952d83c3`) |
| `Π` from Arthur–Clozel induction (B2, B3) | B2 only, with `cyclicNormKernelCharacter` (proved in the Library); B3 is not used |
| supercuspidal component of `Π` at `Q.Ps.v` | B4, with the distinct conjugate components of step 8 |
| weak induction of `ξ` (Mackey's formula) | interface 5 (Task 7823) |
| conjugate self-duality "as in the published branch" | interface 7 (Task 7823) with the rigidity premise of the target |
| parameters of `Π` from restricted B7(2) | step 10 |
| regular algebraicity from the bridge | interface 6 (Task 7823) with the bridge premise of the target |

Shared with other decompositions: interfaces 3, 6, 7, 8, 9 and 10–12 are used by
the exact-stabilizer singleton branch (Task 7786,
`794a4691-1e86-44f4-a28d-d79270146b71`); interfaces 2, 3, 5 and 7 are
obligations of the general-position prime branch (Task 7221,
`528311c0-f3fd-4553-ad48-a6bed4282b5a`). New for this branch: interfaces 1 and 4.
