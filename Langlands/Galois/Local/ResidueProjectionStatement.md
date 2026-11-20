# The residue projection of a separable closure: statements

Worker 988 authors this statement unit for Task 7421. Its two declarations are
Prop-valued definitions in `Langlands.LocalGalois`. They state, for a
nonarchimedean local field of either characteristic and any separable closure,
every property of the residue projection that the published characteristic-zero
statement `LocalResidueProperties` (`Galois/Local/AbsoluteStatement.lean`) states
for the algebraic closure. The objects are Task 7404's general declarations in
`Langlands.LocalGalois.SepClosed` (`Galois/Local/AbsoluteDefinitions.lean`). The
statements are targets for later proof tasks; nothing here proves them, and none
is used as a hypothesis of a construction.

## Parameters

`ResidueProjectionProperties K Ω` takes `K : Type uK` with `[Field K]
[ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]` and
`Ω : Type uΩ` with `[Field Ω] [Algebra K Ω] [IsSepClosure K Ω]`, and returns
`Prop`. There is no hypothesis on the characteristic. Task 7404's declarations
need `[Algebra.IsAlgebraic K Ω]`, which Mathlib derives from `IsSepClosure`.
From the residue-closure clauses on they also need `[IsSepClosed Ω]`, which is the
theorem `IsSepClosure.sep_closed K`, not an instance. The body therefore starts with
`haveI : IsSepClosed Ω := IsSepClosure.sep_closed K`. This installs a proof of a
`Prop`-valued class and adds no hypothesis.

`ResidueProjectionExactness` states `ResidueProjectionProperties K Ω` for every
`K : Type uK` and every `Ω : Type uΩ` with the instances above; the fields and
their instances are quantified inside it. Its type is `Prop`, with the two
independent universe parameters `uK` and `uΩ`.

## The statement in words

Write `G = Ω ≃ₐ[K] Ω` with its Krull topology, `B = SepClosed.closureIntegers K Ω`
for the integers of `Ω` (the valuation ring of the spectral extension
`SepClosed.closureValuation K Ω` of the local norm of `K`), `k = 𝓀[K]`,
`ρ = SepClosed.absoluteResidueHom K Ω : G → Field.absoluteGaloisGroup k` for the
residue projection and `I = SepClosed.absoluteInertia K Ω` for inertia.
`ResidueProjectionProperties K Ω` is the conjunction of the following 22 clauses,
in this order:

1. The topology of the published local norm `localNormedField K` is the given
   topology of `K`. The next three lines install that norm and its ultrametric and
   completeness certificates.
2. The residue field `k` is finite.
3. `closureValuation K Ω` extends the valuation of `K` (`Valuation.HasExtension`).
4. The integer ring of the valuation of that norm is the integer ring of the given
   valuation of `K`.
5. An element of `Ω` lies in `B` exactly when it is integral over `𝒪[K]`.
6. Every `σ ∈ G` preserves `closureValuation K Ω`.
7. With `SepClosed.residueAlgebra K Ω`, the residue field of `B` is an algebraic
   closure of `k`. This is the clause the task keeps unchanged. In characteristic
   `p` it holds because the residue field of `B` is separably closed and `k`, being
   finite, is perfect.
8. The comparison `SepClosed.residueClosureEquiv K Ω` of the residue field of `B`
   with `AlgebraicClosure k` sends the residue of the image of every `a ∈ 𝒪[K]`
   under `SepClosed.integerMap K Ω` to the image of the residue of `a`.
9. For all `σ ∈ G` and `x ∈ B`, `ρ(σ)` sends the residue of `x` (through that
   comparison) to the residue of `integerAut K Ω σ x`.
10. – 12. `ρ` is continuous, surjective and open.
13. The kernel of `ρ` is `I`.
14. `σ ∈ I` exactly when `σ` acts trivially on the residues of all elements of `B`.
15. `I` is the inverse image of Mathlib's inertia subgroup of the valuation subring
    `B` under `decompositionHom K Ω`.
16. – 20. `I` is normal and closed, and in the subspace topology it is compact,
    totally disconnected and Hausdorff.
21. There is a topological group isomorphism `G/I ≃ₜ* Field.absoluteGaloisGroup k`
    sending the class of every `σ` to `ρ(σ)`.
22. For every intermediate field `E` of `Ω/K` that is normal over `K`, every
    `σ ∈ G` and every `y` in the residue field of the integers of `E`, reduction
    commutes with restriction: through `residueInclusion K Ω E`, `ρ(σ)` acts on the
    image of `y` as the residue action `residueHom K E` of `σ.restrictNormal E`.

## Derivation from the characteristic-zero statement

The clauses are those of `LocalResidueProperties K` with the substitutions the task
prescribes:

| `LocalResidueProperties K` (characteristic 0) | `ResidueProjectionProperties K Ω` |
| --- | --- |
| `[CharZero K]` | dropped; `[IsSepClosure K Ω]` added |
| `AlgebraicClosure K` | `Ω` |
| `Field.absoluteGaloisGroup K` | `Ω ≃ₐ[K] Ω` |
| `localClosureValuation K` | `SepClosed.closureValuation K Ω` |
| `closureIntegers K` | `SepClosed.closureIntegers K Ω` |
| `standardResidueAlgebra K` | `SepClosed.residueAlgebra K Ω` |
| `localResidueClosureEquiv K` | `SepClosed.residueClosureEquiv K Ω` |
| `localIntegerMap K` | `SepClosed.integerMap K Ω` |
| `absoluteResidueHom K` | `SepClosed.absoluteResidueHom K Ω` |
| `absoluteInertia K` | `SepClosed.absoluteInertia K Ω` |
| `integerAut K (AlgebraicClosure K)`, `decompositionHom K (AlgebraicClosure K)`, `residueInclusion K (AlgebraicClosure K) E` | the same declarations at `Ω` |
| `LocalResidueProperties K` | `ResidueProjectionProperties K Ω` |
| `PadicResidueExactness` | `ResidueProjectionExactness` |

The left column's characteristic-zero declarations are, by Task 7404, the general
ones at `Ω = AlgebraicClosure K`. A private check file compiled the following in
this environment:

```lean
example (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K] :
    ResidueProjectionProperties K (AlgebraicClosure K) ↔ LocalResidueProperties K :=
  Iff.rfl

example (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K] :
    SepClosed.absoluteInertia K (AlgebraicClosure K) = absoluteInertia K :=
  rfl

example : ResidueProjectionExactness.{u, u} → PadicResidueExactness.{u} := by
  intro h p _ F T
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact h F.Carrier (AlgebraicClosure F.Carrier)
```

In characteristic zero the instance `IsSepClosure K (AlgebraicClosure K)` is
Mathlib's `IsSepClosure.of_isAlgClosure_of_perfectField`, found by instance
search. So the general statement at the algebraic closure is the published one by
`Iff.rfl`, and the universal general statement implies the p-adic one, which
quantifies over every realization `T` of a p-adic field.

## Sources

The source correspondence is that of the published characteristic-zero statement
(`Galois/Local/AbsoluteStatement.md`) and of Task 7404's `AbsoluteDefinitions.md`.
Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg, GTM 67,
Springer (1979): Chapter I §7, Propositions 20–22 and the definition of the inertia
group, pp. 20–23 (PDF 28–31); Chapter II §2, Proposition 3 and Corollaries 2–3,
pp. 28–29 (PDF 36–37); Chapter III §5, Theorems 2–3 and Corollaries 1–3,
pp. 54–55 (PDF 61–62). Registered source `serre-1979-local-fields`, file
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`. These are
finite-level results over complete discretely valued fields and do not depend on
the characteristic. The infinite statement is derived from them, and the
topological passage and the explicit transports are left to the proofs.
Separability of the residue extensions, which Serre assumes, holds because `k` is
finite.

This unit does not edit the published statement `Galois/Local/AbsoluteStatement.lean`,
the proof module `Galois/Local/AbsoluteProof.lean`, or Task 7404's definitions.
