# Uniqueness of Langlands quotients for `GL_n(ℂ)`

Module `Langlands.Representation.Archimedean.ComplexLanglandsQuotientUniqueProof`, namespace
`Langlands.Archimedean`, universe `uV` for the module carrier.

## Results

```
theorem complexStandardOppositeOrderHom : ComplexStandardOppositeOrderHomStatement
theorem complexLanglandsQuotientUnique : ComplexLanglandsQuotientUniqueStatement.{uV}
```

**Target.** `ComplexLanglandsQuotientUniqueStatement` is the Library statement of module
`Langlands.Representation.Archimedean.ComplexStandardSurjectionInjectiveReduction` (Knapp 1994,
Theorem 4 (a) and (c); its conventions are explained in
`ComplexStandardSurjectionInjectiveReduction.md`). For every `n : ℕ`, every complex vector
space `V : Type uV`, every `ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V` and every
`π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V` with `IsComplexGKModule n ρ π`,
`IsIrreducibleGKModule ρ π` and `IsAdmissibleGKModule ρ`, and for all lists
`ds es : List ComplexCharacterData` of length `n` that are Langlands ordered
(`IsComplexLanglandsOrdered`: the real parts of the exponents do not increase), if there are
nonzero linear maps
`A : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] V` and
`B : kFiniteFunctions (complexStandardModule n es) (unitaryCompact ℂ n) →ₗ[ℂ] V` with
`IsComplexStandardIntertwining n ρ π ds A` and `IsComplexStandardIntertwining n ρ π es B`, then
`ds.Perm es`. In words: the Langlands parameter of an irreducible admissible
`(𝔤𝔩_n(ℂ), U(n))`-module, read off from a standard module of which it is a quotient, is
unique up to order.

**Intermediate result (Orth).** `ComplexStandardOppositeOrderHomStatement` is the Library
statement of module `ComplexLanglandsQuotientUniqueReduction`: for lists `ds`, `cs` of `n`
complex characters, `ds` Langlands ordered and `cs` with non-decreasing real parts of the
exponents, every nonzero linear map `T` from the `U(n)`-finite functions of the standard module
of `ds` to those of `cs` with
`IsComplexStandardIntertwining n (complexStandardRep n cs) (complexStandardLie n cs) ds T`
forces `ds.Perm cs`.

Neither theorem has hypotheses beyond those inside its statement.

## Proof

The proof composes Library theorems; it introduces no new mathematics.

### 1. Orth (`complexStandardOppositeOrderHom`)

`complexStandardOppositeOrderHomReduction : ComplexStandardOppositeOrderHomReductionStatement`
(module `ComplexStandardOppositeOrderHomReduction`) proves E → TP → Orth. Its two inputs are
supplied as follows.

* **E**, `ComplexStandardHomExponentStatement` (module `ComplexStandardHomExponent`): a nonzero
  intertwining map `X(d) → X(c)` between `U(n)`-finite principal series forces
  `p(c) = σ·p(d) + u` and `q(c) = σ·q(d) + v` for one permutation `σ` and nonnegative integer
  combinations `u`, `v` of the simple roots, where `p = t + l/2`, `q = t - l/2`. The term is
  `complexStandardHomExponentJacquetReduction complexStandardJacquetExponent`:
  - `complexStandardJacquetExponent : ComplexStandardJacquetExponentStatement` (module
    `ComplexStandardJacquetExponentProof`) describes the exponents of all nonzero Jacquet
    functionals on `X(d)` in this shape;
  - `complexStandardHomExponentJacquetReduction` (module
    `ComplexStandardHomExponentJacquetReduction`) proves JE → E: for a nonzero intertwining
    map `T`, the functional `f ↦ (T f)(1)` is a nonzero Jacquet functional on `X(d)` whose
    exponents are those of `c`.
* **TP**, `ComplexStandardHomTransposeStatement` (module `ComplexStandardHomTranspose`): a
  nonzero intertwining map `X(d) → X(c)` gives a nonzero intertwining map `X(c⁻¹) → X(d⁻¹)`.
  The term is `ComplexStandardHomTransposeProof.complexStandardHomTranspose` (module
  `ComplexStandardHomTransposeProof`).

The reduction itself (see `ComplexStandardOppositeOrderHomReduction.md`) applies E to `T` and
to the transpose of `T`, and compares prefix sums of the real parts of the exponents: the
orders of `ds` and `cs` force both shifts to vanish, so `cs` is `ds` permuted by `σ`.

### 2. The target (`complexLanglandsQuotientUnique`)

`complexLanglandsQuotientUniqueReduction : ComplexLanglandsQuotientUniqueReductionStatement.{uV}`
(module `ComplexLanglandsQuotientUniqueReduction`) proves S1 → Orth → target. Its inputs are

* **S1**, `ComplexLanglandsSubrepresentationStatement.{uV}` (module
  `ComplexLanglandsQuotientReduction`): every irreducible admissible module embeds, by a
  nonzero intertwining map `E`, into the `U(n)`-finite part of the standard module of a list
  `cs` of length `n` with non-decreasing real parts. The term is the Library theorem
  `complexLanglandsSubrepresentation` (module `ComplexLanglandsSubrepresentationProof`).
* **Orth**, the theorem `complexStandardOppositeOrderHom` of step 1.

The reduction (see `ComplexLanglandsQuotientUniqueReduction.md`) runs as follows. Since `V` is
irreducible, the nonzero intertwining map `A` is onto
(`surjective_of_isComplexStandardIntertwining`), so `E ∘ A` is a nonzero intertwining map from
the standard module of `ds` into that of `cs`. Orth gives `ds.Perm cs`. In the same way
`es.Perm cs`, hence `ds.Perm es`.

The universe parameter `uV` of the target is passed through to S1 unchanged.

## Dependencies

All inputs are Library theorems:

| Name | Module | Statement |
| --- | --- | --- |
| `complexLanglandsQuotientUniqueReduction` | `ComplexLanglandsQuotientUniqueReduction` | S1 → Orth → target |
| `complexLanglandsSubrepresentation` | `ComplexLanglandsSubrepresentationProof` | S1 |
| `complexStandardOppositeOrderHomReduction` | `ComplexStandardOppositeOrderHomReduction` | E → TP → Orth |
| `complexStandardHomExponentJacquetReduction` | `ComplexStandardHomExponentJacquetReduction` | JE → E |
| `complexStandardJacquetExponent` | `ComplexStandardJacquetExponentProof` | JE |
| `ComplexStandardHomTransposeProof.complexStandardHomTranspose` | `ComplexStandardHomTransposeProof` | TP |

All modules are in `Langlands.Representation.Archimedean`.
