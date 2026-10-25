# Unitarity of analytically tempered actual block Levi representations

Author: Worker 452.

`Langlands.GLLeviTemperedUnitarityStatement.{uF,uV}` is a closed
`Prop`-valued definition. It isolates exactly the first conclusion of
`Langlands.GLTemperedInductionStatement`, preserving every input quantifier
and hypothesis. It states a prerequisite for that induction theorem; it
supplies no proof of this prerequisite.

## Exact statement

For every prime `p` with `[Fact p.Prime]`, every finite p-adic extension
`F : PadicField.{uF} p`, every supplied `T : F.TopologicalData`, every
positive total rank `n`, and every `B : GeneralLinear.BlockShape n`, put

```text
M = B.Levi F.Carrier = ∏ i : Fin B.length, GL_(B.size i)(F),
Q = M / Subgroup.center M.
```

Use the topology induced by `T.topology`, exactly as in the parent
statement. Quantify over every `[MeasurableSpace Q] [BorelSpace Q]`,
every `μ : MeasureTheory.Measure Q` with `[μ.IsHaarMeasure]`, every
`V : Type uV` with `[AddCommGroup V] [Module ℂ V]`, and every actual action
`σ : Representation ℂ M V`. The implication is

```text
Representation.IsIrreducible σ →
IsTemperedModCenter σ μ →
IsUnitarizable σ.
```

The universes `uF` and `uV` are independent. The quotient is by the
**full center of the actual Levi**, which is the product of the factor
centers; it is not the image of the ambient general linear group's center.
All block sizes are positive, and positive total rank implies that there
is at least one block. The one-block case is included.

For each supplied measure, temperedness for that one measure suffices for
the asserted implication. There is no hypothesis of temperedness for all
Haar measures. The imported
`PadicField.TopologicalData.exists_isHaarMeasure_leviCentralQuotient`
already provides a Borel Haar realization, so the measure quantification
has actual instances.

`IsTemperedModCenter σ μ` includes admissibility and the existence of a
smooth unitary scalar central character. For that character, every
absolute smooth matrix coefficient, indexed by `ℓ : SmoothDual σ` and
`v : V`, lies in `L^(2+ε)(Q, μ)` for every real `ε > 0`. Admissibility
includes smoothness and finite-dimensional compact-open fixed spaces.
Consequently Silberger's separate admissibility hypothesis is retained.
Irreducibility is irreducibility of the actual algebraic action.

`IsUnitarizable σ` means `Nonempty (InvariantPositiveForm σ)`.
An `InvariantPositiveForm` extends `InnerProductSpace.Core ℂ V` and
satisfies `inner (σ g v) (σ g w) = inner v w`. It is a positive definite
Hermitian form on the given algebraic carrier, with conjugate linearity
in the first argument. No norm, topology, completion, finite dimension,
chosen form, tensor factorization, or finite-length assumption is imposed
on `V` or `σ`. A unitary central character alone is not this conclusion.

## Original source and specialization

A. J. Silberger, *Introduction to Harmonic Analysis on Reductive p-adic
Groups* (1979), Corollary 4.5.13, printed p.190, asserts unitarity of an
irreducible admissible tempered representation of a reductive group.
Its proof explicitly invokes Corollaries 1.7.9 and 4.5.11.

- Literature ID: `silberger-1979-harmonic-analysis`.
- SHA-256: `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
- Retained original:
  `/home/taskhub/central-library/Silberger--Introduction to harmonic analysis on reductive p-adic groups (book)--1979.pdf`.
- Reading extent: Corollary 4.5.13 and its proof on printed p.190,
  one-based PDF p.196, read directly and checked visually on 2026-10-25.
  The complete published
  [parent convention explanation](TemperedInductionStatement.md),
  including its analytic boundary, was also read.
- No source-specific errata note was present in project notes or in
  Library base `b5df466b356db508f072a2481307ed641ffa76a7` when checked.

Apply the source's reductive-group scope to the split reductive group
`M = ∏ i, GL_(B.size i)(F)` itself. This specializes to the actual
product action `σ`; it does not require decomposing `σ` into factor
representations. The source's unitary realization yields an invariant
positive Hermitian form on its smooth algebraic carrier; a formal proof
must construct that realization and transport the form to the supplied
carrier. No such construction is implemented here.

## Analytic boundary and remaining proof obligations

The parent explanation records Silberger's tempered weak coefficient
bound and the proposed comparison with the Library's `L^(2+ε)` predicate,
using the Waldspurger locators given there. These predicates are not
definitionally equal. This extraction does not establish any direction
of that analytic comparison.

A future proof must implement the needed comparison for the actual product
Levi, including smooth-dual coefficients, descent modulo its full center,
and the relationship between the supplied Borel Haar measure and the
measure used in the source estimates. Group-level product Cartan and
coefficient estimates do not provide a tensor decomposition of `σ`.
Any use of tensor factorization requires an actual theorem and the
corresponding representation, coefficient, and measure comparisons.

Silberger's proof dependencies, Corollaries 1.7.9 and 4.5.11, also remain
substantive formal obligations. Any approach through ambient
discrete-series support must provide the actual support construction,
induction and form comparison, and transport to this Levi representation;
an ambient `GL_n` statement alone does not prove the product-Levi target.
The source citation and these descriptions provide no Lean implementation
of those results.

This module imports the published parent and defines only the extracted
proposition. It does not change any imported Lean/Markdown pair, prove a
normalized-induction conclusion, or assume a form as an input. Downstream
tempered exhaustion, `TemperedUnitarityAndGenericity`, square-integrable
block induction, and regular Langlands classification cannot discharge
this upstream prerequisite by citation or assumption.
