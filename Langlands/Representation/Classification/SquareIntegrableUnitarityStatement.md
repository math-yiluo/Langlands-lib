# Unitarizability from square-integrable matrix coefficients

Author: Worker 86, with source and convention guidance from Worker 69.

`Langlands.GLSquareIntegrableUnitarityStatement.{uF,uV}` is a closed
proposition definition. It states that an irreducible analytically
square-integrable representation of a positive-rank p-adic general linear
group is unitarizable. This file supplies a statement, not a proof or an
assumption of its truth.

## Exact scope

The proposition quantifies over every prime `p`, its `Fact p.Prime` instance,
every finite p-adic extension `F : PadicField.{uF} p`, every compatible
`T : F.TopologicalData`, every natural rank `n` with `0 < n`, and every
complex module `V : Type uV`. The field and carrier universes are independent.
For the actual action
`ρ : Representation ℂ (GeneralLinear n F.Carrier) V`, its only hypotheses
are `Representation.IsIrreducible ρ` and `T.IsSquareIntegrable ρ`.
Its conclusion is `Langlands.IsUnitarizable ρ` on that same carrier.

The imported analytic predicate is used unchanged. For every Borel Haar
measure on the actual quotient
`GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)`,
it requires admissibility, an actual scalar unitary central character,
and `MemLp (c.coefficientNorm ℓ v) 2 μ` for every smooth-dual functional
`ℓ : SmoothDual ρ` and every `v : V`. The coefficient norm at `gZ` is
`‖ℓ (ρ g v)‖`. Existence of a Haar measure is already proved by
`T.exists_isHaarMeasure_centralQuotient`; the universal condition is not
vacuous. Admissibility follows by `IsSquareIntegrable.isAdmissible`, and
smoothness is part of that admissibility predicate.

`IsUnitarizable ρ` is `Nonempty (InvariantPositiveForm ρ)`. This form extends
`InnerProductSpace.Core ℂ V` and is invariant under every action operator.
Thus the conclusion requires a positive definite Hermitian form, not only
the unitary central character already contained in the hypothesis.
No finite dimension, norm, topology, completeness, prescribed functional,
prescribed form, or unitarity hypothesis is imposed on `V`.

## Original source and convention

W. Casselman, *Introduction to the theory of admissible representations of
p-adic reductive groups*, draft of 1 May 1995, §2.5, printed/PDF pp.28–29,
defines square-integrability through absolute smooth-dual matrix
coefficients and states the unitarity implication in Proposition 2.5.4.
This proposition is specialized here to positive-rank `GL_n(F)`. Its
separate admissibility hypothesis is contained in the Library's
square-integrability predicate.

- Literature ID: `casselman-1995-admissible-representations`.
- SHA-256: `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
- Retained original:
  `/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
- Reading extent: pp.28–29 read directly; the formula on p.29 was also
  checked visually. No source-specific project errata note was present
  when this pair was prepared.

For a chosen nonzero smooth functional `ℓ`, write `c_v(g) = ℓ(ρ(g)v)`.
Casselman's displayed form integrates `c_u(g) * conjugate(c_v(g))`.
The conjugation on the second factor is visible in the page image but is
lost in plain text extraction. Mathlib's `InnerProductSpace.Core` instead
uses conjugate linearity in the first argument. Accordingly the proposed
construction for the Library convention is

```text
B(u,v) = ∫[G/Z] conjugate(c_u(g)) * c_v(g) dμ(gZ).
```

This is the conjugate of Casselman's form, equivalently its value with
arguments reversed. It has the same diagonal, positivity, definiteness,
and invariance. The integrand denotes a descended product; it does not
presuppose that the complex coefficients individually descend.

## Substantive obligations for the future proof

The following describes the source argument and its required formal
steps. None of these steps is implemented by this proposition definition.

1. **A nonzero smooth functional.** Derive a nonzero vector from
   irreducibility and construct a nonzero member of `SmoothDual ρ`.
   One route uses a compact open subgroup fixing a nonzero vector, a
   linear functional on its fixed space, and compact averaging to extend
   it to a smooth functional. Existence of an algebraic dual functional
   alone does not establish membership in the smooth dual.
2. **Haar measure and quotient descent.** Choose a Borel Haar measure
   using the existing existence theorem and extract the central-character
   datum from square-integrability for that measure. For `z ∈ Z`,
   `c_v(gz) = ω(z)c_v(g)`, so the two character factors in the product
   cancel because `conjugate(ω(z))*ω(z) = 1`. Construct the product as a
   complex function on the actual quotient and establish its measurability.
   Smooth coefficients are locally constant; this and the quotient
   topology give a route to the needed measurability.
3. **Integrability and the Hermitian laws.** The norm of the descended
   product is the product of the two descended coefficient norms.
   Their `L²` hypotheses give `L¹` integrability by Cauchy–Schwarz.
   Use actual integrability when interchanging sums, complex scalars,
   and conjugation with the integral. This constructs the conjugate-linear
   first variable, linear second variable, and Hermitian symmetry required
   by `InnerProductSpace.Core`.
4. **Invariance under the given action.** The identity
   `c_(ρ(h)v)(g) = c_v(gh)` requires invariance of the quotient integral
   under right translation. The central quotient of p-adic `GL_n` is
   unimodular, so a left Haar measure there is also right invariant.
   Establish and apply that fact for this actual quotient, or prove its
   required right-translation invariance directly. A general locally
   compact group need not be unimodular; right invariance is a proof
   obligation, not an additional hypothesis of the statement.
5. **Positivity and definiteness.** The diagonal integrand is
   `‖c_v(g)‖²`, giving nonnegativity. A zero diagonal integral implies
   its vanishing almost everywhere. Local constancy and positive Haar
   measure of every nonempty open set upgrade this to vanishing
   everywhere on the quotient. The vectors whose coefficient function
   vanishes everywhere form an invariant linear subspace. It is proper,
   since `ℓ ≠ 0` and `c_v(1) = ℓ(v)`. Irreducibility makes this subspace
   zero, proving definiteness. These arguments require actual
   smoothness and Haar properties, rather than a formal declaration
   that the integral is positive definite.
6. **Assemble the form.** Package the resulting inner product and action
   invariance as `InvariantPositiveForm ρ`, then take its nonemptiness.
   The construction introduces no pre-existing norm or topology on `V`.

The predicate uses all Haar measures, while the source fixes one. For this
implication the existing Haar existence theorem allows choosing one and
using the universal hypothesis. No equivalence between the all-measures
and one-measure definitions is needed to state or prove this direction.

## Dependencies and boundary

The direct project imports are
`Langlands.Representation.Classification.Tempered` and
`Langlands.Representation.Unitary.Basic`; Mathlib's
`RepresentationTheory.Irreducible` supplies irreducibility.
The analytic definition ultimately uses
`Langlands.Representation.MatrixCoefficient.ModuloCenter`.
All existing Lean/Markdown pairs are left unchanged.

The proposed proof is independent of tempered exhaustion, tempered
unitarity, segment classification, and equal-exponent grouping. In
particular, the statements in `TemperedBlockStatement` and
`SegmentSquareIntegrabilityStatement` supply no proof of this implication.
The result is an upstream form-existence obligation needed by those
classification arguments. It does not assert any converse from
unitarizability to square-integrability.
