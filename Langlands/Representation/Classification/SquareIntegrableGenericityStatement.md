# Whittaker genericity of a square-integrable representation

Author: Worker 386.

`Langlands.Classification.SquareIntegrableGenericity.{uF,uV} F T` states
the intrinsic single-representation genericity theorem as a `Prop`-valued
definition. This module proves no genericity theorem.

## Statement and conventions

The outer parameters are `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p` and `T : F.TopologicalData`. Thus the declaration
is available for every prime, actual finite p-adic extension and compatible
topological realization. It installs `T.topology` before quantifying over
smooth representations and additive characters.

For every `n : ℕ` and
`π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier)`,
the three hypotheses are, separately:

1. `Representation.IsIrreducible π.representation`;
2. `T.IsSquareIntegrable π.representation`;
3. `IsUnitarizable π.representation`.

The conclusion is `Whittaker.IsGeneric ψ n π.representation` for **every**
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier`.
Field and carrier universes `uF` and `uV` are independent; the actual
representation carrier belongs to `Type (max uF uV)`. There is no
finite-dimensional carrier assumption or carrier topology.

The analytic predicate is the published square-integrability condition on
the actual central quotient `G / Z(G)`, with its Borel measurable structure.
For every Borel Haar measure `μ` it requires admissibility and a smooth
unitary scalar central character `c`, with
`MemLp (c.coefficientNorm ℓ v) 2 μ` for every smooth-dual functional `ℓ`
and vector `v`. The descended function is
`g Z(G) ↦ ‖ℓ(π(g)v)‖`. The Library proves existence of such Haar measures,
so the universal measure quantifier is not vacuous. This is an analytic
condition, with no segment or classification-image substitute.

`IsUnitarizable` is existence of an `InvariantPositiveForm`: a positive
definite Hermitian form on the actual complex carrier, invariant under
every action operator. A unitary central character alone is not this witness.
No Hilbert completion is supplied by this hypothesis.

`UnitaryAdditiveCharacter` bundles an additive character valued in the unit
circle, continuity for the installed field topology, and nontriviality.
`Whittaker.IsGeneric` requires irreducibility, admissibility and an actual
nonzero complex-linear functional `λ` with

    λ(π(u)v) = ψ.complex(∑ i : Fin n, u[i,i+1]) * λ(v)

for the actual standard upper-unipotent subgroup of `GL_(n+1)(F)`.
This is the published `Whittaker.standardCharacter ψ n`, with the positive
sign and no inverse character. No continuity of `λ` on a representation
carrier is imposed. The already proved
`PadicField.TopologicalData.IsSquareIntegrable.isAdmissible` supplies the
admissibility part from the hypotheses; the substantive missing conclusion
is existence of the nonzero functional.

The case `n = 0` includes `GL₁`. Its upper-unipotent subgroup is trivial
and the superdiagonal sum is empty. The published
`Whittaker.standardCharacter_rankOne` and `Whittaker.glFunctionals_rankOne`
verify the corresponding trivial character and unrestricted functional
space. A proof still needs a nonzero functional on the nonzero irreducible
carrier; equality of the functional space with the top submodule alone
does not establish that existence.

## Original-source correspondence

**JS83**, §1.2, printed pp.108–109, is the direct source. Equation (1.2.2)
on p.108 defines the upper-unipotent character as the product of
`ψ(u[i,i+1])`, equal by additivity to the Library's character of the sum.
Equation (1.2.3) is precisely the equivariance equation above. In the first
paragraph of p.109, before discussing induction, Jacquet and Shalika take
an irreducible preunitary square-integrable representation, pass to its
unitary realization, and use its mirabolic restriction to obtain a
nonzero linear form satisfying (1.2.3). Their subsequent use of uniqueness
is stronger than the existence conclusion stated here.

**Ku94**, §2.3, printed p.374, equation (2.3.1), gives the same functional
definition and states independence of the nontrivial additive character
by Borel conjugation. Immediately after Theorem 2.3.1, the single-segment
example states that essentially square-integrable representations are
generic. This corroborates the single-representation statement and its
character scope. Its broader tempered-genericity assertion is not used as
an input or as a proof of this prerequisite.

JS83 introduces its higher-rank discussion with rank greater than two;
the elementary rank-one extension here uses the actual trivial unipotent
group as explained above. Ku94's general positive-rank formulation agrees
with this scope. No multiplicity-one theorem, canonical functional,
induced representation or induction heredity is asserted by this module.

## Remaining proof and comparison obligations

The source argument is a route for a future proof, not an implemented
Lean proof. In particular it requires the following comparisons.

1. Starting with the invariant positive form, construct the Hilbert
   completion and its strongly continuous unitary action. Identify the
   original admissible smooth representation with the smooth vectors
   of that completion and compare algebraic irreducibility with
   irreducibility of the unitary realization. These identifications are
   not fields of `InvariantPositiveForm`.
2. Relate the Library's smooth-dual coefficients and their descended
   absolute values to the Hilbert matrix coefficients used in the
   square-integrable unitary theory. This includes the central-character
   realization on `G / Z(G)` and the appropriate regular-representation
   embedding. Ordinary `L²(G)` cannot silently replace square-integrability
   modulo the center. Relate the universal Borel Haar quantifier to a
   source's fixed Haar measure using uniqueness up to positive scaling
   and preservation of `L²` membership under that scaling.
3. Formalize the required mirabolic representation, the restriction
   result for the unitary realization and the passage from it to a
   nonzero **algebraic** Whittaker functional on the original smooth
   vectors. JS83 states this passage; citing it does not implement it.
   Uniqueness is not part of the present conclusion.
4. Supply the argument for every allowed additive character. If a proof
   first chooses one character, it must construct the relevant change
   of character and conjugation transport; Ku94's stated independence
   does not itself constitute a Lean theorem. Handle rank one by
   nontriviality and linear duality.

An alternative segment route would require proofs of the actual analytic
square-integrable classification, genericity for the corresponding special
constituents and transport along genuine representation equivalences.
Published segment statement definitions do not supply those proofs.
The source limitations in
`notes/henniart/gln-classification-sources.md` and
`Classification/TemperedBlockStatement.md` remain in force.

## Dependencies and retained originals

The direct imports are `Representation.Category.Basic`,
`Representation.Classification.Tempered`, `Representation.Unitary.Basic`
and `Representation.Whittaker.GeneralLinear`, all under `Langlands`.
They supply the actual smooth category, analytic predicate, invariant
forms, characters and functionals. Neither `TemperedBlockStatement` nor
the segment-classification statements are imported. No existing pair is
modified. This single-block target precedes Worker 90's separate
square-integrable-block genericity proof; it does not take that target,
parent tempered genericity, or another theorem-valued assumption as input.
The formulation was developed against Library commit
`da90f21ba20b6d762325ec051bd63406a7c3a3cf`.

The following registered originals were read directly. PDF page numbers
are one-based; fingerprints identify the retained editions.

- **JS83:** H. Jacquet and J. A. Shalika, *The Whittaker models of induced
  representations*, Pacific J. Math. 109 (1983), no.1, pp.107–120.
  ID `jacquet-shalika-1983-whittaker`;
  SHA256 `e171831da6c064fdcb55efe79381ba1f85daa4efd7f3a79071589ffee9527f98`.
  Retained file:
  `/home/taskhub/central-library/Jacquet-Shalika--The Whittaker models of induced representations--1983.pdf`.
  Read PDF pp.2–4 (printed pp.107–109), with visual checks of pp.108–109.
- **Ku94:** S. S. Kudla, *The local Langlands correspondence: the
  non-archimedean case*, Motives, Part 2, Proc. Sympos. Pure Math. 55
  (1994), pp.365–391.
  ID `kudla-1994-local-langlands-nonarchimedean`;
  SHA256 `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`.
  Retained file:
  `/home/taskhub/central-library/Jannsen-Kleiman-Serre--Motives Part II (proceedings)--1994/Jannsen-Kleiman-Serre--Motives Part II (proceedings)--1994.pdf`.
  Read and visually checked §2.3, printed p.374 (PDF p.384).

Both file hashes were rechecked. No source-specific errata note was present
in the supplied Library snapshot.
