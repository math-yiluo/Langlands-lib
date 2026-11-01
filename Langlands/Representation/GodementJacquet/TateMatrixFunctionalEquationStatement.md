# Tate matrix functional-equation base in rank one

`Langlands.GodementJacquet.TateMatrixFunctionalEquationStatement.{uF,uV}`
defines the full normalized matrix functional-equation existence proposition
for every admissible irreducible complex representation of `GL₁` over a
canonical p-adic field. It is a proposition definition and supplies no proof.

The quantifiers retain every prime `p`, every `F : PadicField.{uF} p`, the
canonical topology, valuation and local-field structures, and the field and
`GL₁` Borel structures. The representation carrier `V : Type uV` has an
independent universe and carries only an additive commutative group and complex
module structure. The actual representation `σ` has premises `IsAdmissible σ`
and `Representation.IsIrreducible σ`. Admissibility includes smoothness;
irreducibility excludes the zero carrier. No topology on `V`, selected
quasicharacter, Whittaker certificate, central character or equivalence with a
one-dimensional model is an input.

For every bundled nontrivial continuous unitary additive character `ψ`, every
supplied scalar additive Haar measure `ν`, and the premise `IsSelfDual ψ ν`,
the conclusion constructs polynomials `P, PDual : Polynomial ℂ`, a complex unit
`c` and an integer `a` satisfying exactly

```text
Padic.NormalizedMatrixFunctionalEquationData (n := 0) F ψ ν σ P PDual c a.
```

This is the existing data predicate on the specified actual representation.
It retains a common right half-plane of absolute convergence for every test
and bi-smooth coefficient on each side, rational continuation for every such
pair, and both normalized Laurent-span generator equalities with
`P.coeff 0 = PDual.coeff 0 = 1`. The group measure is the canonical
`RankinSelberg.generalLinearHaar F.Carrier 0`, the absolute value is canonical,
and the spectral variable is `q^(-s)` for the canonical residue cardinality.
Since the matrix rank is one, the normalized shift is zero.

For every full `1 × 1` matrix Schwartz–Bruhat test, the Fourier witness precedes
all coefficients and all continuation pairs. It uses the plus transpose
pairing, integrability at every matrix, and exactly the one-entry product of
the supplied scalar measure `ν`. The coefficient transformation is
`f(g) ↦ f(transpose(g⁻¹))`, which in rank one is inversion. With the central
scalar fixed to `1` and sign exponent fixed to `0`, the guarded equation is

```text
PDual(q^(-(1-s))) RDual(q^(-(1-s)))
  = c (q^(-s))^a P(q^(-s)) R(q^(-s)).
```

It ranges over every actual continuation pair where both continuation
denominators evaluate nonzero. Neither those existence clauses nor the guards
are omitted.

Roger Godement and Hervé Jacquet, *Zeta Functions of Simple Algebras* (1972),
Theorem 3.3 and its normalization discussion, printed pages 30–34 (one-based
PDF pages 40–44), is registered as
`godement-jacquet-1972-zeta-simple-algebras`, SHA256
`86a8900900504adeb5757a04b5bb8a8754e6ef00b0fff49754096d371f59d568`.
The retained original is
`/home/taskhub/central-library/Godement-Jacquet--Zeta functions of simple algebras (book)--1972.pdf`.
The theorem gives the admissible irreducible analytic assertion. Printed page
31 explicitly identifies `M = F` as the known Tate case. Specializing the
matrix rank to one gives this prerequisite. The statement keeps the theorem's
actual representation scope; a future proof must establish any character-model
reduction it uses.

H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic Forms on
GL(3) I* (1979), printed page 177 (one-based PDF page 10), equations
(1.1.1)–(1.1.2) and the following Fourier formula, is registered as
`jps-1979-gl3-i`, SHA256
`6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`.
It supplies the plus transpose convention used by the data predicate. In rank
one the transpose has no effect. The cited passages were read in the retained
originals. No source-specific errata note was found in the project literature
or published notes.

This unit supplies the analytic base target, without assuming a preexisting
abelian local-analysis theorem or the generic matrix functional equation. It
does not prove either one or assert the reducible analogue.
