# Shalika invariance of Whittaker bi-equivariant distributions

Author: Worker 16.

`Langlands.Whittaker.ShalikaDistributionInvarianceStatement.{uF}` is an
unproved Prop-valued statement. For every prime `p`, every
`F : PadicField.{uF} p`, every natural number `n`, and every bundled unitary
additive character `psi` of `F.Carrier`, it asserts

```text
∀ D : HarmonicAnalysis.Distribution (GeneralLinear (n + 1) F.Carrier),
  IsBiEquivariantDistribution psi n D →
  IsWeylTransposeInvariant n F.Carrier D.
```

It installs `F.canonicalNormedField`, so all test functions, characters and
matrix-group homeomorphisms use the canonical p-adic topology. The field
universe `uF` is arbitrary. The rank is `n + 1`, including rank one at
`n = 0`. The character bundle already includes continuity, nontriviality
and unit-circle values. No Haar measure, representation, representation
unitarity, or genericity premise occurs.

## Exact imported predicates

The statement reuses `Whittaker.Distribution` without changing its objects
or hypotheses. Write `G = GL_(n+1)(F)`, `U` for the actual upper-unipotent
subgroup and `chi = standardCharacter psi n`. Then

\[
\chi(u)=\psi\left(\sum_{i=1}^{n}u_{i,i+1}\right).
\]

A distribution is an arbitrary complex linear functional on the actual
compactly supported, locally constant complex test functions
`SchwartzBruhat G`. There is no topology or continuity hypothesis on this
algebraic dual. The hypothesis states, for all `u1,u2` in `U` and all test
functions `f`,

\[
D\bigl(g\mapsto f(u_1 g u_2)\bigr)
   =\chi(u_1)\chi(u_2)D(f).
\]

Both character factors are positive. In the imported translation notation,
the test function is `leftTranslate u1.val⁻¹ (rightTranslate u2.val f)`;
`biTranslate_apply` proves its displayed value. The unipotent variables
are independently quantified and the condition is global on `G`.

Let `w` be the existing long-Weyl matrix with anti-diagonal entries one.
The conclusion is invariance under the actual homeomorphism
`weylTransposeHomeomorph n F.Carrier`, namely

\[
\tau(g)=w g^t w,\qquad \tau_*D=D.
\]

The imported pushforward evaluates as `D(f ∘ tau)`, and
`isWeylTransposeInvariant_iff` identifies the conclusion with
`D(f ∘ tau) = D(f)` for every test function. No inverse of `g`, complex
conjugation or measure factor is inserted. The imported entry formula is
`tau(g)[i,j] = g[j.rev,i.rev]`. In rank one tau is the identity, as proved
by `weylTransposeHomeomorph_rankOne`; the unipotent subgroup is trivial
and the superdiagonal sum is empty. The same implication is retained in
that case.

## Source and specialization

The source of the invariance assertion is J. A. Shalika, *The multiplicity
one theorem for GLn*, Annals of Mathematics (2) **100** (1974), 171–193,
registered as `shalika-1974-multiplicity-one`, SHA256
`788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
The original PDF is
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`.
Printed pp.173–175 (PDF pages 4–6) give the group and character conventions,
the anti-automorphism and Theorem 1.6. Worker 16 read these pages and
visually checked pp.174–175; no source-specific errata note was found.

On p.174 Shalika writes the character with nonzero coefficients on the
first superdiagonal. Taking every coefficient equal to one gives exactly
the standard character here. Nontriviality of the additive character
makes it nondegenerate. Reversing the adjacent entries preserves their
sum, so the auxiliary diagonal element `h0` can be one. Shalika's
anti-automorphism is then `g ↦ w*gᵀ*w`, with `w⁻¹ = w`, exactly the imported
homeomorphism. The elementary character-preservation identity is already
proved in `standardCharacter_weylTranspose`.

Theorem 1.6 on p.174 asserts invariance under this anti-automorphism for
nonarchimedean fields and distributions with the stated left/right
character transformation. Shalika defines the actions on distributions
by duality. The test-function version is explicit in Proposition 1.8 on
p.175: its hypothesis evaluates `T` on `L_(u1⁻¹) R_u2 f` and multiplies
`T(f)` by `chi(u1*u2)`. The homomorphism property identifies this with our
two positive factors. Proposition 1.8 is a cellwise step of the source
proof; the present global conclusion is Theorem 1.6. No invariance or
stability of each individual Bruhat cell is added to this statement.

The restriction from the source's nonarchimedean local fields to the
Library's finite extensions of the p-adic numbers is the same field
scope as the parent multiplicity-one target. The imported algebraic
convention for p-adic distributions is stated explicitly in Bernstein and
Zelevinsky, *Representations of the group GL(n,F), where F is a
non-Archimedean local field (survey)* (1976), Section 1.7, printed/PDF p.7:
test functions are locally constant with compact support and distributions
are their linear functionals, without topologies on either vector space.
This registered source is `bernstein-zelevinsky-1976-representations-gln`,
SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`;
that page was read directly. This second citation specifies the algebraic
distribution convention; the invariance assertion is Shalika's Theorem 1.6.

## Proof boundary

This module only defines the proposition. It proves neither distribution
invariance nor multiplicity one. The Bruhat geometry, character-compatible
loci, distribution restriction and descent, and finite-filtration argument
belong to the eventual proof; none is an additional premise of the
statement. Shalika's representation argument in Section 3 is not used to
supply a proof for the parent's unrestricted admissible representations.
The representation bridge from this distribution statement to the full
`MultiplicityOneStatement` remains a separate obligation.
