# Splitting off a representation with compact matrix coefficients

`Langlands.CompactCoefficientSplittingStatement` states a representation-theoretic
input to the Ext-vanishing argument used by Harris. It is a proposition
definition; its truth has not been proved in Lean.

Let \(G\) be a Hausdorff, locally compact, totally disconnected topological group
that is a countable union of compact sets. Its measurable structure is the Borel
structure. Let \(\mu\) be a regular left Haar measure that is also right
invariant. Thus the source's unimodularity hypothesis is explicit, and no
probability normalization or chosen volume of a compact open subgroup is needed.

Let \(\rho\) be an irreducible smooth complex representation on a vector space
\(V\), of arbitrary dimension. Suppose every matrix coefficient
\[
  g\longmapsto \ell(\rho(g)v)
\]
has compact support when \(v\in V\) and the algebraic functional \(\ell\) is a
smooth vector of the contragredient action
\((g\ell)(v)=\ell(\rho(g^{-1})v)\).
For every smooth complex representation \(\sigma\) on an arbitrary vector
space \(W\), the proposition asserts both:

1. Every injective intertwiner \(i:\rho\to\sigma\) has an intertwining retraction
   \(r:\sigma\to\rho\), with \(r\circ i=1_\rho\).
2. Every surjective intertwiner \(p:\sigma\to\rho\) has an intertwining section
   \(s:\rho\to\sigma\), with \(p\circ s=1_\rho\).

The group and the two vector spaces have independent universe parameters.
Neither vector space carries a topology, and \(W\) need not be admissible,
irreducible or finite dimensional. Irreducibility includes nontriviality.
The support hypothesis is imposed only on smooth algebraic functionals, not on
every functional in the algebraic dual.

## Original source and derived formulation

I. N. Bernstein and A. V. Zelevinsky, *Representations of the group GL(n,F)
where F is a non-archimedean local field*, Russian Mathematical Surveys
31:3 (1976), 1–68, English translation.

- Literature ID: `bernstein-zelevinsky-1976-representations-gln`.
- Retained PDF SHA-256:
  `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
- Locators: Section 1.1, p.6 (the locally profinite group convention);
  Section 1.5, p.7 (countability at infinity);
  Section 2.13, p.19 (algebraic dual and its smooth part);
  Sections 2.39–2.41, p.26 (matrix coefficients and “finite” representations);
  Section 2.42, pp.27–28 (unimodular, countable-at-infinity hypotheses);
  Section 2.43 and Theorem 2.44(a), p.28 (natural isotypic projection and
  splitting of every irreducible finite subfactor).
- Retained original:
  `C:/Central-Library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.

The source's word “finite” means compact matrix coefficients, not finite
dimension. Its coefficient uses \(g^{-1}\) where the project's bilinear
coefficient uses \(g\). Inversion is a homeomorphism, so these two coefficient
functions have compact support simultaneously. Smoothness makes these
coefficients locally constant; their nonzero locus is closed, so topological
compact support agrees with the source's support convention.
The source's locally profinite condition is expressed by the usual equivalent
Hausdorff, locally compact, totally disconnected group conditions.

This target is a derived consequence of Theorem 2.44(a), not a verbatim
translation of its isotypic-decomposition statement. That theorem gives
\(W=W_\rho\oplus W_\rho^\perp\), where \(W_\rho\) is a direct sum of copies
of \(V\), and \(W_\rho^\perp\) has no subquotient isomorphic to \(V\).
The image of an embedding of \(V\) lies in the first summand. A surjection to
\(V\) vanishes on the second summand and is nonzero on some simple summand
of the first. Semisimplicity of the first summand therefore gives the stated
retraction or section. This explains the literature implication; no Lean
proof of that implication or of Theorem 2.44 is supplied.

For the application, Harris, *Supercuspidal representations in the cohomology
of Drinfel'd upper half spaces; elaboration of Carayol's program*, Inventiones
Mathematicae 129 (1997), p.96 following Lemma 6, first passes to the component
stabilizer with compact center. He then uses compact matrix coefficients and
projectivity/injectivity there. The present proposition does not identify
supercuspidality with this support condition for an arbitrary group, does not
assert splitting for compact support only modulo a noncompact center, and does
not yet construct the smooth category or prove higher Ext vanishing.

The Harris original is registered as `harris-1997-drinfeld-cohomology`,
PDF SHA-256
`aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.
Its role here is the application and the restriction just described; the
splitting theorem's mathematical source is Bernstein–Zelevinsky.

## Exact formal dependencies and remaining obligations

The source-backed statement uses these accepted and published definitions,
verified current at Library commit `9007729971e6e6ecea63b5567b6d1621769ccfb0`:

| Artifact, version | Imported module | Published Lean SHA-256 |
| --- | --- | --- |
| `665022df-625b-44ae-9dbd-425f6e266bab`, v1 | `Langlands.Representation.Smooth.Definitions` | `435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb` |
| `5352a743-a6a8-4824-b91e-1cbc32b79b30`, v1 | `Langlands.Representation.MatrixCoefficient.Definitions` | `92c0bf57151ef798f1198793a4d685afd175274240c1956b54ce3d10e855b7ae` |

The environment is artifact `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, v1:
Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Mathlib supplies actual algebraic representations, their dual actions,
irreducibility through the subrepresentation lattice, linear intertwiners,
composition and identity, compact support and measure invariance.
No project theorem proof is imported to state the conclusion.

Proof of this proposition, its categorical projective/injective consequences,
transport to the characteristic-zero coefficient field used by Harris,
the compact-center application, and the Ext-vanishing and spectral-sequence
arguments remain separate obligations. This one statement does not complete
the Harris–Berkovich framework task.

Authored by Worker 3.
