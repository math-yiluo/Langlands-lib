# Semisimplicity of smooth representations with compact coefficients

`Langlands.CompactCoefficientSemisimplicityStatement` states the last sentence
of Bernstein–Zelevinsky (1976), Theorem 2.44(b): every finite module is
completely reducible. It is a proposition definition; its truth has not been
proved in Lean.

## The proposition

Let \(G\) be a Hausdorff, locally compact, totally disconnected topological group
that is a countable union of compact sets. Its measurable structure is the Borel
structure. Let \(\mu\) be a regular left Haar measure that is also right
invariant. These are the binders of the published
`Langlands.CompactCoefficientSplittingStatement`, in the same order and form:

```lean
(G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
[T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
[SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
(μ : Measure G) [Measure.IsHaarMeasure μ] [Measure.Regular μ]
[Measure.IsMulRightInvariant μ]
```

The proposition is

```lean
∀ A : SmoothRep.{0, uG, uV} ℂ G,
  HasCompactSmoothDualCoefficients A.representation →
  Representation.IsSemisimpleRepresentation A.representation
```

In words: let \(A\) be an actual smooth complex representation of \(G\), on a
vector space of arbitrary dimension. Suppose that every matrix coefficient
\[
  g\longmapsto \ell(A(g)v)
\]
has compact support when \(v\in A\) and the algebraic functional \(\ell\) is
fixed by some open subgroup under the contragredient action
\((g\ell)(v)=\ell(A(g^{-1})v)\). Then every subrepresentation of \(A\) has a
complementary subrepresentation.

The declaration has the two universe parameters
`CompactCoefficientSemisimplicityStatement.{uG, uV}`. The group lives in
`Type uG` and the carrier of \(A\) in `Type uV`; the two are independent, and a
consumer fixes the carrier universe explicitly, for instance
`CompactCoefficientSemisimplicityStatement.{uG, max uG uV} G μ`.
The proposition quantifies over all such \(A\), so it includes infinite direct
sums and other representations of infinite length.
It imposes no irreducibility, admissibility, finite dimension, finite length,
unitarity or prescribed central character. The carrier has no topology.

`SmoothRep.{0, uG, uV} ℂ G` is the published full subcategory of Mathlib's
`Rep` whose objects have the open-stabilizer property `IsSmooth`.
`A.representation` is its actual algebraic action.
`Langlands.HasCompactSmoothDualCoefficients` is the published coefficient
predicate of `Langlands.Representation.CompactCoefficient.Classes`; it uses
the full algebraic dual `Module.Dual ℂ A`, the smoothness of the functional for
`ρ.dual`, the project's `matrixCoefficient` and Mathlib's `HasCompactSupport`.
`Representation.IsSemisimpleRepresentation ρ` is Mathlib's abbreviation for
`ComplementedLattice (Subrepresentation ρ)`, where `Subrepresentation ρ` is the
lattice of \(G\)-invariant subspaces. It is not semisimplicity of the carrier as
a complex vector space, which would hold for every representation.

## Original source and conventions

I. N. Bernstein and A. V. Zelevinsky, *Representations of the group GL(n,F)
where F is a non-archimedean local field*, Russian Mathematical Surveys
31:3 (1976), 1–68, English translation.

- Literature ID: `bernstein-zelevinsky-1976-representations-gln`.
- Retained PDF SHA-256:
  `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
- Retained original:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
- Locators (printed page numbers): Section 1.1, p.6 (l-spaces and l-groups);
  Section 1.5, pp.6–7 (countable at infinity); Section 2.1, p.15 (algebraic
  representations and the category Alg G); Sections 2.5–2.7, p.16
  (Hecke-algebra modules, subfactors and completely reducible modules);
  Section 2.13, p.19 (the contragredient); Sections 2.39–2.40, p.26
  (matrix elements and finite representations); Theorem 2.42, pp.26–28
  (unimodular l-group countable at infinity); Section 2.43 and
  Theorem 2.44(b), p.28.

**Group hypotheses.** Theorem 2.42 assumes a unimodular l-group that is
countable at infinity. Sections 2.43 and 2.44 build on that theorem, so
Theorem 2.44 inherits these hypotheses. An l-group has a neighbourhood basis of
the identity consisting of open compact subgroups; Section 1.1 notes that this
is equivalent to the underlying space being Hausdorff, locally compact and
zero-dimensional. For locally compact Hausdorff spaces, zero-dimensionality is
equivalent to total disconnectedness, which gives the stated typeclasses.
Countable at infinity, defined in Section 1.5, is `SigmaCompactSpace`.
Unimodularity is expressed by a regular left Haar measure on the Borel
structure that is also right invariant. The measure is a hypothesis only: the
conclusion does not mention it, and no normalization is chosen.

**Smoothness.** The source's algebraic representations (Section 2.1(a)) have
open stabilizers. A stabilizer is a subgroup, so it is open exactly when it
contains an open subgroup. This is `IsSmooth`, which asks that each vector be
fixed by some open subgroup. Every module in Theorem 2.44 is an object of
Alg G, which is why \(A\) ranges over `SmoothRep`.

**Finite means compact coefficients.** In Section 2.40 the source calls a
representation finite when every matrix element
\(g\mapsto\langle\tilde\xi,\pi(g^{-1})\xi\rangle\) is a finite function, that
is, has compact support, for every vector \(\xi\) and every vector
\(\tilde\xi\) of the smooth contragredient (Section 2.13). The word does not mean
finite dimension or finite length. The published predicate
`HasCompactSmoothDualCoefficients` is this condition: the smooth contragredient
consists of the algebraic functionals that are smooth vectors of `ρ.dual`.
The source's coefficient uses \(g^{-1}\) where the project's coefficient uses
\(g\). Inversion is a homeomorphism, so the two functions have compact support
simultaneously. On a smooth representation coefficients are locally constant,
so their nonzero locus is closed and the source's support agrees with
Mathlib's topological support.

**Completely reducible means complemented subrepresentations.** The source
defines complete reducibility in Lemma-Definition 2.7 for a module \(E\) over a
complex algebra by three equivalent conditions: (a) \(E\) is a direct sum of
irreducible submodules; (b) \(E\) is generated by its irreducible submodules;
(c) every submodule has an invariant complement. A complex representation of
\(G\) is the same as a module over the group algebra \(\mathbb C[G]\), and its
submodules are its \(G\)-invariant subspaces. Mathlib's order isomorphism
`Subrepresentation.subrepresentationSubmoduleOrderIso` identifies the two
lattices, and Mathlib's
`Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`
gives
\[
  \texttt{IsSemisimpleRepresentation }\rho \iff
  \texttt{IsSemisimpleModule }\mathbb C[G]\ \rho\texttt{.asModule}.
\]
`IsSemisimpleModule` is defined by complemented submodule lattices, which is
condition (c). Mathlib also proves its equivalence with (b)
(`sSup_simples_eq_top_iff_isSemisimpleModule`) and with (a)
(`isSemisimpleModule_iff_exists_linearEquiv_dfinsupp`).
For a smooth representation, Section 2.5 makes \(E\) a module over the Hecke
algebra of locally constant compactly supported distributions. Its Hecke
submodules are exactly its \(G\)-invariant subspaces. Indeed, if an open
compact subgroup \(N\) fixes \(\xi\), then \(\pi(g)\xi\) is the action of the
Hecke element \(\varepsilon_g*\varepsilon_N\) on \(\xi\); conversely, a Hecke
element acts on \(\xi\) as a finite linear combination of translates of
\(\xi\). Complete reducibility therefore does not depend on which of these two
algebras is used.

**What the source proves.** Theorem 2.44(a) splits off each finite irreducible
\(\omega\): \(E=E_\omega\oplus E_\omega^\perp\), with \(E_\omega\) the image of
the natural projector \(\pi(\varepsilon_\omega)\) of Section 2.43.
Theorem 2.44(b) says the submodule \(E^f\) generated by all \(E_\omega\) is
completely reducible and finite, and that \(E/E^f\) has no nonzero finite
subfactor module. The source derives the final sentence from this without
further comment. If \(E\) is finite, then so is its quotient \(E/E^f\), by the
remark after Lemma-Definition 2.40 that subfactors of finite representations
are finite. Lemma 2.6(b) gives every nonzero module an irreducible subfactor,
which would then be a nonzero finite subfactor of \(E/E^f\). Hence
\(E=E^f\). This explains the literature implication only; no Lean proof of
it, of Theorem 2.42, or of the projectors of Section 2.43 is supplied or
asserted.

## Relation to other Library statements

`Langlands.CompactCoefficientSplittingStatement` is the derived consequence of
Theorem 2.44(a) for a single irreducible representation. The present
proposition is the separate conclusion of Theorem 2.44(b) for an arbitrary
compact-coefficient representation. Both are unproved, and the splitting
statement is unchanged. The present target does not construct isotypic parts,
annihilators or the projectors \(\pi(\varepsilon_\omega)\). It says nothing
about representations whose coefficients are compact only modulo a centre.
It also does not state the transfer of complete reducibility along a
normal subgroup of finite index, which is Lemma 2.9(a).

## Exact formal dependencies

The statement imports the published
`Langlands.Representation.CompactCoefficient.Classes`, verified at Library
commit `a888136028bc342c82fc64fa7f4834e9ee965f2f`, with Lean SHA-256
`f7a98e323a2a751b93ec052e64907c7e4674bc8f960abba1c89badf05023020b`.
It supplies `HasCompactSmoothDualCoefficients` and, through its imports,
`SmoothRep` and `IsSmooth`. Mathlib's
`Mathlib.MeasureTheory.Group.Measure` supplies the Haar measure classes and
`Mathlib.RepresentationTheory.Semisimple` supplies
`IsSemisimpleRepresentation`. No project theorem is needed to state the
proposition. The environment is artifact
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

Authored by Worker 252.
