# Tensor injectivity for ideals containing maximal-ideal powers

`Langlands.Algebra.FiniteColengthTensorInjectivityStatement.{u,v}` defines
a proposition. This module contains no proof of that proposition.

Let \(R\) be a commutative Noetherian local ring, with maximal ideal
\(\mathfrak m\), and let \(M\) be an arbitrary \(R\)-module. Suppose that
the map induced by the inclusion \(\mathfrak m\hookrightarrow R\),
\[
M\otimes_R\mathfrak m\longrightarrow M\otimes_R R,
\]
is injective. Then, for every ideal \(J\) and every natural number \(n\),
\[
\mathfrak m^n\subseteq J
\quad\Longrightarrow\quad
M\otimes_R J\longrightarrow M\otimes_R R
\text{ is injective}.
\]
The conclusion's map is also induced by the ideal inclusion.

The Lean proposition quantifies over `R : Type u` and `M : Type v`
with independent universes and the instances `CommRing R`,
`IsNoetherianRing R`, `IsLocalRing R`, `AddCommGroup M`, and `Module R M`.
It assumes neither finiteness, nontriviality, nor flatness of \(M\).
Both maps use `LinearMap.lTensor M`: their left tensor factor is \(M\),
and their codomain is \(M\otimes_R R\). The exponent ranges over all
natural numbers, including zero; when \(n=0\), the containment forces
\(J=R\).

This is an internal, derived tensor formulation of the finite-colength
step in the proof of Stacks Project Lemma 10.99.7, tag
[00MK](https://stacks.math.columbia.edu/tag/00MK). In a Noetherian local
ring, the quotient by an ideal containing a power of the maximal ideal
has finite length: the filtration by powers has finitely generated
residue-field vector spaces as its successive quotients. The source's
Lemma 10.99.6, tag [00MJ](https://stacks.math.columbia.edu/tag/00MJ),
propagates residue-field Tor vanishing to finite-length modules; applying
that step to \(R/J\) motivates the tensor-injectivity conclusion here.
Tensor commutativity and the unit isomorphism relate this left-tensor
form to the ideal-first maps into \(M\) used in the source.
This provenance explanation does not assert a formal comparison with
categorical Tor or a Tor comparison for arbitrary modules. The
declaration states only the displayed tensor implication.

The power-containment form supplies precisely the finite-colength cases
needed by the later 00MK argument, including \(J=\mathfrak m^n\) and
\(J=I+\mathfrak m^n\). The full local flatness criterion, its
separatedness argument, and its proof remain separate obligations.

The registered original is
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`:
`00MK.html`, Lemma 10.99.7, first paragraph of the proof; and
`00MD.html`, Lemma 10.99.6, statement and proof.
The official 00MK and 00MJ pages were also checked on 26 October 2026;
their mathematical content agrees with those originals and each has
zero comments. The retained current-page source is
`stacks-flatness-00mk-00mj-current-2026-10-26`, content SHA256
`867cdedaa7867ff53170db88408b2ad27481210df67727e5af2d3836ff0e5acb`,
files `00MK.html` and `00MJ.html`, statements, proofs and comment sections.
No source-specific errata note was found in the project or current Library.
