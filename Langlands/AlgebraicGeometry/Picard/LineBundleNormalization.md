# Normalizing a line bundle along a section

For a morphism of schemes \(f:X\to S\) and a section
\(\epsilon:S\to X\), this module constructs a rigidified line bundle from an
ordinary line bundle \(L\) on \(X\). Its inputs include a line bundle \(M\) on
\(S\) and an actual module isomorphism
\[
  \mathrm{ev}:\epsilon^*L\otimes M \simeq \mathcal O_S.
\]
Thus \(M\) is a specified tensor inverse of the restriction of \(L\).
The construction does not choose or assert the existence of such an inverse.
It also takes the published
`pullbackTensorComparisonIsIsoStatement` as an explicit proof input.

`LineBundle.normalize` has underlying bundle
\[
  L\otimes f^*M,
\]
and constructs its rigidification along \(\epsilon\). In particular, when
\(M=(\epsilon^*L)^{-1}\), this is the normalization
\(L\otimes f^*(\epsilon^*L)^{-1}\). This base factor is needed before using
an arbitrary line bundle in the rigidified Mumford-family construction.

The construction works for any morphism of schemes with a section. It
does not impose properness, flatness, quasi-separatedness, or a condition
on the direct image of the structure sheaf.

## Implemented construction

`sectionBasePullbackIso` combines the canonical pullback-composition
isomorphism, the section equality \(f\circ\epsilon=\mathrm{id}_S\), and the
pullback-identity isomorphism.
It identifies \(\epsilon^*f^*M\) with \(M\).

`normalizationTrivialization` first uses the canonical tensor comparison
to identify
\(\epsilon^*(L\otimes f^*M)\) with
\(\epsilon^*L\otimes\epsilon^*f^*M\), then applies
`sectionBasePullbackIso` to the second factor, and finally applies
\(\mathrm{ev}\). Its inverse is the rigidification
\(\mathcal O_S\simeq\epsilon^*(L\otimes f^*M)\).
Local rank one follows from the existing line-bundle pullback and tensor
constructions.

`normalize_forget` identifies the underlying bundle by reflexivity.
`normalize_rigidification_comp` verifies that the constructed
rigidification followed by the displayed restriction trivialization is
the identity; its proof is the inverse-hom identity of that isomorphism.

## Provenance and scope

This is a derived construction from the ordinary pullback and tensor
identities. Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary
draft, §6.2, printed pp.88–89 (PDF pp.92–93), defines rigidification and
uses precisely \(L\otimes f^*\epsilon^*L^{-1}\) with its canonical
rigidification in item (ii) on p.89. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

The source assumes additional hypotheses for the asserted comparison
of the relative Picard functor with rigidified classes. This module
constructs only the normalized rigidified bundle by the explicit
isomorphisms above. It makes no claim about that comparison, descent,
quotients by base-pulled bundles, inverse existence, or the independence
of choices. These wider assertions are not used to extend the
construction to arbitrary \(f\) with a section.
