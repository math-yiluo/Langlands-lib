# Factorial prime localizations of smooth algebras over DVRs

`Langlands.CommutativeAlgebra.SmoothDVRFactorialLocalizationsStatement.{u}`
is a proposition definition. It says that for every discrete valuation domain
`R : Type u`, every smooth commutative `R`-algebra `A : Type u`, and every prime
ideal `P` of `A`, the actual ring `Localization.AtPrime P` has
`UniqueFactorizationMonoid`. This module supplies no proof or new axiom.

## Exact conventions and scope

The base ring has the given `CommRing R`, `IsDomain R`, and
`IsDiscreteValuationRing R` instances. Mathlib's DVR class is a local principal
ideal domain with nonzero maximal ideal, so fields are excluded. There is no
completeness, henselianity, excellence, characteristic, or residue-field
assumption. In particular mixed characteristic and arbitrary residue fields are
included.

The algebra has its specified `CommRing A` and `Algebra R A` instances. The
hypothesis `Algebra.Smooth R A` is an explicit argument, and includes finite
presentation. No domain hypothesis is imposed on `A`: a smooth algebra may have
several components. Each `P` is an arbitrary prime, not necessarily maximal.
The conclusion is about Mathlib's actual prime localization of that algebra.

`UniqueFactorizationMonoid` extends cancellation away from zero and gives
well-founded strict divisibility together with equivalence of irreducibility
and primality. A prime localization is a nontrivial local ring. Thus in this
conclusion the class expresses the usual unique factorization domain property;
there is no separate domain premise to be supplied by a caller. The universe
`u` is arbitrary and shared by the base and algebra; the proposition quantifies
over every such universe instance.

## Derived provenance

This is an internal reusable specialization of two source results, rather than
a quotation of one source theorem in this exact ring formulation:

- The Stacks Project, Descent, Lemma 35.18.4, [tag 036D](https://stacks.math.columbia.edu/tag/036D),
  states that regularity is local in the smooth topology. In particular a
  scheme smooth over a regular scheme is regular. The retained original is
  `036D.html` in source `stacks-smooth-local-regularity-036D-2026-11-01`, directory
  SHA256 `5496a4516f93572c6619901d7a60fd14a8b0c258b6f89742ae3944cd17de49e6`.
- The Stacks Project, More on Algebra, Lemma 15.123.2,
  [tag 0AG0](https://stacks.math.columbia.edu/tag/0AG0), proves that every regular
  local ring is a UFD. Its retained original is `0AG0.html` in source
  `stacks-regular-local-ufd-2026-10-29`, directory SHA256
  `49b665ff41945fd15cc966fe79e70688059509c0487cc27f32167fe1e1baed31`.

For the specialization, `Spec R` is regular and Noetherian: a DVR is a
Noetherian local PID, and its prime localizations are fields or DVRs, hence
regular local rings. Smoothness makes `Spec A` regular by 036D. The stalk at
`P` is the actual localization `A_P`, so 0AG0 gives the displayed conclusion.
This explains the mathematical derivation; the Lean file does not implement
any of these proof steps. The finite presentation in `Algebra.Smooth` is
sufficient for the usual smooth affine morphism convention.

The complete retained 036D and 0AG0 pages, including their proofs, were read.
Both tag pages have zero comments. The two comments on the retained section
15.123 page `0FJH.html` suggest additional power-series results and do not
correct Lemma 15.123.2. No source-specific errata note was found in the bounded
workspace/project-note filename check. This records the check without claiming
that no errata exist.

## Intended use and proof boundary

This ring statement is a prerequisite for factorial stalks of schemes smooth
over a DVR. Applying it on affine opens and transporting prime localizations
to stalks yields that geometric result. The final intended application is to
the total self-product of an abelian scheme over a DVR, for actual line-bundle
extension from the generic open. This proposition asserts no line-bundle
extension, no Picard comparison, and no arbitrary-valuation or ampleness
result. A proof must establish the displayed proposition without extra outer
hypotheses; an algebraically closed field argument alone does not do so.
