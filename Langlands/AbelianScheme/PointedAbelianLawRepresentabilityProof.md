# Representability of pointed abelian-scheme laws

`Langlands.AbelianScheme.pointedAbelianLawRepresentability.{u}` proves
`Langlands.AbelianScheme.PointedAbelianLawRepresentabilityStatement.{u}`.
For the pointed family in the statement, the construction gives a locally
finitely presented monomorphism into the affine base. For every test scheme,
a map to the base factors through this monomorphism exactly when the
pullback admits an abelian-scheme structure of the specified relative
dimension with identity induced by the section.

## Implemented proof

Write `X²` and `X³` for the relative square and cube over `S`. The projective
presentations of these powers use the tensor product of the pulled-back
invertible modules and
`Scheme.Modules.ClosedImmersionBySections.pullback_fst_tensor_pullback_snd`.
The powers are smooth by base change and composition. The construction
`PointedLaw.exists_homScheme` supplies the relative Hom schemes with source
`X`, `X²` and `X³` and target `X`. Their universal maps classify morphisms
on arbitrary tests by affine gluing.

The product of the Hom schemes for source `X²` and source `X` parametrizes
multiplication and inversion. The section fixes the unit. Evaluate
associativity, commutativity, the left unit identity and the left inverse
identity on the universal triple of points with this common parameter.
Each side is a morphism from the relative cube over the parameter scheme to
`X`. Each pair of sides therefore gives two maps from the parameter scheme
to the relative Hom scheme for source `X³`. Evaluating on the universal
triple suffices for all generalized points, because any triple with the
same parameter pulls back from the universal one.

The Hom scheme for `X³` is separated and locally of finite presentation
over `S`. The proof successively takes the equalizers of the four pairs,
using
`AlgebraicGeometry.exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated`.
The resulting closed immersion into the parameter scheme is locally of
finite presentation. The parameter scheme is also locally of finite
presentation over `S`, so their composite is locally of finite presentation.
Naturality of evaluation identifies the factorization condition through the
closed locus with the four equations on each test scheme.

`PointedLaw.exists_law_iff` identifies these equations with the existence of
an abelian scheme of relative dimension `g` on the actual pullback, with the
prescribed unit. `PointedLaw.Law.unique` uses rigidity on the identity map to
compare any two laws with that unit. If two maps to the locus have equal
composite to `S`, this uniqueness gives equality of their multiplication
and inversion. The Hom classifications identify their images in the
parameter scheme, and the closed immersion identifies the two maps to the
locus. This proves the monomorphism on all test schemes.

## Source

The closed-locus construction is the representability step of Mumford,
Fogarty and Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994),
Proposition 6.16, printed pp. 126–127 (PDF pp. 139–140). Uniqueness with a
fixed identity is Corollary 6.6, printed p. 117 (PDF p. 130). The source is
registered as
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`
with SHA-256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`.
The source expresses the group law by the difference map. The Lean
construction expresses it by multiplication and inversion with the unit
fixed, and uses affine gluing and the relative rigidity theorem on arbitrary
test schemes.
