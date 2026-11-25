# Affine full-centre quotients over an arbitrary base: statement

`Langlands.GroupScheme.RelativeAdjointQuotientExistenceStatement.{u}` says
that, for every scheme `S` and reductive group scheme `G` over `S`, there
exist a group scheme `A` over the same base and a homomorphism `q : G → A`
such that `A → S` is affine and
`RelativeRoot.IsFppfQuotient (center G) q` holds.

All schemes and groups are in the arbitrary common universe `u`. There is
no field, affine-base, quasi-compact-base, Noetherian, connected-base or
semilocal hypothesis. The quotient and its map are conclusions.

The published quotient predicate means that the underlying scheme map
of `q` is flat, surjective and locally of finite presentation, and that
the range of its actual scheme-theoretic kernel inclusion is exactly
`center G` on every relative scheme test. The centre functor records
commutation after every further test morphism. Thus the kernel includes
any non-smooth or non-reduced part of the centre, and surjectivity does
not mean surjectivity on the points of every original test.

This is a proposition definition, with no proof in this module. Its
conclusion does not assert reductivity, semisimplicity or trivial centre
of `A`, nor does it supply an action. It isolates the affine quotient
existence needed to apply the existing descent constructions. The
published `AdjointQuotientExistenceStatement` instead has a field base
and asks for the stronger field-specific `IsAdjointQuotient` structure.
`RelativeCentralQuotientStatement` takes the quotient as an input, and
`ReductiveRelativeCenterStatement` only represents the centre. Neither
of these is this existence assertion.

## Source and derived scope

Brian Conrad, *Reductive group schemes* (2014), registered source
`conrad-2014-reductive-group-schemes`, original PDF
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`:

- Theorem 3.3.4, original printed/PDF p.98, identifies the reductive
  centre with the full scheme-theoretic centre and in particular makes
  it flat and of multiplicative type.
- The proof of Lemma 3.3.2 on that page explains representability of
  the fppf quotient by a central subgroup of multiplicative type by an
  affine scheme of finite presentation over the base, citing SGA3
  VIII, 5.1 and IX, 2.3.
- Corollary 3.3.5, original printed/PDF pp.100–101, applies this
  quotient to a subgroup of the centre and gives the stronger
  reductivity, centre and maximal-torus conclusions.

The Lean proposition is a derived, weaker packaging of these results:
take the whole centre as the subgroup and retain affine
representability, the fppf covering map and its full kernel. It
requires no smoothness of that kernel. Its all-test kernel equality
is the sheaf-quotient meaning, rather than an assertion about only
geometric fibres or rational points. The cited original pages have
been read. The author-homepage snapshot registered as
`conrad-author-reductive-errata-check-2026-11-13` links these notes
without a separate correction link; no correction is being used here.

The proof of this proposition is `relativeAdjointQuotientExistence`, in
the separate module `Adjoint.RelativeExistenceProof`. This
statement alone proves neither the existence nor the uniqueness of a
quasi-split inner form over a semilocal base.
