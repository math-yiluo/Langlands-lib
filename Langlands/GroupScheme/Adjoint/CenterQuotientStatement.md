# The quotient of a connected reductive group by its centre: statements

Worker 1400 (draft) and Worker 1499 (source check).

This module defines two propositions and proves nothing. It constructs no
quotient. Proofs of the propositions are separate tasks.

## Common hypotheses

Both propositions quantify over a universe `u`, a field `k : Type u`, group
schemes `G` and `Q` over `Spec k` and a group-scheme homomorphism
`q : G ⟶ Q`, and assume:

1. `IsConnectedReductive G`: `G` is smooth, affine and connected over
   `Spec k`, and its base change to `AlgebraicClosure k` has trivial
   unipotent radical, that is, every smooth connected unipotent normal
   closed subgroup of that base change is trivial (published in
   `Langlands.GroupScheme.Reductive.Basic`).
2. `Q.X.hom` is affine (`IsAffineHom`) and locally of finite type.
3. `RelativeRoot.IsFppfQuotient (center G) q`, the published predicate of
   `Langlands.GroupScheme.Rational.RootSubgroupStructureStatement`, used
   unchanged: the underlying scheme morphism of `q` is flat, surjective and
   locally of finite presentation, and the range functor of the actual
   pullback kernel `kernelι q` equals `center G` on every test scheme over
   `Spec k`.

`center G` is the published scheme-theoretic centre functor of
`Langlands.GroupScheme.Rational.Characters`: a point `g` of `G` over `T` is
central when, for every `a : T' ⟶ T`, the restriction `a ≫ g` commutes with
every point of `G` over `T'`. The centre is not replaced by its reduced
subgroup or its rational points; it may be nonsmooth, for example `μ_p` in
`SL_p` in characteristic `p`. No smoothness, reducedness or finiteness of the
kernel of `q` is assumed. Surjectivity is surjectivity of underlying
topological spaces.

The hypotheses do not name a particular construction of `Q`; any `q` with
these properties is covered. The existence of such a `q` is not asserted
here.

## `CenterQuotientReductiveStatement`

Under the common hypotheses, `IsConnectedReductive Q`: `Q` is smooth, affine
and connected over `Spec k`, and its base change to `AlgebraicClosure k` has
trivial unipotent radical.

## `CenterQuotientCenterTrivialStatement`

Under the common hypotheses, `center Q = ⊥`: on every test scheme `T` over
`Spec k`, the only central point of `Q(T)` in the above sense is the
identity point.

Together, the two conclusions are the components `IsConnectedReductive Q`
(inside the field `isSemisimple`) and `center Q = ⊥` (the field
`center_eq_bot`) of the Library's `IsAdjoint Q`
(`Langlands.GroupScheme.Reductive.Semisimple`). The remaining component,
`HasFiniteCenter Q`, is not part of these statements.

## Sources

- J. S. Milne, *Algebraic Groups* (2017), source ID
  `milne-2017-algebraic-groups`.
  - Corollary 17.62(e), printed p.372 / PDF p.388, with its proof on printed
    p.373 / PDF p.389: for a reductive group `G`, the quotient `G/Z(G)` has
    trivial centre.
  - Remark 17.63, printed p.373 / PDF p.389: the quotient of a reductive
    group by its centre is an adjoint group, where an adjoint group is a
    semisimple group with trivial centre.
  - 6.44 and 6.46, printed p.135 / PDF p.151: a connected group variety `G`
    over `k` is semisimple if its geometric radical `R(G_{k^a})` is trivial,
    and reductive if its geometric unipotent radical `R_u(G_{k^a})` is
    trivial. Since `R_u(G_{k^a})` is contained in `R(G_{k^a})`, a semisimple
    group is reductive; this gives the reductivity of `G/Z(G)` from Remark
    17.63. Milne's reductive groups are connected group varieties.
  - Theorem 5.13, printed p.101 / PDF p.117: a quotient map is determined
    by its kernel up to unique isomorphism, so the hypotheses determine `Q`
    up to isomorphism as Milne's `G/Z(G)`. Definition 5.5, printed p.99 /
    PDF p.115: quotient maps are the faithfully flat homomorphisms.
  - Milne's centre `Z(G) = C_G(G)` is the scheme-theoretic one
    (Proposition 1.92 and the following definition, printed pp.33–34 / PDF
    pp.49–50), defined by commutation on all `k`-algebras.

The official Milne errata snapshot of 2026-11-02
(`milne-2017-algebraic-groups-errata-2026-11-02`) has no correction to 1.92,
5.5, 5.13, 6.44, 6.46, 17.62 or 17.63. It corrects Corollary 12.41 (printed
p.244), cited in the proof of 17.62(e), to require `N` central in `H`. That
proof applies 12.41 to the centre `Z(G)` inside its preimage `Z'`, where
`Z(G)` is central, so the correction leaves 17.62(e) intact.

## Derived packaging

The statements are derived: Milne states facts about the quotient `G/Z(G)`
of algebraic groups and `k`-algebras. The Lean statements transcribe them as
follows.

- `G/Z(G)` is replaced by an arbitrary affine, locally finite type (hence
  finite type) `Q` with an fppf homomorphism `q` whose actual kernel is the
  full centre on all test schemes. Such a `Q` is an algebraic group and `q`
  is a quotient map in Milne's sense (5.5), so by Milne 5.13 such a `Q` is
  Milne's `G/Z(G)`.
- Local finite presentation of `q` is not named in the source; it holds for
  morphisms of schemes of finite type over a field and is recorded to match
  `RelativeRoot.IsFppfQuotient`.
- Milne's "reductive" is the Library's `IsConnectedReductive`, and Milne's
  "trivial centre" is `center Q = ⊥` on all test schemes over `Spec k`.

This module does not prove these comparisons or the propositions; they are
obligations of the proof tasks for these statements.
