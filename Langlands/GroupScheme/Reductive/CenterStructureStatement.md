# Scheme-theoretic centre existence and field base change

Author: Worker 1360.

This module states two results for actual connected reductive group schemes over
arbitrary fields. Both declarations are proposition definitions at arbitrary
universe `u`. They are targets for subsequent proofs; this module proves neither
existence nor base-change compatibility.

## Original sources and derived scope

- B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive groups*, second edition
  (2015), registered source `conrad-gabber-prasad-2015-pseudo-reductive`,
  SHA-256 `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`:
  Definition A.1.8, printed p.468 / PDF p.494, fixes actual closed subgroup
  inclusions. Definition A.1.9 and its following discussion, printed
  pp.468–469 / PDF pp.494–495, give a closed scheme-theoretic centralizer when
  the acted-on closed subscheme is geometrically reduced and separated, and
  state that its formation commutes with every ground-field extension.
  Definition A.1.10, printed p.469 / PDF p.495, defines the centre of a smooth
  group as its centralizer of itself: conjugation is trivial after arbitrary
  base extension. The same page gives `Z(SL_p) = μ_p` in characteristic `p`,
  showing why the centre must retain its nonreduced structure. No
  source-specific errata note was present in the supplied public notes.
- J. S. Milne, *Algebraic Groups* (2017), registered source
  `milne-2017-algebraic-groups`,
  SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`:
  the discussion immediately before Proposition 19.10, printed p.400 /
  PDF p.416, describes the centre of a reductive group and explicitly allows
  it to be nonsmooth and disconnected. Corollary 17.62(a) and the proof of
  17.62(c), printed pp.372–373 / PDF pp.388–389, concern the full centre and
  its compatibility with extension of the base field. Remark 17.63, printed
  p.373 / PDF p.389, identifies the quotient by the full centre as the
  adjoint group.
- Milne's official 2017-book errata, registered snapshot
  `milne-2017-algebraic-groups-errata-2026-11-02`,
  SHA-256 `a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
  was read in full. It gives no correction to these centre assertions. Its
  correction to 12.41 is relevant to Milne's proof of the separate quotient
  assertion 17.62(e); no quotient assertion is a target of this module.

The targets are a derived specialization and packaging of these sources, not
verbatim source declarations. CGP's centralizer discussion has wider scope than
connected reductive groups and defines the centre there for smooth ambient
groups. Here `IsConnectedReductive G` supplies smoothness and affineness, hence
the geometric reducedness, local finite type and separatedness needed when
applying that discussion to the conjugation action of `G` on itself. The
published `center` in `Rational.Characters` expresses trivial conjugation using
commutation on every test scheme after every change of test scheme. Passing
from the source's affine-algebra description to this full scheme-functor
description is part of the intended proof obligation.

## Existence target

`Langlands.GroupScheme.SchemeTheoreticCenterExistenceStatement` quantifies
every field `k : Type u` and every actual group scheme `G` over `Spec k`.
Its only premise is `IsConnectedReductive G`. Its conclusion supplies an actual
group scheme `Z` and homomorphism `z : Z ⟶ G` satisfying the published
`IsSchemeTheoreticCenter z`.

That predicate means `IsClosedSubgroup z` and
`SubgroupFunctor.range z = center G`. Thus closedness and representation of
the full centre are conclusions. A chosen centre, a representability premise,
and smoothness or reducedness of `Z` are not required.

## Field base-change target

`Langlands.GroupScheme.SchemeTheoreticCenterBaseChangeStatement` quantifies
every pair of fields `k K : Type u`, every `Algebra k K`, every actual `G`
and `Z` over `Spec k`, and every `z : Z ⟶ G`. For a connected reductive `G`,
the premise `IsSchemeTheoreticCenter z` implies

```lean
IsSchemeTheoreticCenter
  ((GroupScheme.baseChange (algebraBaseMap k K)).map z)
```

The conclusion concerns the actual pullback homomorphism `Z_K ⟶ G_K`.
Its image must equal `center G_K` on all test schemes over `Spec K`, including
all subsequent changes of test scheme. Neither field is required to be
perfect, and the extension need not be finite, algebraic or separable.
Both fields lie in the same arbitrary universe, as required by the existing
`algebraBaseMap` and `baseChange` interfaces.

The targets retain finite nonreduced centres such as `μ_p`. They neither
replace the centre with its reduced subscheme or largest central torus nor
identify it with the abstract centre of `G(k)`. They make no assertion about
an adjoint quotient or a simply connected cover of the derived group; those
are separate constructions. Existing uniqueness and point equivalences for
represented subgroup functors are reused through the published predicates
and are not new targets here.
