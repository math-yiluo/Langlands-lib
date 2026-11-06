# Closed normalizers of smooth connected subgroups

`Langlands.GroupScheme.SmoothConnectedNormalizerStatement.{u}` asserts the
following over every scheme `S : Scheme.{u}`. Let `G` be an actual smooth affine
group scheme over `S`, and let `i : H ⟶ G` be a closed subgroup whose structure
morphism is smooth and geometrically connected. There exist an actual group
scheme `N` and a homomorphism `j : N ⟶ G` such that:

- `j` is a closed immersion;
- `j` is locally of finite presentation; and
- `j` represents the normalizer of the subgroup functor `range i` on every
  scheme over `S`.

Here `IsRepresentedBy` says that `j` is a monomorphism over `S` and its
pointwise range equals the specified normalizer functor. Normalizer membership
requires conjugation in both directions to preserve the subgroup after every
refinement of the test scheme. Thus the conclusion retains all tests, including
nonreduced tests. It does not assert smoothness or flatness of `N`.
A closed immersion is quasi-compact and separated, so the added local finite
presentation condition expresses the finitely presented closed representative.
There is no Noetherian assumption, and no connectedness assumption on `G`.

This is the subgroup case of Brian Conrad, *Reductive group schemes* (2014),
Proposition 2.1.6, printed and one-based PDF pp.61–62, source
`conrad-2014-reductive-group-schemes`, SHA256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The source assumes a finitely presented closed subscheme `Y` that is smooth
with nonempty geometrically connected fibres. In this formulation `Y = H`:
the identity section makes every fibre nonempty, and smoothness together with
closedness in the smooth affine `G` gives finite presentation over `S` and of
the closed immersion. This finiteness implication is part of the proof
obligation. Proposition 2.1.6 uses finite infinitesimal neighbourhoods and
Noetherian approximation; it does not require the coordinate algebra of `H`
to be projective as a module over the base.

This module defines a proposition only. A proof of the closed representability
assertion remains required.
