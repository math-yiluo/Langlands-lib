# Proof: the Isomorphism Theorem for split reductive groups over a reduced local ring

Module `Langlands.GroupScheme.Reductive.LocalSplitReducedIsomorphismProof`.

This module proves the Library statement `LocalSplitReducedIsomorphismTheoremStatement`
(theorem `localSplitReducedIsomorphismTheorem`). Two split reductive groups over a reduced local
ring with isomorphic fibrewise root data are isomorphic. This is Conrad, *Reductive group
schemes* (2014), Thm. 6.1.17 (PDF p. 197), for a base `Spec R` with `R` local and reduced.

## Structure of the proof

The Library's `localSplitReducedIsomorphismTheorem_of_simpleRootGroups` (module
`LocalSplitReducedIsomorphismReduction`) reduces the theorem to
`LocalSplitSimpleRootGroupStatement`. That reduction glues isomorphisms along big cells,
checks compatibility at field points (`R` is reduced), and compares split groups over fields.
The statement asks, for every base `b`, for a family `u : J → (𝔾ₐ ⟶ G)` such that, for each
simple root `a`,

- `u a` is a root parametrization for `a`, and `u (-a)` one for `-a`
  (with `-a = P.reflectionPerm a a`);
- `weylPoint (u a) (u (-a)) = u(-a)(-1) · u(a)(1) · u(-a)(-1)` acts on the torus through the
  simple reflection `s_a` (`IsWeylPoint`).

`localSplitSimpleRootGroup` proves this statement.

1. Worker 712's `LocalRootGroup.exists_rootParametrization` (module `LocalRootGroupParam`)
   gives a root parametrization `u α` for every root `α`.
2. For each simple root `a`, `localWeylNormalization_of_field fieldWeylNormalization`
   gives a root parametrization `v a` of `-a` such that `weylPoint (u a) (v a)` is a Weyl point
   for `s_a`. `localWeylNormalization_of_field` is Worker 712's proof of
   `LocalWeylNormalizationStatement` from `FieldWeylNormalizationStatement` (module
   `LocalWeylNormalizationProof`). `fieldWeylNormalization` is the field case (module
   `LocalWeylNormalizationField`).
3. The family `u'` takes the value `v a` at `-a` for each simple root `a`, and the value
   `u α` elsewhere. This is well defined. The negative of a simple root is not simple
   (`RootPairing.Base.root_ne_neg_of_ne`). And `-a = -a'` forces `a = a'`, because `P.root`
   is injective. So `u'` agrees with `u` at the simple roots and with `v` at their negatives,
   and the two conditions above hold.

`localSplitReducedIsomorphismTheorem` then follows from
`localSplitReducedIsomorphismTheorem_of_simpleRootGroups`.

## Provenance

Source: Brian Conrad, *Reductive group schemes* (SGA3 summer school notes, 2014), Thm. 6.1.17
(the Isomorphism Theorem, PDF p. 197). Root groups over a base are Thm. 4.1.4 (PDF p. 110), and
the normalized Weyl elements are Cor. 5.1.9 (PDF pp. 140-141). The route through big cells,
field points and the explicit Weyl normalization is internal to this formalization. The
Markdown files of the imported modules describe each step.
