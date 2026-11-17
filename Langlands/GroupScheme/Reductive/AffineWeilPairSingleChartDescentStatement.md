# Statement: descent of a Weil-restriction presentation along one étale cover

`Langlands.GroupScheme.AffineWeilPairSingleChartDescentStatement.{u}` is the core of the étale
descent step in Conrad's proof of Proposition 6.4.4 of *Reductive group schemes* (2014). It is
stated for a single étale cover of an affine base, with no simply connected or adjoint
hypothesis.

## The statement

All rings lie in one universe `u`. Let `A → A'` be an étale ring map with
`Spec A' → Spec A` surjective, and let `G` be a group scheme over `Spec A` whose underlying
scheme is affine and whose structure map is locally of finite type. Let `C` be a finite,
projective, étale `A'`-algebra and `H` a group scheme over `Spec C` with affine underlying
scheme and structure map locally of finite type. Assume that `H` is reductive
(`IsReductive H`), that every geometric fibre of `H` is almost simple
(`IsAlmostSimple (geometricFiber H t)`), and that there is an isomorphism of group schemes
over `Spec A'`

`G_{A'} ≅ AffineWeil.groupScheme A' C H`,

where `G_{A'}` is the base change of `G` along `Spec A' → Spec A`.

The conclusion is that there are a finite, projective, étale `A`-algebra `B` and a group scheme
`G'` over `Spec B` with affine underlying scheme and structure map locally of finite type, such
that `G'` is reductive, every geometric fibre of `G'` is almost simple, and
`G ≅ AffineWeil.groupScheme A B G'`.

## Source and provenance

Conrad, *Reductive group schemes* (2014), proof of Proposition 6.4.4 (p. 232 of the PDF): "In
view of the uniqueness assertions, by étale descent we may work étale-locally on S." Remark
6.4.5 (p. 233) states that the proposition and its proof hold with "adjoint" in place of "simply
connected". The source does not state this descent step separately. This formulation is
derived from it and is internal to the project:

- the base is affine, `S = Spec A`, and the étale cover is a single étale `A`-algebra `A'`
  whose spectrum maps onto `Spec A`;
- Conrad's "absolutely simple fibres" for semisimple groups is the Library's
  `IsAlmostSimple` on every geometric fibre, together with `IsReductive`;
- Conrad's finite étale cover `S' → S` is a finite, projective, étale algebra. Unlike the
  target theorems, the statement does not require `Spec C → Spec A'` or `Spec B → Spec A` to
  be surjective;
- only existence is asserted. Uniqueness of the pair (Conrad's second paragraph) is proved
  separately from factor rigidity (`WeilFactorIdempotentRigidityStatement`).

## Use

`Langlands.GroupScheme.affineWeilPairEtaleDescent_of_singleChart` (module
`Langlands.GroupScheme.Reductive.AffineWeilPairEtaleDescentReduction`) derives the
covering-family statement `AffineWeilPairEtaleDescentStatement` from this statement and
`WeilFactorIdempotentRigidityStatement`. It combines finitely many charts into one product chart.

## Why the statement should hold

Let `A'' = A' ⊗_A A'`. The two pullbacks of the presentation to `A''` are presentations of the
same group `G_{A''}`. By uniqueness of Weil pairs (Conrad, Proposition 6.4.4, second
paragraph), the isomorphism between them comes from a unique isomorphism of pairs. Uniqueness
makes these pair isomorphisms satisfy the cocycle condition over `A' ⊗_A A' ⊗_A A'`. Faithfully
flat descent of algebras then gives `B` with `A' ⊗_A B ≅ C`, and étale descent of affine group
schemes along `Spec C → Spec B` gives `G'`. The isomorphism `G ≅ R_{B/A}(G')` is checked after
the faithfully flat base change to `A'`. Reductivity and almost simple geometric fibres hold
for `G'` because they hold étale-locally.
