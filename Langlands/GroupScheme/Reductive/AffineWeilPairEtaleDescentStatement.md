# Statement: étale descent of Weil-restriction presentations with almost simple factors

`Langlands.GroupScheme.AffineWeilPairEtaleDescentStatement.{u}` is the descent step in
Conrad's proof of Proposition 6.4.4 of *Reductive group schemes* (2014), stated over an affine
base and with no simply connected or adjoint hypothesis.

## The statement

All rings and index types lie in one universe `u`. The data are:

- a commutative ring `A` and a group scheme `G` over `Spec A` whose underlying scheme is affine
  and whose structure map is locally of finite type;
- an index type `ι` (arbitrary, not necessarily finite) and étale `A`-algebras `R i` such that
  every point of `Spec A` lies in the image of some `Spec (R i) → Spec A`;
- for every `i`, a finite, projective, étale `R i`-algebra `B' i` with `Spec (B' i) → Spec (R i)`
  surjective, and a group scheme `G₁ i` over `Spec (B' i)` with affine underlying scheme and
  structure map locally of finite type.

Assume that every `G₁ i` is reductive (`IsReductive`), that every geometric fibre of every
`G₁ i` is almost simple (`IsAlmostSimple (geometricFiber (G₁ i) t)`), and that for every `i`
there is an isomorphism of group schemes over `Spec (R i)`

`G_{R i} ≅ AffineWeil.groupScheme (R i) (B' i) (G₁ i)`,

where `G_{R i}` is the base change of `G` along `Spec (R i) → Spec A`.

The conclusion is that there are

- a finite, projective, étale `A`-algebra `B` with `Spec B → Spec A` surjective, and
- a group scheme `G'` over `Spec B` with affine underlying scheme and structure map locally of
  finite type,

such that `G'` is reductive, every geometric fibre of `G'` is almost simple, there is an
isomorphism `G ≅ AffineWeil.groupScheme A B G'`, and for every `i` there is an
`R i`-algebra isomorphism `e : R i ⊗[A] B ≃ₐ[R i] B' i` such that the base change of `G'` along
the spectrum of the ring map `B → B' i`, `b ↦ e (1 ⊗ b)`, is isomorphic to `G₁ i`.

Here `R i ⊗[A] B` is an `R i`-algebra through its left factor, and
`Algebra.TensorProduct.includeRight` is the map `b ↦ 1 ⊗ b`.

## Source and provenance

Conrad, *Reductive group schemes* (2014), Proposition 6.4.4 and its proof (pp. 232–233 of the
PDF). The proof begins: "In view of the uniqueness assertions, by étale descent we may work
étale-locally on S." Remark 6.4.5 states that the proposition and its proof remain valid with
"adjoint" in place of "simply connected". This statement isolates that étale descent step as a
derived, type-independent result. It is not stated separately in the source; its formulation
is internal and chosen so that both the simply connected and the adjoint versions over an
affine base can use it.

- **Base.** Conrad works over an arbitrary non-empty scheme `S`. Here `S = Spec A` is affine,
  and the empty case is allowed: then any family satisfies the covering hypothesis and the
  conclusion holds with `B = 0`.
- **Fibres.** Conrad's factors have "absolutely simple fibres". For a semisimple group over an
  algebraically closed field this is the Library's `IsAlmostSimple` (semisimple, noncommutative,
  and with no nontrivial proper smooth connected closed normal subgroup). The hypotheses ask
  for this on every geometric fibre of every `G₁ i`, and for `IsReductive (G₁ i)`. No simply
  connected or adjoint condition appears, in either the hypotheses or the conclusion.
- **Local presentations.** Conrad's `S' → S` is a finite étale cover. Here the local covers are
  the finite, projective, étale algebras `B' i` with surjective spectrum maps, and the global
  cover `B` is required to have the same properties.
- **Covering family.** Étale-local data are given as an arbitrary family of étale algebras whose
  spectra jointly cover `Spec A`. For example, one can take one chart for every point of
  `Spec A`. Since étale maps are open and `Spec A` is quasi-compact, finitely many charts
  suffice, and their product is a single faithfully flat étale `A`-algebra. The statement does
  not require the charts to be combined by the user.
- **Recovery of local pairs.** The last clause records that the descended pair restricts to each
  given local pair. A user can then transfer fibre properties of the `G₁ i` (for example
  adjointness) to `G'`: every point of `Spec B` lies under a point of some `Spec (B' i)`.
- **Hypotheses on `G`.** `G` is only assumed affine and locally of finite type over `Spec A`.
  Every reductive group scheme over `Spec A` satisfies these hypotheses.

## Why the statement should hold

By the uniqueness half of Proposition 6.4.4, every isomorphism of Weil restrictions
`R_{B₁/T}(H₁) ≅ R_{B₂/T}(H₂)` of such pairs comes from a unique pair consisting of an algebra
isomorphism `B₂ ≃ B₁` and a group isomorphism over it. Uniqueness makes these pair isomorphisms
compatible with base change and composition. On the overlaps `R i ⊗[A] R j`, the two pulled-back
presentations of `G` therefore give canonical pair isomorphisms, and these satisfy the cocycle
condition. Descent of finite étale algebras along the faithfully flat étale cover gives `B`, and
étale descent of affine group schemes over `Spec B` gives `G'`. Reductivity and almost simple
geometric fibres hold for `G'` because they hold étale-locally.
