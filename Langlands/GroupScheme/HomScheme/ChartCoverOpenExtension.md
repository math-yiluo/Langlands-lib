# Extension of chart covers along open immersions of bases

Worker 1412. This is an internal construction for the open-restriction step of
SGA 3, Exposé XI, proof of Theorem 4.1, registered source
`sga3-exposes-xi-xii-xiv-gille-polo-2008`, `Expo11.pdf`, PDF page 21. That
proof reduces to an affine base. Here charts of the restrictions of `G` to the
members of an open cover of `S` are pushed back to charts of `G` itself.

Families over a changed base `S'` are viewed over `S` with
`TorusSubgroupModuli.pushFamily` from
`Langlands.GroupScheme.HomScheme.ChartCoverTransport`. That module's
`familyHom_pushFamily` compares the evaluations of a pushed family with those of
the original family.

## Statements and proofs

- `familyHom_pushFamily_homMk` restates `familyHom_pushFamily` for a test object
  `T` over `S` whose structure morphism is given as `t ≫ f`, with an explicit
  parameter `c` over `t`. The proof destructures `T`, substitutes both
  factorization equations and applies `familyHom_pushFamily`.
  `evaluate_pushFamily_homMk_iff` deduces that two pushed families have equal
  evaluations at such parameters exactly when the original families do. The
  two evaluations differ by the same comparison isomorphism, and
  `range_postcomp_eq_iff` reflects equality of ranges.
- `pushFamily_injective`: if `f` is a monomorphism and the original family has
  injective evaluation, so does the pushed family. Two parameters `a, b` over
  `S` with equal evaluations have the same composite to `S'` after cancelling
  `f`. The previous lemma then gives equal evaluations over `S'`, so `a.left`
  equals `b.left`.
- `pushFamily_isOpen`: let `f` be an open immersion and let `j` be an open chart
  over `S'`. Fix a test object `T` over `S` and a closed torus `i` of `G_T`. Let
  `ι : W = S' ×_S T → T` be the part of `T` over `S'`. `ι` is an open immersion,
  with projection `t : W → S'`. Evaluating `i` along `ι` and composing with the
  inverse comparison isomorphism gives a closed torus `i₀` of `(G_{S'})_W`.
  Pushing `i₀` forward recovers the evaluation of `i` along `ι`. The open-locus
  property of `j` applied to `i₀` gives an open `V' ⊆ W`, and the locus for the
  pushed family is the open image `ι(V')`. For a test morphism `b : T' → T` that
  factors as `c ≫ ι`, the auxiliary statement `core` shows two things are
  equivalent: a parameter matches `i` at `b` over `S`, or the corresponding
  parameter matches `i₀` at `c` over `S'`. If a parameter `a` matches, `b`
  factors through `W` by the pullback property, so the image of `b` lies in
  `ι(V')`. Conversely, if the image of `b` lies in `ι(V') ⊆ ι(W)`, then `b`
  lifts through `ι` (`IsOpenImmersion.lift`). Injectivity of `ι` on points
  shows that the lift lands in `V'`, and the open-locus property of `j` gives
  the parameter.
- `isOpenChart_pushFamily` assembles these facts for an open immersion `f`.
  Closedness is `isClosedSubgroup_pushFamily` and the torus property is
  unchanged. Smoothness of the parameter morphism `U.hom ≫ f` holds because
  open immersions are smooth.
- `exists_evaluate_pushFamily`: suppose a field point `x` of `S` factors through
  `S'` as `x'`. Then every closed torus of `G_x` is the evaluation of some pushed
  family. Transport the torus to `(G_{S'})_{x'}` with the inverse comparison
  and apply the field-point coverage over `S'`. Then push the parameter forward
  with `Over.map f`; `familyHom_pushFamily` and `range_postcomp_congr` give
  equality of ranges.
- `hasChartCover_of_openCover`: let `p l : S' l → S` be open immersions whose
  images cover `S`. If every `G_{S' l}` has a chart cover, so does `G`. The new
  index type is the sigma type of the old index types, still in `Type u`, and
  the families are the pushed families. A field point lands in the image of
  some `p l`, because the spectrum of a field has one point. It then lifts
  through `p l`, and `exists_evaluate_pushFamily` applies.

No hypothesis on `S` is added, and all constructions are uniform in the universe
`u`.
