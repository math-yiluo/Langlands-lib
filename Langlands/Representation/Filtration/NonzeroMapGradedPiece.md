# Nonzero maps out of a filtered representation

Author: Worker 1713.

This internal algebraic supporting unit is the dual of
`Filtration.IrreducibleEmbedding`: there a nonzero map *into* a finitely
filtered representation gives a nonzero map into a graded piece; here a
nonzero map *out of* a finitely filtered representation gives a nonzero map
out of a graded piece. The coefficient ring, acting monoid, filtered carrier
and target carrier have independent universes, so the target need not live
in the universe of the filtered functor. No topology, smoothness, finite
dimension, irreducibility, or simple-factor hypothesis is used.

## Object filtrations

Fix a supplied `ObjectRepFiltration A n` and an intertwiner `f` from `A` to
an arbitrary representation `σ`.

- `restrictToStep` restricts `f` to the actual invariant subspace at step
  `i`; `restrictToStep_apply` evaluates it.
- `mapFromGraded`: if `f` vanishes on step `i.castSucc`, then the
  restriction of `f` to step `i.succ` kills the pulled-back lower step, and
  `Submodule.liftQ` descends it to the actual graded quotient
  `gradedRepresentation i`. Intertwining is checked on representatives
  through the surjective `gradedProjection i`.
  `mapFromGraded_projection` states that the descended map sends the class
  of `v` to `f v`.
- `exists_mapFromGraded_ne_zero`: if `f ≠ 0`, there is an index `i` such
  that `f` vanishes on step `i.castSucc` and the descended map is nonzero.
  Proof: the property "f vanishes on step j" holds at the zero step (which
  is `⊥`) and fails at the last step (which is `⊤`, and `f ≠ 0`). Finite
  induction over `Fin` gives adjacent steps where it holds below and fails
  above. If the descended map were zero, `mapFromGraded_projection` would
  make `f` vanish on the upper step, a contradiction. At length zero the
  two endpoint facts already contradict each other.

## Functor filtrations and gluing

- `RepFunctorFiltration.exists_graded_intertwiningMap_ne_zero` evaluates a
  natural finite filtration at an input `X` with `atObject` and applies the
  object result: a nonzero intertwiner out of `F.obj X` gives a nonzero
  intertwiner out of `(s.graded i).obj X` for some `i`.
- `RepFunctorFiltration.exists_piece_intertwiningMap_ne_zero` transports
  this along the natural isomorphisms of `HasGradedPieces`: the graded map
  is precomposed with the inverse isomorphism at `X`, which stays nonzero
  because precomposing again with the forward isomorphism recovers it.
- `IsGluedFrom.exists_piece_intertwiningMap_ne_zero` unpacks the
  permutation in `IsGluedFrom` and returns the permuted index.

## Provenance and use

This is a derived elementary construction, not a translated literature
assertion. In Renard's proof of III.2.5 / VI.5.3 (Renard 2026, PDF pp.79 and
179) a nonzero morphism `r_P i_P τ' → τ` is analysed through the
geometric-lemma filtration of `r_P ∘ i_P`; this unit supplies the step
"some graded piece admits a nonzero morphism to `τ`". It does not prove the
geometric lemma, Frobenius reciprocity, or any statement about the pieces.
The only project dependency is `Filtration.SingleSurvivingGrade` (for
`atObject`) and, through it, the actual filtration definitions.
