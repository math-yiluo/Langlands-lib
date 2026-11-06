# Jacquet modules of contragredients on Levi points from the literal Levi image

Lean module: `Langlands.Representation.Exponents.LeviJacquetContragredientReduction`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

## Source

Renard 2026, *Représentations des groupes réductifs p-adiques*, VI.9.6 Theorem (VI.9.6.2)
(printed p.201, PDF p.207): `r_{P̄}^G(π~) ≅ (r_P^G π)~` for every smooth `π`. Renard obtains
it from the `M`-equivariant duality `⟨,⟩_P` (Proposition on PDF p.208), which is built from
the unipotent radicals `N`, `N̄` inside `G`. The Library states (VI.9.6.2) for represented
parabolics (`LeviJacquetContragredientStatement`,
`Exponents/LeviJacquetContragredientStatement.lean`), with Jacquet functors valued in smooth
representations of `M(F)` itself. This module proves the step from an isomorphism for the
literal subgroups `N(F)`, `N̄(F)` and the Levi image in `G(F)` to that statement. Renard does
not write this step, because he identifies `M(F)` with its image; it is internal
bookkeeping.

## Statement

`nonempty_leviJacquetContragredient_iso_of_pointImage` has the following setting. The field
`k` is a topological field with `T2Space k`. `G` is a group scheme over `k` with affine
structure morphism, and `G(F)` has its canonical point topology and is locally compact and
nonarchimedean. The data are those of `LeviJacquetContragredientStatement`: represented
parabolics `p : P ⟶ G` and `pbar : Pbar ⟶ G` with rational Levis `m : M ⟶ P` and
`mbar : M ⟶ Pbar`, geometric unipotent radicals `n`, `nbar` and isomorphic multiplication maps.
The hypotheses are:

- `hP : mbar ≫ pbar = m ≫ p`, the first equality of `LeviJacquetContragredientStatement`;
- `hiso`: for all proofs `hU`, `hO` of closedness of `pointImage (nbar ≫ pbar)` and
  `pointImage (n ≫ p)`, and all proofs `hMU`, `hMO` that `pointImage (m ≫ p)` normalizes them,
  the natural isomorphism

  `SmoothRep.contragredientFunctor ⋙ normalizedJacquetFunctor (pointImage (nbar ≫ pbar)) (pointImage (m ≫ p)) hU hMU ≅ (normalizedJacquetFunctor (pointImage (n ≫ p)) (pointImage (m ≫ p)) hO hMO).op ⋙ SmoothRep.contragredientFunctor`

  exists. In words, `r_{N̄(F)}(π~) ≅ (r_{N(F)} π)~` naturally in `π`, as smooth
  representations of the Levi image `pointImage (m ≫ p)`.

With `M(F)` given the topology `leviPointTopology m hm` and the nonarchimedean structure
`leviPoints_nonarchimedeanGroup p m hp hm`, the conclusion is the conclusion of
`LeviJacquetContragredientStatement`:

`Nonempty (SmoothRep.contragredientFunctor ⋙ leviJacquetFunctor pbar mbar nbar … ≅ (leviJacquetFunctor p m n …).op ⋙ SmoothRep.contragredientFunctor)`.

The statement's second equality, `P(F) ∩ P̄(F) = M(F)`, and the local-field and
connected-reductive hypotheses are not hypotheses here. They are needed only to produce
`hiso`. The hypothesis `hiso` has the form of the conclusion of
`nonempty_contragredient_normalizedJacquet_iso_of_splits`, with `U = pointImage (nbar ≫ pbar)`,
`M = pointImage (m ≫ p)` and `O = pointImage (n ≫ p)`.

## Proof

`leviJacquetFunctor pbar mbar nbar …` is by definition the normalized Jacquet functor of
`pointImage (nbar ≫ pbar)` to the Levi image `pointImage (mbar ≫ pbar)`, followed by pullback
along `leviPointsEquiv pbar mbar hpbar hmbar`. The same holds for `(p, m, n)` with
`leviPointsEquiv p m hp hm`. Apply `Aubert.General.nonempty_contragredient_normalizedJacquet_pullback_iso`
(`Aubert/General/ContragredientJacquetTransport.lean`) with:

- `U = pointImage (nbar ≫ pbar)` and `O = pointImage (n ≫ p)`, closed by
  `isClosed_pointImage_comp`;
- `M₁ = pointImage (mbar ≫ pbar)` and `M₂ = pointImage (m ≫ p)`, equal by `hP`, normalizing
  `U` and `O` by `pointImage_le_normalizer`;
- `e₁ = leviPointsEquiv pbar mbar hpbar hmbar` and `e₂ = leviPointsEquiv p m hp hm`. These have
  the same values in `G(F)`: by `leviPointsEquiv_apply_coe` they are the point maps of
  `mbar ≫ pbar` and `m ≫ p`, which agree by `hP`;
- `hiso` specialised to these closedness proofs.

The topology `leviPointTopology mbar hmbar`, in which `e₁` is stated, agrees definitionally
with `leviPointTopology m hm`. Both are the canonical point topology of `M` and differ only in
a proof of affineness.
