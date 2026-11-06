# Finite fibre powers of a scheme chart of a presheaf

Internal infrastructure for the proof of `RationalPointEtaleLiftStatement` (Knutson,
*Algebraic Spaces*, II.6.4; Stacks Project, Tag 0BBP). The Galois-descent argument there
uses the `G`-fold fibre power `V ×_X ⋯ ×_X V` of an étale chart `a : h_V → X`, indexed by
the Galois group `G`, with `G` acting by permuting the factors. This module builds that
fibre power. It is a standard construction, not taken from a specific statement in the
literature.

Throughout, `S` is a scheme, `X : Presheaf S` a presheaf on schemes over `S`, `V : Over S`
a scheme over `S`, and `a : (schemeYoneda S).obj V ⟶ X` a morphism from the represented
presheaf of `V`. All names are in the namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`.

## Definitions

- `ChartFibrePower a ι` is a structure holding an `ι`-fold fibre power of `a`:
  - `obj : Over S`, the fibre power;
  - `pr : ι → (obj ⟶ V)`, projections with equal images in `X` (`w`);
  - `lift`, which sends a family `y : ι → (T ⟶ V)` with equal images in `X` to a morphism
    `T ⟶ obj`, with `lift_pr : lift y hy ≫ pr i = y i`;
  - `hom_ext`: morphisms `T ⟶ obj` with equal projections are equal.

  So `obj` represents families of `T`-points of `V` with a common image in `X`. The
  structure records this universal property only for test objects in `Over S`.
- `ChartFibrePower.one a` is the one-fold fibre power `V` itself, indexed by `Fin 1`.
- `ChartFibrePower.reindex P e` reindexes a fibre power along an equivalence `e : κ ≃ ι`.
- For a relatively representable `a` and `P : ChartFibrePower a (Fin (n + 1))`,
  `ChartFibrePower.succ ha P : ChartFibrePower a (Fin (n + 2))` adds one factor. Its object
  `succObj` is the represented pullback of `a` along `P.toBase = h(P.pr 0) ≫ a`. The new
  factor `succFst` is the pullback projection to `V`; the old factors are the composites of
  `succSnd` with `P.pr i`.
- `ChartFibrePower.fin ha n : ChartFibrePower a (Fin (n + 1))` is obtained by iterating
  `succ`, starting from `one`.
- For a group `G` and `P : ChartFibrePower a G`, `P.act g : P.obj ⟶ P.obj` is the lift of
  the family `e ↦ P.pr (g * e)`.

## Statements

- `succ_isPullback`: the defining square of `succObj` is a pullback of presheaves.
- `succPr_image`: every projection of `succ ha P` has the same image in `X`, namely
  `h(succSnd) ≫ P.toBase`.
- `succ_isSeparated`: if `V.hom` and `P.obj.hom` are separated, so is `(succ ha P).obj.hom`.
- `succ_etale`: if `a` is étale (`IsEtale a`) and every projection of `P` is étale, then
  every projection of `succ ha.1 P` is étale.
- `fin_properties`: if `a` is étale and `V.hom` is separated, then `(fin ha.1 n).obj.hom` is
  separated and all projections of `fin ha.1 n` are étale.
- `exists_of_finite`: if `a` is étale, `V.hom` is separated, and `ι` is finite and
  nonempty, then there is `P : ChartFibrePower a ι` with `P.obj.hom` separated and every
  `(P.pr i).left` étale.
- `act_pr : P.act g ≫ P.pr e = P.pr (g * e)`, `act_one : P.act 1 = 𝟙 P.obj`, and
  `act_mul : P.act g ≫ P.act h = P.act (g * h)`.

## Proofs

- The universal property of `succ` comes from the represented pullback API:
  `Functor.relativelyRepresentable.lift'`, `lift'_fst`, `lift'_snd` and `hom_ext'`. Its
  compatibility condition follows from `P.lift_pr` and the hypothesis on the family.
- `succ_isSeparated`: the map `m = (succSnd, succFst)` from `succObj` to
  `P.obj ×_S V` is a monomorphism. Two morphisms `g₁, g₂` into `succObj` that agree after
  `m` become morphisms over `S`, and `hom_ext` for `succ ha P` identifies them. Then
  `succObj.hom = m ≫ pullback.fst ≫ P.obj.hom` is a monomorphism followed by a base change
  of the separated `V.hom` and the separated `P.obj.hom`. Monomorphisms are separated, and
  Mathlib's instances close the goal.
- `succ_etale`: `succSnd` is a base change of the étale `a`, so it is étale
  (`IsEtale.projection` applied to `succ_isPullback`). The new factor `succFst` is a base
  change of `P.toBase`, which is étale by `isEtale_map` and `IsEtale.comp`. The old factors
  are composites of étale morphisms.
- `fin_properties` is by induction on `n`. `exists_of_finite` picks
  `ι ≃ Fin (n + 1)`, using that `ι` is nonempty, and reindexes `fin ha.1 n`.
- The action laws follow from `hom_ext` and `lift_pr`; `act_mul` also uses associativity of
  multiplication in `G`.
