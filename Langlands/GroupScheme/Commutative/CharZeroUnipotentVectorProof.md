# Commutative unipotent groups in characteristic zero are vector groups: proof

The theorem `Langlands.GroupScheme.charZeroCommutativeUnipotentVectorGroup`
proves the unchanged published proposition
`Langlands.GroupScheme.CharZeroCommutativeUnipotentVectorGroupStatement.{u}`
(module [`CharZeroUnipotentVectorStatement`](CharZeroUnipotentVectorStatement.md)) in every
universe `u`. Its type is exactly that proposition; no hypothesis is added.

## Statement proved

Let `k : Type u` be a field with `CharZero k`, and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy `LocallyOfFiniteType G.X.hom`,
`IsAffineHom G.X.hom` and `IsCommMonObj G.X`. If `IsUnipotent G`, then
`RelativeRoot.IsVectorGroup G`: for some `n` there are natural group equivalences between
the points of `G` over every test scheme `T` and `n`-tuples of global functions on `T`.
This is Milne, *Algebraic Groups* (2017), Corollary 16.15, second sentence, as recorded in
the statement Markdown.

## The implemented proof

The proof assembles four published Library results. It does not follow Milne's
exponential-map route (14.32–14.33); it goes through smoothness, connectedness and a split
series instead.

1. **Smoothness.** `affineCartierSmooth` (module `Langlands.GroupScheme.AffineCartierSmoothProof`,
   statement `AffineCartierSmoothStatement`) says that every affine group scheme locally of
   finite type over a field of characteristic zero is smooth. Applied to `G` with the
   hypotheses `IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`, it gives
   `Smooth G.X.hom` (Cartier's theorem).
2. **Connectedness.** `charZeroUnipotentConnected` (module
   `Langlands.GroupScheme.Unipotent.CharZeroConnectedProof`) says that an affine group scheme
   locally of finite type over a field of characteristic zero that is unipotent has a
   connected underlying space. Applied to `G` and `IsUnipotent G`, it gives
   `ConnectedSpace G.X.left`.
3. **Split series.** A field of characteristic zero is perfect (Mathlib instance
   `PerfectField.ofCharZero`). `perfectFieldUnipotentSplit` (module
   `Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof`, statement
   `PerfectFieldUnipotentSplitStatement`, Milne 16.24) says that a smooth connected affine
   unipotent group over a perfect field is split unipotent. With steps 1 and 2 it gives
   `RelativeRoot.IsSplitUnipotent G`, that is, `RelativeRoot.HasSplitSeries n G` for some
   `n`: a finite normal series with represented fppf quotients isomorphic to `𝔾ₐ`.
4. **Commutative split groups in characteristic zero.**
   `RelativeRoot.HasSplitSeries.isVectorGroupOfDimension_of_commutative` (module
   `Langlands.GroupScheme.Rational.CommutativeVectorClassificationProof`) says that over a
   field of characteristic zero, a commutative affine group scheme (`IsAffineHom`,
   `IsCommMonObj`) with a split series of length `n` satisfies
   `RelativeRoot.IsVectorGroupOfDimension G n`. Applied to the series of step 3, together
   with `IsAffineHom G.X.hom` and `IsCommMonObj G.X`, it gives the vector-group
   coordinates of dimension `n`.

The conclusion `RelativeRoot.IsVectorGroup G` is `∃ n, RelativeRoot.IsVectorGroupOfDimension G n`,
so the pair `⟨n, _⟩` from step 4 proves it.

## Scope

The proof uses only the hypotheses of the statement. Smoothness and connectedness, which the
source's Corollary 16.15 does not assume, are derived in steps 1 and 2 rather than imposed.
The trivial group is covered by a series of length `0` (dimension `0`).
