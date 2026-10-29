# Simultaneous local approximation of a module map (Stacks 046Y, first proof step)

`Langlands.Algebra.localCompatibleMapApproximationExistence` proves the published proposition
`Langlands.Algebra.LocalCompatibleMapApproximationExistenceStatement.{uR, uS, uM, uN}`. This is the
first paragraph of the proof of Stacks Project Lemma 10.128.4 (tag 046Y). Let `R → S` be an
essentially finitely presented local homomorphism of local rings, and let `f : M → N` be an
`S`-linear map of finitely presented `S`-modules. Then one directed system of local rings
approximating `R → S` carries approximation systems of `M` and `N`, together with compatible
component maps that induce `f`.

## Proof

The proof applies two published theorems:

- `localCompatibleMapApproximationExistence_of_localAlgebraApproximationExistence`, from
  `Langlands.Algebra.LocalCompatibleMapApproximation`, which proves the target from the 00QV
  existence statement `LocalAlgebraApproximationExistenceStatement.{uR, max uS uM uN}`;
- `Langlands.Algebra.localAlgebraApproximationExistence`, from `Langlands.Algebra.LocalAlgebraApproximationExistenceProof`, which proves
  `LocalAlgebraApproximationExistenceStatement` (Stacks 00QV, Lemma 10.127.11) for every pair of
  universes. Here it is used at `{uR, max uS uM uN}`.

The reduction does the actual work. It applies 00QV to `R → ULift.{max uM uN} S`, so the index
and the ring carriers land in `Type (max uR uS uM uN)`, and transports the system back to `S`
along `ULift.algEquiv`. It then descends presentation matrices `A`, `A'` of `M` and `N`, and a
lift `(B, C)` of `f` with `A' B = C A`, to a single index. Past an index where `A' B - C A`
becomes zero, the cokernel systems of `A` and `A'` carry the induced compatible maps, and the
colimit comparison maps are bijective. Finally the systems are transported to `M` and `N` along
the presentation equivalences. The documentation of
`Langlands.Algebra.LocalCompatibleMapApproximation` gives the details.

No new mathematics is introduced here.
