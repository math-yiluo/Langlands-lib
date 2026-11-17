# Existence of the KP §9.8 filtration of `Z(F)`

Lean module: `Langlands.Geometry.Building.CentralizerFiltrationExistenceProof`.

The theorem `Langlands.Geometry.Building.centralizerFiltrationExistence` proves the published
proposition `Langlands.Geometry.Building.CentralizerFiltrationExistenceStatement` (module
`CentralizerFiltrationExistenceStatement`) at arbitrary universe `u`. Its type is exactly
`CentralizerFiltrationExistenceStatement.{u}`. It adds no hypothesis, assumes no unproved
proposition and uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

This is Kaletha–Prasad §9.8 and Lemma 9.8.1. Let `F` be a nonarchimedean local field, in either
characteristic. Let `G` be a group scheme over `Spec F` with `[IsAffineHom G.X.hom]`, and let
`P : ParahoricBuildingData G` satisfy `P.SatisfiesApartmentAxioms` (V 7 and AS 2–AS 5). Then
there is a filtration `Zf : P.CentralizerFiltration` of `Z(F)`, where `Z = Z_G(S)`, with
`Zf.SatisfiesFiltrationAxioms` and `Zf.IsOpenFiltration`. The structure and the two predicates
are in module `KPMoyPrasadFiltration`. The fields of the structure say that the subgroups
`Z(F)_r` (`r : ℝ≥0`) are decreasing and separated, with `Z(F)_0 = P.centralizerZero`.
`SatisfiesFiltrationAxioms` says that the filtration is commutator friendly (KP
Definition 7.2.1) and stable under `N(F)`, that `[Z(F)_r, Z(F)_s] ⊆ Z(F)_{r+s}`, and that
`Z(F)_r` moves `U_{a,x,s}` into the block `U_{a,x,r+s} U_{2a,x,r+s}`. `IsOpenFiltration` says
that each `Z(F)_r` is open in `Z(F)`.

## The construction

This module builds no new filtration. It uses the filtration of the published theorem
`centralizerFiltrationDoubleRootExistence` (module `KPDoubleRootFiltrationExistence`). That
theorem proves the stronger statement `CentralizerFiltrationDoubleRootExistenceStatement`
(module `KPMoyPrasadDoubleRootStatement`). The stronger statement has the same hypotheses and
gives a filtration with one more property, `Zf.IsDoubleRootCommutatorFriendly`. This is the
sharper `Z`-component bound `Z(F)_{2r}` when `u ∈ U_{2a}(F)` or `u' ∈ U_{-2a}(F)`, which comes
from KP's `SU_3` computation in the proof of Proposition 7.1.1.

That filtration is the one of KP §9.8: `Z(F)_r = Z(K)_{x₀,r} ∩ Z(F)`, where `K` is the maximal
unramified extension of `F` and `x₀` is an apartment point. In Lean it is
`IsRationalMoyPrasadFamily.centralizerFiltration hQ x₀` (module `KPRationalMoyPrasadFamily`),
the preimage under `Z(F) → G(F)` of `G(K)_{e x₀, r} ∩ G(F)`. Here `B`, `hZ` and `e` come from the
unramified comparison over `K`, and `hQ` comes from the `K`-level Moy–Prasad properties. The
Markdown of `KPDoubleRootFiltrationExistence` describes how these pieces are assembled.

## The proof

1. `centralizerFiltrationExistence_of_doubleRoot` shows that
   `CentralizerFiltrationDoubleRootExistenceStatement.{u}` implies
   `CentralizerFiltrationExistenceStatement.{u}`. Introduce `F`, its instances, `G`, its
   instance, `P` and `hP`. The hypothesis applied to `F G P hP` gives `Zf` with
   `SatisfiesFiltrationAxioms`, `IsOpenFiltration` and `IsDoubleRootCommutatorFriendly`. Keep
   the same `Zf` with the first two properties and drop the third.
2. `centralizerFiltrationExistence` applies this lemma to the published theorem
   `centralizerFiltrationDoubleRootExistence : CentralizerFiltrationDoubleRootExistenceStatement.{u}`.

## Library results used

- `Langlands.Geometry.Building.CentralizerFiltrationExistenceStatement` (target statement).
- `Langlands.Geometry.Building.CentralizerFiltrationDoubleRootExistenceStatement`
  (module `KPMoyPrasadDoubleRootStatement`).
- `Langlands.Geometry.Building.centralizerFiltrationDoubleRootExistence`
  (module `KPDoubleRootFiltrationExistence`, Task 5647).

## Credits

The double-root existence theorem and the published inputs it assembles name their authors in
their own Markdown. This includes the `K`-level Moy–Prasad properties (Task 6191) and the
local torus filtration (Task 6199), which reuse helper modules first written for this task.
