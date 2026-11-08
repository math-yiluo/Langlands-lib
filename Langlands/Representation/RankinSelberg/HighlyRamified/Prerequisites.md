# Highly ramified gamma stability from its published prerequisites

Module `Langlands.Representation.RankinSelberg.HighlyRamified.Prerequisites`.

Internal helper for the proof of `Langlands.RankinSelberg.HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, Proposition (4.1), printed page 326). It states the reduction of the
target to three published Library statements. They are the only inputs of the
`HighlyRamified` development that are not yet proved. Everything else it uses is proved,
either in the Library or in the `HighlyRamified` modules.

## Declaration

`highlyRamifiedGammaStability_of_prerequisites hT1 h2 h3 hone` proves
`HighlyRamifiedGammaStabilityStatement.{uF, uV, uW}` from

- `hT1 : Whittaker.WhittakerCompletenessStatement.{uF, U}`: the completeness of Whittaker
  functions, JS85 Lemma (3.2) (printed page 325);
- `h2 : Conductor.EssentialConductorStatement.{uF, U}`: the essential-vector and conductor
  theorems (Jacquet 2012, Theorem 1; JPSS 1981, Théorème (5.1)). Only its third conjunct,
  `EssentialVectorLevelStatement` (an essential vector is fixed by the level-`m` subgroup), is
  used;
- `h3 : UniformRankOneTwistStatement.{uF, U}` and `hone : UniformRankOneTwistStatement.{uF, uV}`:
  the level-uniform rank-one stability, JS85 Proposition (2.2) (printed page 320), at the
  working universe `U` and at the universe `uV` of the target's representation spaces.

Here `U = max uF uV uW`. The adjacent-rank core works with all representation spaces in the
single universe `U`. The universe transport of `HighlyRamified.UniverseTransport` then
returns to the target's independent universes `uV` and `uW`.

## Proof

The proof is one application of `highlyRamifiedGammaStability_of_inputs`
(`HighlyRamified.AdjacentStep`). It passes `hT1`, the third conjunct `h2.2.2`, `h3`, `hone` and
`kirillovShellInput` (`HighlyRamified.KirillovShell`), the proved Kirillov shell input. That
input is an internal substitute for the vector `W'` of JS85 (4.4.16)–(4.4.17), not that
vector; `KirillovShell.md` lists the differences. Each of the three prerequisite statements is the target of a
separate proof task. When their proofs are published, applying this theorem to them gives
the target with no remaining premise.
