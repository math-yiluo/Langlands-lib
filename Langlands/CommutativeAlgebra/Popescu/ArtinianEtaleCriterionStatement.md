# Unramified flat maps of Artinian local rings are essentially smooth

`Langlands.CommutativeAlgebra.Popescu.ArtinianEtaleCriterionStatement` (universe `u`). Let
`P → D` be a ring map between Artinian local rings (`[Algebra P D]`). Assume:

- the map is local (`IsLocalHom (algebraMap P D)`);
- `D` is essentially of finite type over `P` (`Algebra.EssFiniteType P D`);
- `D` is flat over `P` (`Module.Flat P D`);
- `𝔪_P D = 𝔪_D`;
- the residue field extension `κ_D/κ_P` is separable (`Algebra.IsSeparable`; in particular
  algebraic).

Then `D` is essentially smooth over `P` (`EssentiallySmooth P D`, from
`Langlands.CommutativeAlgebra.Popescu.EssentiallySmooth`: `D` is a localization of a smooth
`P`-algebra).

## Source

This is the last step of the proof of Stacks Project, Smoothing Ring Maps, Lemma 16.11.2 (Tag 07FH;
source `stacks-artin-axioms-approximation-2026-11-06`, smoothing.pdf, printed p. 27), applied with
`P = k[y]_𝔭/𝔭ⁿk[y]_𝔭` and `D = A`. The text reads: "By construction the residue field extension
`F/κ(𝔭)` is finitely generated and `Ω_{F/κ(𝔭)} = 0`. Hence it is finite separable… Thus
`k[y₁, …, y_m]_𝔭/𝔭ⁿ → A` is finite by Algebra, Lemma 54.4. Finally, we conclude that it is étale by
Algebra, Lemma 143.7. Since an étale ring map is certainly essentially smooth we win."

The cited results are Algebra, Lemma 10.54.4 (Tag 07DT) and Lemma 10.143.7 (Tag 00U6), both in the
registered snapshots `stacks-geometric-regularity-07E5-07E6-2026-11-14`.

- Tag 07DT: for `S` Artinian local, `R → S` is finite (resp. essentially of finite type) if and
  only if `R → S/𝔪_S` is.
- Tag 00U6: if `R → S` is of finite presentation, `R_𝔭 → S_𝔮` is flat, `𝔭S_𝔮` is the maximal ideal
  of `S_𝔮` and `κ(𝔮)/κ(𝔭)` is finite separable, then `R → S` is étale at `𝔮`.

## Encoding

- The hypotheses are stated for Artinian local rings, the only case used. "Essentially étale" is
  weakened to the Library notion `EssentiallySmooth`, which is what Lemma 16.11.2 requires.
- The residue algebra `ResidueField P → ResidueField D` is Mathlib's instance for local
  homomorphisms. The source's "finite separable" is encoded as `Algebra.IsSeparable`. Finiteness of
  `κ_D/κ_P` follows: `κ_D` is algebraic and essentially of finite type over `κ_P`, hence finite.
- All types are in one universe `u`.
