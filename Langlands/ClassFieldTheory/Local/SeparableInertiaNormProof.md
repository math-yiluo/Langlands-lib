# Proof of unit norm surjectivity over the separable inertia fixed field

Authors: Worker 1512 and Worker 1248. Worker 1512 wrote the Lean proof and
the Markdown of this module and of the four helper modules
`SeparableInertiaNormHensel`, `SeparableInertiaNormCyclic`,
`SeparableInertiaNormReduction` and `SeparableInertiaNormAmbient` (same
directory, each with its own Markdown). Worker 1248 checked the five pairs
against the Library and the cited sources, corrected the description of
Serre's Proposition 7 below, and submitted them.

## Target

`Langlands.ClassFieldTheory.Local.separableInertiaUnitNormSurjectivity :
SeparableInertiaUnitNormSurjectivity.{u}` proves the unchanged statement
`Langlands.ClassFieldTheory.Local.SeparableInertiaUnitNormSurjectivity` of
`Langlands.ClassFieldTheory.Local.SeparableInertiaNormStatement`. The statement
covers every `F : Type u` with `[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`, of either characteristic. Let
`E : IntermediateField (inertiaFixedField F) (SeparableClosure F)` be finite
over `inertiaFixedField F`, let `L : IntermediateField E (SeparableClosure F)` be
finite over `E`, and let `u : Eˣ` satisfy
`sepClosureValuation F ((u : E) : SeparableClosure F) = 1`. Then there is
`x : Lˣ` with `sepClosureValuation F ((x : L) : SeparableClosure F) = 1` and
`Langlands.LocalClassField.normUnits E L x = u`.

There are no further hypotheses: `L / E` need not be Galois, and nothing
about ramification is assumed. The theorem has the single universe parameter
`u`, and its axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Proof in this module

Write `Ω = SeparableClosure F`, `U = inertiaFixedField F` and
`w = sepClosureValuation F`.

1. `sepClosure_isGalois_inertiaFixedField` is the instance
   `IsGalois U Ω`, from `IsGalois.tower_top_of_isGalois F U Ω`.
2. `ambientHyp_sepClosureValuation F : AmbientHyp (U := U) w` checks the four
   fields of `SeparableInertiaNorm.AmbientHyp`:
   - `inv`: by `sepClosureValuation_apply`, `w x` is the spectral norm
     `spectralNorm F Ω x`, which is invariant under the `F`-automorphism
     `σ.restrictScalars F` (`spectralNorm_eq_of_equiv`). The base norm is the
     Library's `localNormedField F`, as in `SeparableInertiaDefinitions`.
   - `hensel`: the valuation ring of the separably closed field `Ω` is
     Henselian (`sepClosed_henselian (sepClosureIntegers F)` from
     `Langlands.Galois.Local.SeparableHenselian`), so
     `valHensel_of_henselian` applies.
   - `residueRoot`: the restriction of `w` to `U` is, by definition,
     `fixedFieldValuation F`. Its residue field is an algebraic closure of the
     residue field of `F` (`fixedFieldResidueIsAlgClosure F` from
     `Langlands.Galois.Local.SeparableUnramifiedArithmeticProof`). Hence it is
     algebraically closed, and `valResidueRoot_of_isAlgClosed` applies.
   - `unif`: `fixedFieldIntegers F` is a discrete valuation ring
     (`fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)`),
     so `exists_valUniformizer_of_dvr` applies.
3. `separableInertiaUnitNormSurjectivity`: `AmbientHyp.exists_norm_eq` gives
   `x : L` with `w x = 1` and `Algebra.norm E x = u`. Then `x ≠ 0`, and
   `Units.mk0 x _` is the required unit. Since
   `normUnits E L = Units.map (Algebra.norm E)`, `Units.ext` reduces the norm
   equation to `Algebra.norm E x = u`.

## Outline of the whole proof

- `SeparableInertiaNormAmbient`: `L / E` is replaced by the normal closure
  `M` of `L / E` in `Ω`, which is finite Galois over `E`. The ambient
  hypotheses on `Ω / U` give the hypotheses of the reduction theorem for
  `M / E`. A unit norm from `M` to `E` gives a unit norm from `L` to `E` by
  transitivity of norms.
- `SeparableInertiaNormReduction`: for finite Galois `M / E`, a Sylow
  `p`-subgroup reduces the problem to a prime-to-`p` part, where Hensel's
  lemma extracts roots of units, and a tower of Galois extensions of degree `p`.
  Here `p` is a prime such that integers prime to `p` are units.
- `SeparableInertiaNormCyclic`: for Galois `C / B` of prime degree, a direct
  Henselian argument. It uses the norm expansion `N(1 + b x) = ∑ c_k b^k`,
  total ramification derived from the equality of the residue fields (the
  congruence hypothesis `res`) and discreteness,
  openness of unit norms by a strong Hensel lemma, and level-by-level
  approximation through root finding modulo the maximal ideal.
- `SeparableInertiaNormHensel`: the valuation-theoretic hypothesis predicates
  and the strong Hensel lemma.

## Relation to the literature

The statement is the unit form of KP Remark 2.5.11, as applied in KP Lemma
2.5.12 (Kaletha–Prasad, *Bruhat–Tits theory: a new approach*, literature ID
`kaletha-prasad-2023-bruhat-tits-new-approach`, printed pp. 89–90, PDF
pp. 120–121; the citation in Remark 2.5.11 is corrected from Serre V §7 to
V §6 by `kaletha-prasad-2024-corrections`, Section 2.5, PDF p. 24). Serre,
*Local Fields* (`serre-1979-local-fields`), Chapter V, §4, Proposition 7
(printed p. 90, PDF p. 97) proves the multiplicative form `N(L^×) = E^×`.
Its proof first makes the extension Galois. Lemma 7 of §4 then descends it to
a totally ramified Galois extension over a finite subextension of `K_nr`.
Dévissage along the solvable Galois group reduces to the cyclic case of prime
degree, where the corollary to Proposition 6 (§4, printed pp. 88–89, PDF
pp. 95–96) applies. That corollary rests on the study of totally ramified
cyclic extensions of prime degree in §3.

The Lean proof follows the same overall reduction but works directly in the
Henselian, non-complete field `U` inside `Ω`. It never completes `U`, and it
does not use Serre's descent of finite extensions of `K_nr` to finite
extensions of `K` (Lemma 7 of §4). All valuation facts come from the Galois
invariance of the spectral valuation on `Ω` and the published arithmetic of
`U` (Henselian valuation ring of `Ω`, algebraically closed residue field and
discrete valuation ring of `U`).
