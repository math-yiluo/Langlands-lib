# Ideles that are norms from a Kummer extension of prime degree

Author: Worker 269.

This module, in namespace `Langlands.Global.Arithmetic.KummerNormLift`, gives a sufficient
condition for an idele of a number field `K` to be the norm of an idele of a Kummer extension
`L = K(β)` of prime degree `p`, `β ^ p = a ∈ K`. It combines the local norm facts of
[KummerRadical](KummerRadical.md) with the lifting criterion `mem_range_ideleNorm_of_local` of
[IdeleNormLift](../AdelicFunctoriality/IdeleNormLift.md). It changes none of the imported
definitions.

Notation: `ideleCoordinate v y` is the unit of `K_v = v.adicCompletion K` at a finite place `v`
(module `Langlands.ClassField.Global.IdeleCohomology`), and `ideleInfiniteCoordinate w y` the
unit of `K_w = w.Completion` at an infinite place `w` (module
`Langlands.ClassField.Global.IdeleArchimedean`). `localPowers v p` is the subgroup of `p`-th
powers in `K_vˣ` (module `Langlands.ClassField.Global.LocalPowerIndex`), and
`infiniteUnitPowers w p` the subgroup of `p`-th powers in `K_wˣ` (module
`Langlands.ClassField.Global.LocalUnitPowers`).

## The local conditions

For `p : ℕ`, `a ∈ K` and an idele `y` of `K`:

- `FiniteRadicalCondition p a y v`, at a finite place `v`: either `a` is the `p`-th power of
  some `c ∈ K_v`, or `ideleCoordinate v y ∈ localPowers v p`.
- `InfiniteRadicalCondition p a y w`, at an infinite place `w`: either `a` is the `p`-th power
  of some `c ∈ K_w`, or `ideleInfiniteCoordinate w y ∈ infiniteUnitPowers w p`.

These two definitions only name the disjunctions. The main theorem below states the same
disjunctions inline.

## Local norms

Let `K` contain a primitive `p`-th root of unity `ζ` for a prime `p` (`IsPrimitiveRoot ζ p`),
and let `L/K` be Galois with `[L : K] = p`, `L = K(β)` (`Algebra.adjoin K {β} = ⊤`) and
`β ^ p = algebraMap K L a`.

- `exists_localNorm_eq_of_finiteRadicalCondition y v q h`: for a finite place `q` of `L` over
  `v` and `h : FiniteRadicalCondition p a y v`, there is a unit `c` of `L_q` with
  `FiniteExtension.localNorm v q c = ideleCoordinate v y`. If `a` is a `p`-th power in `K_v`,
  then `[L_q : K_v] = 1` (`finrank_adicCompletion_eq_one`), and every unit of `K_v` is a local
  norm (`exists_localNorm_eq_of_finrank_eq_one`). If `ideleCoordinate v y = u ^ p`, then it is
  a local norm by `exists_localNorm_eq_pow`.
- `exists_infinite_localNorm_eq_of_infiniteRadicalCondition y w u h`: the same for an infinite
  place `u` of `L` over `w` and `h : InfiniteRadicalCondition p a y w`, with
  `InfiniteExtension.localNorm w u`. If `a` is a `p`-th power in `K_w`, then `u` is unramified
  (`isUnramified_of_pow_eq`) and every unit is a local norm
  (`exists_infinite_localNorm_eq_of_isUnramified`). Otherwise the coordinate is a `p`-th power,
  and `exists_infinite_localNorm_eq_pow` applies. This lemma does not need `[L : K] = p`,
  `L/K` Galois or `L` a number field.

## The global criterion

`mem_range_ideleNorm_of_radical hζ hdeg hβ hβa S hpS haS y hyS hyfin hyinf`: in the situation
above, let `S` be a finite set of finite places of `K` such that for every finite `v ∉ S`

- `p` is a unit of `O_v = v.adicCompletionIntegers K` (`hpS`), and
- `a` has valuation `1` in `K_v` (`haS`).

Let `y` be an idele of `K` such that

- `ideleCoordinate v y` has valuation `1` for every finite `v ∉ S` (`hyS`),
- at every `v ∈ S`, `a` is a `p`-th power in `K_v` or `ideleCoordinate v y ∈ localPowers v p`
  (`hyfin`), and
- at every infinite place `w`, `a` is a `p`-th power in `K_w` or
  `ideleInfiniteCoordinate w y ∈ infiniteUnitPowers w p` (`hyinf`).

Then `y` lies in the range of `ideleNorm : IdeleGroup (𝓞 L) L →* IdeleGroup (𝓞 K) K` (module
`Langlands.Global.AdelicFunctoriality.Norm`).

Proof. Choose the places `placeAbove L v` (module
`Langlands.Global.AdelicFunctoriality.LocalDegree`) and `infinitePlaceAbove L w` (module
`Langlands.Global.AdelicFunctoriality.IdeleClassNormIndexReduction`) above every place of `K`. At `v ∈ S` and
at infinite places, the two local lemmas above give units whose local norms are the
coordinates of `y`. At `v ∉ S`, `exists_localNorm_eq_of_valued_eq_one` of KummerRadical gives a
unit `c` of valuation `1` whose local norm is `ideleCoordinate v y`. So `c` and `c⁻¹` are
integral at every `v` outside the finite set `S`. This is the almost-everywhere integrality
hypothesis of `mem_range_ideleNorm_of_local`, which then gives the preimage.

## Provenance

Emil Artin and John Tate, *Class Field Theory*, AMS Chelsea edition (2009), registered original
`artin-tate-2009-class-field-theory`, Chapter VI §3, proof of the first statement of Lemma 2
(printed p. 25, PDF p. 34). There, `a = b^n · c`. The idele `c` has component `1` on `S_j`, and
it is a local norm on `S_i`, where the prime splits completely in `K_j`, and outside `S`,
where it is a unit at an unramified prime. "Thus `c_p` is local norm at all primes, and hence
`c ∈ N_j J_j`." `mem_range_ideleNorm_of_radical` is a Lean form of this step for one radical of
prime degree. The hypotheses are local:

- at a place where `a` is a local `p`-th power, the place splits completely;
- at a place where the coordinate is a local `p`-th power, it is a local norm. The book reaches
  `b^n` through its Lemma 1, but the Lean proof only uses the local fact that `p`-th powers
  are local norms;
- outside `S`, units are local norms.

The packaging of these hypotheses and the choice of one place above each place of `K` are
internal. The exact shape of the main theorem was requested by Worker 226 for the Kummer case
of the prime-degree second inequality.
