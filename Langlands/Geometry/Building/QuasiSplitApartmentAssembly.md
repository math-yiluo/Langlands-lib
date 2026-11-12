# Assembly of the quasi-split apartment, given V 5 at multipliable roots

Author: Worker 4783.

Lean module: `Langlands.Geometry.Building.QuasiSplitApartmentAssembly`.

This internal unit belongs to task 8ffe0456. It proves the task target
`QuasiSplitIntegerApartmentExistenceStatement` from one remaining statement,
`QuasiSplitMultipliableOppositeStatement`: axiom V 5 of the descended family at multipliable
relative roots (type R2). Everything else is proved here or in earlier units:

- the descent of the split apartment class: `SplitChevalleyApartment`,
  `SplitApartmentGaloisFixedPoint`, `QuasiSplitApartmentShifts`;
- V 5 at roots whose double is not a root: `QuasiSplitApartmentOpposite`.

Notation. `k` is a field and `K/k` a field extension. Base changes to `K` are written `S_K`,
`T_K`, `G_K`, `i_K`, `j_K`, `t_K`, and `a_K` is the base change of a character `a` of `S`.
The torus-then-field restriction of an upper family is the published
`torusFieldRestrictedRootFunctionFamily`. The Galois action on root function families is the
published `RootFunctionFamily.galoisAction`.

## The remaining statement

`QuasiSplitMultipliableOppositeStatement` (a `Prop`-valued definition) quantifies over:

- fields `k` and `K`, with `K/k` finite Galois;
- commutative group schemes `S`, `T` over `k`, with `T` affine and locally of finite type;
- an affine smooth group scheme `G` over `k`, locally of finite type, with `G_K` affine and
  smooth;
- `t : S ⟶ T`, `jT : T.toGrp ⟶ G` and a monomorphism `i : S.toGrp ⟶ G`, with `j_K` and
  `groupHom t_K ≫ j_K` monomorphisms;
- `S` split and `T_K` split.

It assumes:

- `G` is connected reductive, `i` is a maximal split torus, and `groupHom t ≫ jT = i`;
- `jT` is a closed subgroup representing the full centralizer `torusCentralizer i`;
- `G_K` is connected reductive, and `j_K` is a maximal torus;
- `hE`: `j_K` has opposite factor pairs;
- `x` is a point of a published `KPApartmentData j_K ω` (a normalizer-stable apartment class
  of `j_K` for some `ω : Kˣ → ℝ`), fixed by every `RootFunctionFamily.galoisAction σ`;
- `groupHom t_K ≫ j_K` is the base change of `i`;
- `P` is a reduced root datum of `j_K` with finitely many roots.

The conclusion: let `a` be a relative root of `i` with `2 • a` also a relative root. Let
`g ≠ 1` be a rational point of `U_a`, and `g', g''` rational points of `U_{-a}` with
`g' g g''` normalizing `i`. Then the torus-then-field restriction `ψ` of `x` along `t_K`
satisfies `ψ (-a) g' + ψ a g = 0`.

The hypotheses are exactly the data that the assembly below provides. The facts used for
roots whose double is not a root follow from them. These facts are: no root of `j_K`
restricts to zero; the roots over each relative root form one Galois orbit; normalizer
points of `i` normalize `jT`; `t` is the largest split subtorus of `T`.

## Helpers

- `mem_normalizerPoints_of_torusCentralizer`: let `jT` be a monomorphism representing the
  full centralizer `torusCentralizer i` of a torus map `i`. Then every rational normalizer
  point of `i` normalizes `jT`. Proof: conjugation by a normalizer point of `i` preserves
  `torusCentralizer i` (published `torusCentralizer_isNormalizedBy_torusNormalizer`), which
  is the range of `jT`. The published `torusNormalizer_le_normalizerPoints` concludes.
- `henselianUnitsOrder v hH K : Kˣ →* Multiplicative ℝ` (definition): the finite values on
  `Kˣ` of the published `FieldTheory.henselianSeparableAddValuation v hH K`, for a henselian
  valuation `v` with values in `ℤ` and a separable extension `K/k`.
  - `henselianUnitsOrder_coe`: it agrees with the valuation on units.
  - `henselianUnitsOrder_algebraMap`: on `kˣ` it is the published `IntegerValuation.order v`.
  - `henselianUnitsOrder_galois`: it is invariant under `Aut_k(K)`.
- `three_le_encard_range_henselianSeparableAddValuation`: if `v` is surjective, the valuation
  on `K` takes at least the three values `⊤`, `0` and `1`.

## The descent

`exists_isOmegaCompatible_of_descent` assumes:

- `QuasiSplitMultipliableOppositeStatement`;
- `K/k` finite Galois, `T` affine and locally of finite type, `G` connected reductive;
- `v` surjective with henselian valuation ring;
- `i = groupHom t ≫ jT` a maximal split torus, and `jT` a closed subgroup representing
  `torusCentralizer i`;
- `T_K` split, `j_K` a maximal torus;
- bijectivity of the published `Cartan.restrictionEvaluation (groupHom t)`.

It concludes that some `D : KPApartmentData i (IntegerValuation.order v)` and some
`C : CentralizerDatum i` satisfy `IntegerValuation.IsOmegaCompatible v D C`.

Proof.

1. `G_K` is connected reductive (`IsConnectedReductive.baseChange_of_algebraicExtension`).
   `j_K` is a split maximal torus, so the published `rootRankOneFactorization` gives opposite
   factor pairs for `j_K`, and also for `i`. `rootDatumExistence` gives a reduced root datum
   `P` of `j_K`.
2. Let `ω` be `henselianUnitsOrder v hH K`. Let `DK` be the published
   `KPApartmentData.ofSplitMaximalTorus` for `j_K`, `ω` and the henselian valuation.
   `KPApartmentData.galoisStable_of_isSplitTorus` makes it Galois stable, and
   `x := KPApartmentData.galoisFixedPoint` is a Galois-fixed point.
3. Structural facts. `groupHom t` is the largest split subtorus of `T`
   (`IsMaximalSplitTorus.of_comp` and `isLargestSplitSubtorus`). Normalizer points of `i`
   normalize `jT` (helper above). No root of `j_K` restricts to zero
   (`root_restrict_ne_zero_of_torusCentralizer`). The roots over each relative root form one
   Galois orbit (`rootOrbit_eq_restrictionFiber_of_torusCentralizer`).
4. `torusFieldOriginalPointShifts_of_galoisFixed` gives the original-point normalizer shifts.
   V 5 holds at every relative root `a`. If `2a` is not a root, this is
   `torusFieldRestrictedRootFunctionFamily_opposite_of_two_not_mem`. Otherwise it is the
   assumed `QuasiSplitMultipliableOppositeStatement`.
5. The published `torusFieldRestrictedValuationOfOriginalPointShifts` gives a valuation `ψ` of
   the root datum of `i`. A unit of `k` of order `1` shows that the order is not identically
   zero. `torusFieldRestrictedRootFunctionFamily_isSplitTorusCompatible`, with
   `henselianUnitsOrder_algebraMap`, makes `ψ` split-torus compatible for
   `IntegerValuation.order v`. `torusFieldOriginalPointShifts_iff` turns the shifts into
   normalizer translations of `ψ`. Then `KPApartmentData.ofNormalizerShifts` gives `D`, the
   orbit of `ψ`.
6. `C` is the centralizer datum `(T.toGrp, jT, groupHom t)`. By
   `IntegerValuation.isOmegaCompatible_iff_of_mem`, it suffices that `ψ` is centralizer
   compatible. That is `torusFieldRestricted_isCentralizerCompatible`.

## The target

`quasiSplitIntegerApartmentExistence_of_multipliableOpposite` proves
`QuasiSplitMultipliableOppositeStatement.{u} → QuasiSplitIntegerApartmentExistenceStatement.{u}`.

Proof. Take the target's data `k`, `v`, `G`, `S`, `i`.

1. `fieldCentralizerRepresentability` gives a closed subgroup `j : Z ⟶ G` representing
   `torusCentralizer i`.
2. `Z` is a torus by `isTorus_of_quasiSplit_torusCentralizer`, using the published
   `quasiSplitTorusCentralizerExistence` and `maximalSplitTorusConjugacy`. So `Z` is a
   commutative group scheme `T`, and `i` factors as `t ≫ jT` through
   `torusCentralizerFactor`.
3. `jT` is its own centralizer, so it is a maximal torus after every base change
   (`isMaximalTorus_baseChange_of_torusCentralizer_eq`). `torusFiniteGaloisSplitting` gives a
   finite Galois splitting field `K` of `T`.
4. `Cartan.restrictionEvaluation_bijective_of_torusCentralizer` gives bijectivity.
   `exists_isOmegaCompatible_of_descent` concludes.

## Provenance

The construction is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §6.1(b)–(c):

- the apartment of a quasi-split group is the Galois-fixed part of the split apartment over a
  splitting field (Construction 6.1.21, printed pp. 207–208, PDF pp. 238–239);
- it is a space of valuations of the relative root datum (Proposition 6.1.19, printed
  pp. 206–207, PDF pp. 237–238);
- it is stable under the normalizer (Lemma 6.1.28, printed p. 210, PDF p. 241);
- torus points act through the valuation homomorphism (Lemma 6.1.26, printed p. 209,
  PDF p. 240).

Here the base field is any field with a surjective `ℤ`-valued henselian valuation. The
statement `QuasiSplitMultipliableOppositeStatement` and the assembly are internal. They are
phrased for the Library's torus-then-field restriction of root function families. All proofs
compose published Library results and the earlier units of this task.

## Scope

- `QuasiSplitMultipliableOppositeStatement` is not proved here. It is the R2 part of
  Proposition 6.1.19 (the `SU₃` computation) for the descended family.
- So this unit reduces the target to that statement, and does not prove the target outright.
