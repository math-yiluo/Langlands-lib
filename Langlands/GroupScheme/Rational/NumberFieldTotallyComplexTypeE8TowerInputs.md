# Torus orders and cyclic covers for simply connected groups of type E₈

Module: `Langlands.GroupScheme.Rational.NumberFieldTotallyComplexTypeE8TowerInputs`.

The module states three propositions about simply connected absolutely almost-simple
groups of type `E_8`. It contains no theorem; none of the statements is proved here.

## Common hypotheses

All three statements quantify over a field (`K`, in `Type u`) and an affine, locally
finite-type group scheme `G` over `Spec K` with actual Tits index data
`d : TitsIndexData G` and a bijection `e : d.Vertex ≃ Fin 8` carrying every actual Cartan
pairing `d.cartan a b` to the Mathlib entry `CartanMatrix.E 8 (e a) (e b)`. They assume
`IsSimplyConnected G` and `IsAbsolutelyAlmostSimple G`. These are the hypotheses on `G` of
`NumberFieldTotallyComplexQuasiSplitTypeE8Statement` (module
`Rational/NumberFieldTypeE8TotallyComplexInputs`), apart from quasi-splitness, which only
the second and third statements assume.

Other notation:

- `Cocycle T (GaloisCocycle.cover K L)` is a natural cocycle of `T` on the cover
  `Spec L → Spec K` (module `TorsorCocycle`), and `IsTrivial` says that it is the
  coboundary of one point over `Spec L`. For a finite Galois extension `L/K` this is
  triviality of the class of the corresponding Galois cocycle in `H¹(L/K, T(L))`
  (`GaloisCocycle.isTrivial_iff`).
- `IsMaximalTorus i` (module `Torus/Maximal`) says that `i : T ⟶ G` is a closed subgroup,
  `T` is a torus, and `i` does not factor through a strictly larger closed torus of `G`
  defined over `K`. For the connected reductive groups considered here this is the usual
  notion of a maximal `K`-torus, that is, a `K`-torus that is a maximal torus over an
  algebraic closure: every `K`-torus `S` lies in a maximal torus of `G` defined over `K`,
  namely a maximal `K`-torus of the connected reductive centralizer of `S`.
- The Hom groups of `CommGroupScheme` are written additively, the sum of two homomorphisms
  being their pointwise product. Hence `n • 𝟙 T` is the endomorphism `t ↦ t^n` of `T`, and
  `τ.map (CommGroupScheme.groupHom (n • 𝟙 T))` is the cocycle whose values are the `n`-th
  powers of those of `τ`; its triviality says that the class of `τ` is killed by `n`.
- `IsQuasiSplit G` (module `Reductive/QuasiSplit`) says that `G` is connected reductive and
  contains a Borel subgroup defined over the field that remains Borel over the algebraic
  closure. The Dynkin diagram of `E_8` has no nontrivial symmetry, so for these groups
  quasi-split is the same as split.
- `NumberField.IsTotallyComplex K` is Mathlib's predicate that every infinite place of `K`
  is complex.

## The statements

### `TypeE8MaximalTorusCocycleOrderStatement`

```lean
∀ (K : Type u) [Field K] [CharZero K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 8),
  IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
  (∀ a b, d.cartan a b = CartanMatrix.E 8 (e a) (e b)) →
  ∀ (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G), IsMaximalTorus i →
  ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (τ : Cocycle T.toGrp (GaloisCocycle.cover K L)),
    ∃ a b c : ℕ,
      (τ.map (CommGroupScheme.groupHom ((2 ^ a * 3 ^ b * 5 ^ c : ℕ) • 𝟙 T))).IsTrivial
```

For a field `K` of characteristic zero and a maximal `K`-torus `T` of a simply connected
group of type `E_8`, every element of `H¹(L/K, T(L))`, for every finite Galois `L/K`, is
killed by a number of the form `2^a 3^b 5^c`. Since `H¹(L/K, T(L))` embeds in `H¹(K, T)`
by inflation, this is the `E_8` case of Platonov–Rapinchuk, Proposition 6.21, restricted to
classes represented on a finite Galois cover.

The statement fails for non-maximal tori. Take `G` split simply connected of type `E_8`
over `ℚ`. A connected chain of six simple roots spans a subsystem of type `A_6`; the
corresponding derived Levi subgroup of `G` is split simply connected, that is, isomorphic
to `SL_7`. Let `F` be the subfield of degree `7` of `ℚ(ζ_{29})`, a cyclic extension of `ℚ`.
The regular representation of `F` on the `7`-dimensional `ℚ`-vector space `F` embeds the
norm-one torus `T' = R^{(1)}_{F/ℚ}(𝔾_m)` in `SL_7`, hence in `G`, and
`H¹(F/ℚ, T'(F)) ≅ ℚ^×/N(F^×)`. The Frobenius class of `2` generates `Gal(F/ℚ)`, which is
the quotient of `(ℤ/29)^×` by its subgroup of order `4`, because `2^4 = 16 ≢ 1 (mod 29)`; so
`2` is inert in `F` and the `2`-adic valuation of every norm from `F^×` is divisible by `7`,
while `2^7 = N_{F/ℚ}(2)`. Hence the class of `2` has order `7` in `ℚ^×/N(F^×)`. The
corresponding class of `H¹(F/ℚ, T'(F))` is represented by a cocycle of `T'` on the cover
`Spec F → Spec ℚ`, and no power of that cocycle with exponent `2^a 3^b 5^c` is trivial.

### `NumberFieldTotallyComplexTypeE8QuadraticCubicStatement`

```lean
∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 8),
  IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
  (∀ a b, d.cartan a b = CartanMatrix.E 8 (e a) (e b)) →
  IsQuasiSplit G →
  ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    (Module.finrank K L = 2 ∨ Module.finrank K L = 3) →
    ∀ ξ : Cocycle G (GaloisCocycle.cover K L), ξ.IsTrivial
```

Over a totally complex number field `K`, a quasi-split simply connected group `G` of type
`E_8` satisfies `H¹(L/K, G(L)) = 1` for every Galois extension `L/K` of degree `2` or `3`
(such an extension is cyclic). This is the `E_8` case of Platonov–Rapinchuk,
Theorem 6.29, for `p = 2, 3` over a totally imaginary number field. It is the special case
of `NumberFieldTotallyComplexQuasiSplitTypeE8Statement` in which the cover has degree `2`
or `3`.

### `NumberFieldTotallyComplexTypeE8QuinticStatement`

```lean
∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 8),
  IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
  (∀ a b, d.cartan a b = CartanMatrix.E 8 (e a) (e b)) →
  IsQuasiSplit G →
  ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    Module.finrank K L = 5 →
    ∀ ξ : Cocycle G (GaloisCocycle.cover K L), ξ.IsTrivial
```

Over a totally complex number field `K`, a quasi-split simply connected group `G` of type
`E_8` satisfies `H¹(L/K, G(L)) = 1` for every Galois extension `L/K` of degree `5` (such an
extension is cyclic). This is the case `p = 5` of Platonov–Rapinchuk, Theorem 6.29, over a
totally imaginary number field. It is the special case of
`NumberFieldTotallyComplexQuasiSplitTypeE8Statement` in which the cover has degree `5`.

The cases `p = 2, 3` and `p = 5` are stated separately because their proofs in the source
are different, and the proof of the case `p = 5` uses the cases `p = 2, 3`.

## Sources

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (1994), registered as
`platonov-rapinchuk-1994-algebraic-groups-number-theory`; printed page `p` is PDF page
`p + 10`. Section 6.8, "Groups of type `E_6`, `E_7`, `E_8` (preliminaries)":

- Proposition 6.21 (printed pp. 375–377): for a group of type `E_8` over `K` and a maximal
  `K`-torus `T`, the order of every element of `H¹(K, T)` has the form `2^a 3^b 5^c`. The
  Galois group of a splitting field of `T` acts on the root system through the Weyl group
  `W(E_8)` of order `2^14 · 3^5 · 5^2 · 7`, which bounds the orders by `2^a 3^b 5^c 7^d`.
  The `7`-part is removed (printed p. 377) by the argument given on printed p. 376 for the
  `5`-part in types `E_6` and `E_7`: the root system of type `E_8` contains a subsystem of
  type `D_7`, whose Weyl group has the same `7`-part `7`, and Lemma 6.30 (printed
  pp. 375–376: for a `K`-group `H` of type `¹D_n` or `²D_n` with `n ≥ 4` and a maximal
  `K`-torus `S` of `H`, `H¹(K, S)` is a `2`-group) applies to the corresponding subgroup.
- Theorem 6.29 (printed p. 378): for a simply connected quasi-split simple group `G_0` of
  type `E_8` over a local or totally imaginary number field `K` and a cyclic extension `L/K`
  of degree `p ∈ {2, 3, 5}`, `H¹(L/K, G_0) = 1`. The cases `p = 2, 3` are proved on printed
  pp. 378–382 by induction on the rank: Proposition 6.22 (isotropic twists are trivial,
  using the centralizer of a split torus and lower-rank split simply connected groups),
  Lemma 6.31 (groups split by a quadratic extension are isotropic over totally imaginary
  fields, via three-dimensional Hermitian forms) and Lemma 6.32 (the cubic case). The case
  `p = 5` ("Groups of type `E_8`", printed pp. 386–396) passes to the maximal solvable
  `{2, 3}`-extension `E` of `K`, where it uses the cases `p = 2, 3` along a tower of cyclic
  extensions of degree `2` and `3`; over `E` it uses Chernousov's Theorem 6.30 (printed
  pp. 387–393, with Propositions 6.23 and 6.24: an anisotropic group of type `E_8` over `E`
  split by a cyclic quintic extension has a proper semisimple `E`-subgroup isotropic over
  that extension) and Proposition 6.25 (printed pp. 394–396).

The Lean encodings are derived from these results as follows. A maximal `K`-torus is
expressed by `IsMaximalTorus`, the order of a class by a trivial power of a representing
cocycle, and `H¹(L/K, -)` by cocycles on the finite Galois cover `Spec L → Spec K`.

## Role in the argument for totally complex fields

On printed pp. 377–378 Platonov and Rapinchuk derive `H¹(K, G_0) = 1` for a quasi-split
simply connected group `G_0` of type `E_8` over a totally imaginary number field `K` as
follows. By Proposition 6.19 (Steinberg) every class comes from `H¹(K, T)` for a maximal
`K`-torus `T`. By Proposition 6.21 that class has order `2^a 3^b 5^c`, and by
Proposition 6.20 and Lemma 6.20 it dies over a finite subextension `L` of the cyclotomic
`{2, 3, 5}`-extension of `K`. The extension `L/K` is abelian and its degree has no prime
factor other than `2`, `3` and `5`, hence it is a tower of cyclic steps of degree `2`, `3`
and `5`, and the class is trivial by iterated application of Theorem 6.29 along the tower.
The three statements of this module are the inputs Proposition 6.21 and Theorem 6.29
(split into `p ∈ {2, 3}` and `p = 5`) of this argument for type `E_8`.
