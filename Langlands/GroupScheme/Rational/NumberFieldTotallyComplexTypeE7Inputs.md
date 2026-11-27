# Torus orders and cyclic covers for simply connected groups of type E₇

Module: `Langlands.GroupScheme.Rational.NumberFieldTotallyComplexTypeE7Inputs`.

The module states two propositions about simply connected absolutely almost-simple
groups of type `E_7`. It contains no theorem; neither statement is proved here.

## Common hypotheses

Both statements quantify over a field (`K`, in `Type u`) and an affine, locally
finite-type group scheme `G` over `Spec K` with actual Tits index data
`d : TitsIndexData G` and a bijection `e : d.Vertex ≃ Fin 7` carrying every actual Cartan
pairing `d.cartan a b` to the Mathlib entry `CartanMatrix.E 7 (e a) (e b)`. They assume
`IsSimplyConnected G` and `IsAbsolutelyAlmostSimple G`. These are the hypotheses on `G`
of the published `NumberFieldTotallyComplexTypeE7Statement` (module
`Rational/NumberFieldTypeE7HasseInputs`), apart from quasi-splitness, which only the second
statement assumes.

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
  closure. The Dynkin diagram of `E_7` has no nontrivial symmetry, so for these groups
  quasi-split is the same as split.
- `NumberField.IsTotallyComplex K` is Mathlib's predicate that every infinite place of `K`
  is complex.

## The statements

### `TypeE7MaximalTorusCocycleOrderStatement`

```lean
∀ (K : Type u) [Field K] [CharZero K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7),
  IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
  (∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b)) →
  ∀ (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G), IsMaximalTorus i →
  ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (τ : Cocycle T.toGrp (GaloisCocycle.cover K L)),
    ∃ a b : ℕ, (τ.map (CommGroupScheme.groupHom ((2 ^ a * 3 ^ b : ℕ) • 𝟙 T))).IsTrivial
```

For a field `K` of characteristic zero and a maximal `K`-torus `T` of a simply connected
group of type `E_7`, every element of `H¹(L/K, T(L))`, for every finite Galois `L/K`, is
killed by a number of the form `2^a 3^b`. Since `H¹(L/K, T(L))` embeds in `H¹(K, T)` by
inflation, this is the `E_7` case of Platonov–Rapinchuk, Proposition 6.21, restricted to
classes represented on a finite Galois cover.

The statement fails for non-maximal tori. Take `G` split simply connected of type `E_7`
over a field `K` of characteristic zero that has a cyclic extension `F/K` of degree `5`. A
connected chain of four simple roots spans a subsystem of type `A_4`; the corresponding
derived Levi subgroup of `G` is split simply connected, that is, isomorphic to `SL_5`. The
regular representation of `F` on the `5`-dimensional `K`-vector space `F` embeds the
norm-one torus `T' = R^{(1)}_{F/K}(𝔾_m)` in `SL_5`, hence in `G`, and
`H¹(F/K, T'(F)) ≅ K^×/N(F^×)`. This group can contain elements of order `5`: for
`K = ℚ` and `F` the real subfield of degree `5` of `ℚ(ζ_{11})`, the Frobenius class of `2`
generates `Gal(F/ℚ)`, so `2` is inert in `F` and the `2`-adic valuation of every norm from
`F^×` is divisible by `5`, while `2^5 = N_{F/ℚ}(2)`. Hence the class of `2` has order `5`
in `ℚ^×/N(F^×)`. The corresponding class of `H¹(F/ℚ, T'(F))` is represented by a cocycle
of `T'` on the cover `Spec F → Spec ℚ`, and no power of that cocycle with exponent
`2^a 3^b` is trivial.

### `NumberFieldTotallyComplexTypeE7CyclicStatement`

```lean
∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7),
  IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
  (∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b)) →
  IsQuasiSplit G →
  ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    (Module.finrank K L = 2 ∨ Module.finrank K L = 3) →
    ∀ ξ : Cocycle G (GaloisCocycle.cover K L), ξ.IsTrivial
```

Over a totally complex number field `K`, a quasi-split simply connected group `G` of type
`E_7` satisfies `H¹(L/K, G(L)) = 1` for every Galois extension `L/K` of degree `2` or `3`
(such an extension is cyclic). This is the `E_7` case of Platonov–Rapinchuk,
Theorem 6.29, for `p = 2, 3` over a totally imaginary number field. It is the special case
of `NumberFieldTotallyComplexTypeE7Statement` in which the cover has degree `2` or `3`.

## Sources

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (1994), registered as
`platonov-rapinchuk-1994-algebraic-groups-number-theory`; printed page `p` is PDF page
`p + 10`. Section 6.8, "Groups of type `E_6`, `E_7`, `E_8` (preliminaries)":

- Proposition 6.21 (printed pp. 375–377): for a group of type `E_6` or `E_7` over `K` and a
  maximal `K`-torus `T`, the order of every element of `H¹(K, T)` has the form `2^a 3^b`.
  The proof restricts to Sylow `5`- and `7`-subgroups of the Galois group of a splitting
  field, acting on the root system through the Weyl group `W(E_7)` of order
  `2^10 · 3^4 · 5 · 7`. The `5`-part is treated with a Galois-stable subsystem of type
  `D_5` and Lemma 6.30 (printed pp. 375–376: for a `K`-group `H` of type `¹D_n` or `²D_n`
  with `n ≥ 4` and a maximal `K`-torus `S` of `H`, `H¹(K, S)` is a `2`-group). The
  subgroup of type `D_5` generated by the root groups of that subsystem is of type `¹D_5`
  or `²D_5` over the fixed field of a Sylow `5`-subgroup, since the automorphism group of
  the `D_5` diagram has order `2`, and its intersection with `T` is a maximal torus of it.
  The `7`-part is treated with a Galois-stable subsystem of type `A_7`.
  As recorded in `notes/errata/platonov-rapinchuk-1994-e7-a7-subgroup.md`, the subgroup
  generated by the root groups of the `A_7` subsystem is `SL_8/μ_2` and not `SL_8` as the
  text says; the `7`-primary computation is unaffected, since the coroot lattice of `A_7`
  has index `2` in that of `E_7`.
- Theorem 6.29 (printed p. 378): for a simply connected quasi-split simple group `G_0` of
  type `E_6`, `E_7` or `E_8` over a local or totally imaginary number field `K` and a
  cyclic extension `L/K` of degree `p`, with `p = 2, 3` for types `E_6` and `E_7`,
  `H¹(L/K, G_0) = 1`. The cases `p = 2, 3` are proved on printed pp. 378–382 by
  induction on the rank: Proposition 6.22 (isotropic twists are trivial, using the
  centralizer of a split torus and lower-rank split simply connected groups), Lemma 6.31
  (groups split by a quadratic extension are isotropic over totally imaginary fields, via
  three-dimensional Hermitian forms) and Lemma 6.32 (the cubic case), with Theorem 6.26
  (printed pp. 352–356) for the isotropy of lower-rank groups of type other than `A`.

The Lean encodings are derived from these results as follows. A maximal `K`-torus is
expressed by `IsMaximalTorus`, the order of a class by a trivial power of a representing
cocycle, and `H¹(L/K, -)` by cocycles on the finite Galois cover `Spec L → Spec K`.

## Role in the argument for totally complex fields

On printed pp. 377–378 Platonov and Rapinchuk derive `H¹(K, G_0) = 1` for a quasi-split
simply connected group `G_0` of type `E_6` or `E_7` over a totally imaginary number field
`K` as follows. By Proposition 6.19 (Steinberg) every class comes from `H¹(K, T)` for a
maximal `K`-torus `T`. In the Library, the theorem `quasiSplitCocycleTorusReduction` gives,
after a finite Galois refinement and a twist, a cocycle with values in a closed `K`-torus;
the theorem `exists_maximalTorus_extension_of_finiteType` embeds that torus in a maximal
`K`-torus, and pushing the torus cocycle forward along this inclusion gives a class to which
Proposition 6.21 applies. By Proposition 6.21 that class has order `2^a 3^b`, and by
Proposition 6.20 and Lemma 6.20 it dies over a finite subextension `L` of the cyclotomic
`{2, 3}`-extension of `K`. The extension `L/K` is abelian and its degree has no prime factor
other than `2` and `3`, hence it is a tower of cyclic steps of degree `2` and `3`, and the
class is trivial by iterated application of Theorem 6.29 along the tower. The two
statements of this module are the inputs Proposition 6.21 and Theorem 6.29 of this
argument for type `E_7`.
