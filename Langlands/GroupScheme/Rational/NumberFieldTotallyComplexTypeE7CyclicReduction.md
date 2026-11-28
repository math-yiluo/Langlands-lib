# Reduction of quadratic and cubic vanishing for totally complex type E₇

Module: `Langlands.GroupScheme.Rational.NumberFieldTotallyComplexTypeE7CyclicReduction`.

The module states two propositions,
`NumberFieldTotallyComplexTypeE7CubicTwistIsotropyStatement` and
`NumberFieldTotallyComplexTypeE7SplitLineCentralizerVanishingStatement`, which are not
proved here. Its theorem `numberFieldTotallyComplexTypeE7Cyclic_of_inputs` proves that
these two propositions, together with `NumberFieldTypeE7QuadraticHasseStatement` (module
`Rational/NumberFieldTypeE7HasseInputs`) and `IsotropicTwistSplitLineReductionStatement`
(module `Rational/IsotropicTwistSplitLineReduction`), imply
`NumberFieldTotallyComplexTypeE7CyclicStatement` (module
`Rational/NumberFieldTotallyComplexTypeE7Inputs`).

## Common hypotheses

Both statements quantify over a totally complex number field `K` (in `Type u`) and an
affine, locally finite-type group scheme `G` over `Spec K` with actual Tits index data
`d : TitsIndexData G` and a bijection `e : d.Vertex ≃ Fin 7` carrying every actual Cartan
pairing `d.cartan a b` to the Mathlib entry `CartanMatrix.E 7 (e a) (e b)`. They assume
`IsSimplyConnected G`, `IsAbsolutelyAlmostSimple G` and `IsQuasiSplit G`. These are the
hypotheses on `K` and `G` of `NumberFieldTotallyComplexTypeE7CyclicStatement`. The Dynkin
diagram of `E_7` has no nontrivial symmetry, so such a `G` is split.

The notation for cocycles, twists, local identifications and their discrepancies, closed
copies of `𝔾_m` and centralizers of split lines is explained in the Markdown page of
`Rational/IsotropicTwistSplitLineReduction`.

## The statements

### `NumberFieldTotallyComplexTypeE7CubicTwistIsotropyStatement`

```lean
∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7),
  IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
  (∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b)) →
  IsQuasiSplit G →
  ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    Module.finrank K L = 3 →
    ∀ (ξ : Cocycle G (GaloisCocycle.cover K L))
      (H : GroupScheme (Spec (CommRingCat.of K)))
      (φ : LocalGroupIso G H (GaloisCocycle.cover K L)),
      IsAffineHom H.X.hom → φ.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ →
      ∃ μ : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ H, IsClosedSubgroup μ
```

For a Galois extension `L/K` of degree `3` and a cocycle `ξ` of `G` on `Spec L → Spec K`,
every twist `H` of `G` by `ξ` acting by conjugation contains a closed copy of `𝔾_m`; that
is, `H` is `K`-isotropic. The group `H` is a simply connected group of type `E_7` over `K`
that becomes isomorphic to the split group `G` over `L`, so it is split over the cyclic
cubic extension `L`.

This is the cubic step of Platonov–Rapinchuk's analysis of type `E_7` on printed p. 382.
Lemma 6.32 (printed pp. 380–381) shows that a simply connected group of type `E_7` split
over a cyclic cubic extension is `K`-isotropic or contains a proper semisimple
`K`-subgroup of a type other than a product `A_{l_1} × ⋯ × A_{l_t}`. The proof takes the
maximal parabolic `L`-subgroup `P` whose Levi subgroup has type `E_6`, so that
`dim P = 106`, and the `K`-defined intersection `C = P ∩ σ(P) ∩ σ²(P)` for a generator `σ`
of `Gal(L/K)`, which has dimension at least `133 − 3 · 27 = 52`. If the group is
anisotropic, `C` is reductive, and a dimension count excludes that all simple factors of
its derived group have type `A`. By Theorem 6.26 (printed pp. 352–356) and the vanishing
of `H¹` for simply connected quasi-split groups of lower rank over totally imaginary
fields, a semisimple `K`-group of lower rank and of type other than a product of type `A`
factors is `K`-isotropic. Hence the subgroup, and with it the group, is `K`-isotropic.

### `NumberFieldTotallyComplexTypeE7SplitLineCentralizerVanishingStatement`

```lean
∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7),
  IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
  (∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b)) →
  IsQuasiSplit G →
  ∀ (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ G), IsClosedSubgroup ν →
  ∀ (C : GroupScheme (Spec (CommRingCat.of K))) (j : C ⟶ G),
    IsClosedSubgroup j → Smooth C.X.hom → (torusCentralizer ν).IsRepresentedBy j →
    ∀ (M : Type u) [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
      (τ : Cocycle C (GaloisCocycle.cover K M)), τ.IsTrivial
```

For a closed copy `ν` of `𝔾_m` in `G` and a smooth closed subgroup `j : C ⟶ G` representing
the centralizer of `ν` (`SubgroupFunctor.IsRepresentedBy`: `j` is a monomorphism whose
points are exactly the points of `G` centralizing `ν`), every cocycle of `C` on a finite
Galois field cover `Spec M → Spec K` is trivial, that is, `H¹(M/K, C(M)) = 1`.

The statement is the vanishing step at the end of the proof of Platonov–Rapinchuk,
Proposition 6.22 (printed p. 378), for the centralizer of a split line instead of a
maximal `K`-split torus. Since `G` is split, the line lies in a split maximal torus `T`
of `G`, and `C` is the split connected reductive group generated by `T` and the root
groups of the roots vanishing on `ν`. Its derived group `D = [C, C]` is a split simply
connected semisimple group whose Dynkin diagram is a proper subdiagram of `E_7`, so its
simple factors have types `A_n` (`n ≤ 6`), `D_4`, `D_5`, `D_6` or `E_6`. The quotient
`C/D` is a quotient of `T`, hence a split torus, and `H¹(K, C/D) = 1` by Hilbert's
Theorem 90. The exact sequence `H¹(K, D) → H¹(K, C) → H¹(K, C/D)` and the vanishing of
`H¹(K, D)` for split simply connected groups of these types over a totally imaginary
number field give `H¹(K, C) = 1`. Inflation `H¹(M/K, C(M)) → H¹(K, C)` is injective,
which gives the statement on every finite Galois cover.

## Proof of the implication

`numberFieldTotallyComplexTypeE7Cyclic_of_inputs` treats the two degrees separately.

- Degree `2`. `IsQuasiSplit.baseChange_of_algebraicExtension` shows that `G` remains
  quasi-split over `L`, and `Cocycle.locallyTrivial_of_totallyComplex` (module
  `Rational/NumberFieldTypeE6LeviReduction`) shows that every cocycle of the simply
  connected group `G` over the totally complex field `K` is trivial at every completion.
  `NumberFieldTypeE7QuadraticHasseStatement` then gives triviality.
- Degree `3`. `finiteGaloisTwistExistence` constructs a twist `H` of `G` by the cocycle
  `ξ` acting by conjugation, with an identification `φ` whose discrepancy is `ξ`. The cubic
  isotropy statement gives a closed copy `μ` of `𝔾_m` in `H`, and
  `IsotropicTwistSplitLineReductionStatement` gives a finite Galois refinement `M`, a
  point `g` of `G` over `M` and a closed copy `ν` of `𝔾_m` in `G` such that the refined
  cocycle twisted by `g` takes values in the centralizer of `ν`.
  `torusCentralizer_hasSmoothClosedRepresentative` (module `Torus/CentralizerSmooth`)
  provides a smooth closed subgroup `j : C ⟶ G` representing that centralizer, so the
  twisted cocycle lifts to a cocycle of `C` (`Cocycle.lift`). The centralizer vanishing
  statement trivializes the lift; `Cocycle.IsTrivial.of_lift`,
  `Cocycle.IsTrivial.of_twist` and `GaloisCocycle.isTrivial_of_refine` carry triviality
  back to `ξ`.

The conclusion has the exact type of `NumberFieldTotallyComplexTypeE7CyclicStatement`.

## Source

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (1994), registered as
`platonov-rapinchuk-1994-algebraic-groups-number-theory`; printed page `p` is PDF page
`p + 10`. Section 6.8: Theorem 6.29 and Proposition 6.22 (printed p. 378), Lemma 6.32
(printed pp. 380–381) and the conclusion for type `E_7` (printed p. 382); Section 6.6,
Theorem 6.26 (printed pp. 352–356). Platonov and Rapinchuk prove Theorem 6.29 for
`p = 2` through Lemma 6.31 and Proposition 6.22; here the quadratic case is instead taken
from the quadratic Hasse principle for type `E_7`, combined with the triviality of all
local classes of simply connected groups over totally complex fields.
