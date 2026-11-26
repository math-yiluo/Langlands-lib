# Three inputs of Harder's argument for the Hasse kernel in type E₇

Module: `Langlands.GroupScheme.Rational.NumberFieldTypeE7HasseInputs`.

The module states three propositions about simply connected absolutely
almost-simple groups of type `E_7`. In Platonov and Rapinchuk's treatment of the
Hasse principle for type `E_7` over a number field, these are the three facts the
argument combines. The module contains no theorem; none of the three statements is
proved here.

## Common hypotheses

Each statement quantifies over a number field (`K` or `F`, in `Type u`) and an
affine, locally finite-type group scheme `G` over its spectrum, with actual Tits
index data `d : TitsIndexData G` and a bijection `e : d.Vertex ≃ Fin 7` carrying
every actual Cartan pairing `d.cartan a b` to the Mathlib entry
`CartanMatrix.E 7 (e a) (e b)`. It assumes `IsSimplyConnected G` and
`IsAbsolutelyAlmostSimple G`. These are exactly the hypotheses on `G` of the
published `NumberFieldTypeE7HasseStatement` (module
`Rational/NumberFieldHasseKernelTypeReduction`).

Other notation:

- `IsQuasiSplit H` (module `Reductive/QuasiSplit`) says that the connected
  reductive field group `H` contains a Borel subgroup defined over the field that
  remains Borel over the algebraic closure. The Dynkin diagram of `E_7` has no
  nontrivial symmetry, so for the groups considered here quasi-split is the same
  as split.
- `(GroupScheme.baseChange (algebraBaseMap F L)).obj G` is the base change `G_L` of
  `G` to a field extension `L` of `F`.
- `GaloisCocycle.cover K L` is `Spec L` as a scheme over `Spec K`, and
  `ξ : Cocycle G (GaloisCocycle.cover K L)` is a natural cocycle of `G` on this
  cover (module `TorsorCocycle`). `ξ.IsTrivial` says that `ξ` is the coboundary
  of one point of `G` over `Spec L`; for a finite Galois extension this is
  triviality of the class of the corresponding Galois cocycle
  (`GaloisCocycle.isTrivial_iff`).
- `ξ.LocallyTrivial` (module `Rational/NumberFieldHasseKernelReduction`) says that
  at every place `v` of `F`, archimedean ones included, the pullback of `ξ` to the
  cover `Spec (F_v ⊗_F L) → Spec F_v` is trivial.
- `NumberField.IsTotallyComplex K` is Mathlib's predicate that every infinite
  place of `K` is complex.

## The statements

### `NumberFieldTotallyComplexTypeE7Statement`

```lean
∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7),
  IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
  (∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b)) →
  IsQuasiSplit G →
  ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (ξ : Cocycle G (GaloisCocycle.cover K L)), ξ.IsTrivial
```

Over a totally complex number field `K`, a quasi-split simply connected group of
type `E_7` has trivial first Galois cohomology: every cocycle on every finite
Galois field cover is trivial. No local hypothesis on `ξ` is imposed.

### `NumberFieldTypeE7QuadraticSplittingFieldStatement`

```lean
∀ (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7),
  IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
  (∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b)) →
  ∃ E : IntermediateField F (SeparableClosure F),
    Module.finrank F E = 2 ∧ NumberField.IsTotallyComplex E ∧
      IsQuasiSplit ((GroupScheme.baseChange (algebraBaseMap F E)).obj G)
```

Every such group over a number field `F` becomes quasi-split over some totally
complex quadratic extension `E` of `F`. The extension is taken inside Mathlib's
separable closure `SeparableClosure F`; any quadratic extension of `F` is
`F`-isomorphic to such an intermediate field.

### `NumberFieldTypeE7QuadraticHasseStatement`

```lean
∀ (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7),
  IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
  (∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b)) →
  ∀ (L : Type u) [Field L] [Algebra F L], Module.finrank F L = 2 →
    IsQuasiSplit ((GroupScheme.baseChange (algebraBaseMap F L)).obj G) →
    ∀ ξ : Cocycle G (GaloisCocycle.cover F L), ξ.LocallyTrivial → ξ.IsTrivial
```

Let `L/F` be a quadratic field extension over which `G` becomes quasi-split. A
cocycle of `G` on the cover `Spec L → Spec F` that is trivial at every place is
trivial. In terms of Galois cohomology: the kernel of
`H¹(L/F, G(L)) → ∏_v H¹(F_v, G)` is trivial. The extension `L` is not required to
be totally complex. Since `F` has characteristic zero, `L/F` is Galois.

## Sources and derivation

The book cited is V. Platonov and A. Rapinchuk, *Algebraic Groups and Number
Theory* (1994), registered as
`platonov-rapinchuk-1994-algebraic-groups-number-theory`. Its PDF page is the
printed page plus 10 (printed p. 386 is PDF p. 396).

- **Totally complex vanishing.** Platonov–Rapinchuk §6.8 prove that
  `H¹(K, G₀) = 1` for a simply connected quasi-split group `G₀` of type `E_6` or
  `E_7` over a local field or a totally imaginary number field: Proposition 6.21
  and its Corollary (printed pp. 375–377), Theorem 6.29 (printed p. 378) and its
  proof for cyclic steps of degree 2 and 3 (printed pp. 378–382, Proposition 6.22
  and Lemmas 6.31, 6.32); the text on printed p. 378 reads "the triviality of
  `H¹(K,G₀)` over a local or totally imaginary number field is obtained by
  iterative application of" Theorem 6.29. The same vanishing follows from
  J. S. Milne, *Algebraic Groups* (2017), registered as
  `milne-2017-algebraic-groups`, Theorem 25.65, printed p. 563
  (`H¹(k, G) ≃ ∏_{v real} H¹(k_v, G)` for simply connected `G`), when `k` has no
  real place. The Lean statement is the case of quasi-split groups of type `E_7`,
  with `H¹` represented by cocycles on finite Galois field covers.
- **Quadratic splitting field.** Platonov–Rapinchuk, Proposition 6.16(B), printed
  p. 335: any `K`-group of type `E_7` is split over a suitable quadratic extension
  `L/K`, "which we may assume to be totally imaginary in the number field case".
  The proposition is stated under the assumption that `H¹(P, G₀)` is trivial for
  every totally imaginary extension `P` of `K`; the text after it (printed p. 335)
  notes that it becomes unconditional once Theorems 6.4 and 6.6 are proved. The
  Lean statement asks for quasi-splitness, which is implied by splitness.
- **Quadratic Hasse kernel.** This is a derived special case of the Hasse principle
  for simply connected groups, Platonov–Rapinchuk Theorem 6.6, printed p. 286, and
  Milne, Theorem 25.64(a), printed p. 562: a class of `H¹(F, G)` that is split by
  `L` and locally trivial is trivial. The restriction to quadratic covers over
  which `G` is quasi-split records the situation of the argument for type `E_7` on
  printed p. 386.

## How the statements are used

On printed p. 386, Platonov and Rapinchuk argue as follows for a group `G` of type
`E_7` over a number field `K` and a class `ξ` in the kernel of
`H¹(K, G) → ∏_v H¹(K_v, G)`. By Proposition 6.16, `G` splits over a totally
imaginary quadratic extension `L`. Since `H¹(L, G) = 1`, the class `ξ` lies in
`H¹(L/K, G)`, and the quadratic argument then shows that `ξ` is trivial. The three
statements of this module are these three steps: the splitting field, the
vanishing over `L`, and the kernel on the quadratic cover. The passage from a
cocycle on an arbitrary finite Galois cover to one on the quadratic cover is the
inflation–restriction sequence for nonabelian `H¹`.

For the quadratic kernel, Platonov and Rapinchuk use Lemma 6.17 (printed p. 329),
which gives a Borel subgroup `B` defined over `L` such that `T = B ∩ σ(B)` is a
maximal `K`-torus, where `σ` generates `Gal(L/K)`, and Lemma 6.28 (printed
p. 369), which moves `ξ` into a cocycle of `T` that is trivial at the archimedean
places. Since `E_7` has no diagram symmetry, `σ` acts on the character group of
`T` as `-1`. On printed p. 386 the book then appeals to a simply connected
subgroup of type `A_7` containing `T`. The subgroup of a simply connected group of
type `E_7` generated by the root groups of a closed subsystem of type `A_7`
contains `T`, whose cocharacter group is the coroot lattice of `E_7`; this lattice
contains the coroot lattice of `A_7` with index 2 (the determinants of the two
Cartan matrices are 2 and 8). That subgroup is therefore isomorphic to `SL_8/μ_2`
over the algebraic closure and is not simply connected. An argument that avoids it
writes `T` as the product of the images of the simple coroots, each a
one-dimensional anisotropic torus split by `L`, and uses the rank-one subgroups
generated by the root groups of `±α` for the simple roots `α`, as in the
componentwise argument of Platonov–Rapinchuk, Proposition 6.25 (printed p. 394).
