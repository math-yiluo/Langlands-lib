# Groups of type E₈ over totally complex number fields: two inputs

Module: `Langlands.GroupScheme.Rational.NumberFieldTypeE8TotallyComplexInputs`.

The module states two propositions about simply connected absolutely almost-simple
groups of type `E₈`. It proves that together they give
`NumberFieldTotallyComplexTypeE8Statement` (module
`Langlands.GroupScheme.Rational.NumberFieldTypeE8HasseReduction`): over a totally complex
number field such a group is quasi-split and its cocycles on finite Galois field covers
are trivial. The first proposition is structural and holds over every field; the second
is the arithmetic vanishing theorem for the quasi-split groups. Neither proposition is
proved in this module.

## Common hypotheses

Each statement, and every group it quantifies over, uses the hypotheses on `G` of
`NumberFieldTotallyComplexTypeE8Statement`: a group scheme
`G : GroupScheme (Spec (CommRingCat.of K))` over a field `K : Type u` with
`IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`, actual Tits index data
`d : TitsIndexData G`, and a bijection `e : d.Vertex ≃ Fin 8` with
`d.cartan a b = CartanMatrix.E 8 (e a) (e b)` for all simple vertices `a, b`; and
`IsSimplyConnected G` and `IsAbsolutelyAlmostSimple G`. Below, "a group of type `E₈`
over `K`" means a group with these data and properties.

Other notation:

- `IsQuasiSplit H` (module `Langlands.GroupScheme.Reductive.QuasiSplit`): `H` is
  connected reductive and contains a Borel subgroup defined over the field that remains
  Borel over the algebraic closure. The `E₈` Dynkin diagram has no nontrivial symmetry,
  so a quasi-split group of type `E₈` is split; this comparison is not formalized here.
- `GaloisCocycle.cover K L` is `Spec L` as a scheme over `Spec K`, and
  `ξ : Cocycle H (GaloisCocycle.cover K L)` is a natural cocycle of `H` on this cover
  (module `Langlands.GroupScheme.TorsorCocycle`). `ξ.IsTrivial` says that `ξ` is the
  coboundary of one point of `H` over `Spec L`. For a finite Galois extension `L/K` this
  is triviality of the class of the corresponding Galois cocycle in `H¹(L/K, H(L))`.

## `TypeE8QuasiSplitOfQuasiSplitCohomologyStatement`

```lean
∀ (K : Type u) [Field K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 8),
  IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
  (∀ a b, d.cartan a b = CartanMatrix.E 8 (e a) (e b)) →
  (∀ (H : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom H.X.hom]
    [LocallyOfFiniteType H.X.hom] (d' : TitsIndexData H) (e' : d'.Vertex ≃ Fin 8),
    IsSimplyConnected H → IsAbsolutelyAlmostSimple H →
    (∀ a b, d'.cartan a b = CartanMatrix.E 8 (e' a) (e' b)) →
    IsQuasiSplit H →
    ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      (ξ : Cocycle H (GaloisCocycle.cover K L)), ξ.IsTrivial) →
  IsQuasiSplit G
```

Let `K` be any field and `G` a group of type `E₈` over `K`. Suppose that every
quasi-split group `H` of type `E₈` over `K` has only trivial cocycles on the finite
Galois field covers `Spec L → Spec K` with `L : Type u`. Then `G` is quasi-split. No
hypothesis on the characteristic of `K` or on perfectness is made.

Source: V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (1994),
Proposition 6.16(A) and its proof, printed p. 335. The proposition assumes that
`H¹(K, G₀)` is trivial for the split simply connected group `G₀` (over a local field;
over a number field, for every totally imaginary extension) and concludes that every
`K`-group of type `E₈` is split. Its proof: the Dynkin diagram of `E₈` has no nontrivial
symmetry, so the `K`-forms of `G₀` are classified by `H¹(K, Ḡ₀)` with `Ḡ₀` the adjoint
group, and `Ḡ₀ = G₀` for type `E₈`. The Lean statement is the same argument over an
arbitrary field. It is derived, not a transcription: its hypothesis covers every
quasi-split group of type `E₈` over `K` instead of the split one, and its conclusion is
quasi-splitness instead of splitness.

In terms of the Library, the statement is about the actual inner-form presentation
`QuasiSplitInnerForm G` (module `Langlands.GroupScheme.Rational.QuasiSplitInnerForm`):
`quasiSplitInnerFormExistence` (module
`Langlands.GroupScheme.Rational.QuasiSplitInnerFormExistenceProof`) gives such a
presentation for every connected reductive field group, with a quasi-split model `M`,
its adjoint quotient `M → A` with `A` quasi-split, and an `A`-valued cocycle on a
finite Galois cover. `QuasiSplitInnerForm.isQuasiSplit_of_isTrivial` makes `G`
quasi-split once that cocycle is trivial. To apply the hypothesis to the cocycle, a
proof has to show that `A` is again a group of type `E₈`: the centre of a simply
connected group of type `E₈` is trivial (its character group is the quotient of the
weight lattice by the root lattice, and the `E₈` Cartan matrix has determinant one),
so the adjoint quotient of `M` is an isomorphism, and `M`, which becomes isomorphic to
`G` over a finite Galois extension, is simply connected, absolutely almost-simple and
of type `E₈`.

## `NumberFieldTotallyComplexQuasiSplitTypeE8Statement`

```lean
∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 8),
  IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
  (∀ a b, d.cartan a b = CartanMatrix.E 8 (e a) (e b)) →
  IsQuasiSplit G →
  ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (ξ : Cocycle G (GaloisCocycle.cover K L)), ξ.IsTrivial
```

Over a number field `K` all of whose infinite places are complex
(`NumberField.IsTotallyComplex K`), a quasi-split group of type `E₈` has trivial first
Galois cohomology: every cocycle on every finite Galois field cover is trivial. No local
hypothesis on `ξ` is imposed. The statement has the same form as
`NumberFieldTotallyComplexTypeE7Statement` (module
`Langlands.GroupScheme.Rational.NumberFieldTypeE7HasseInputs`) with `Fin 8` and
`CartanMatrix.E 8` in place of `Fin 7` and `CartanMatrix.E 7`.

Sources:

- Platonov–Rapinchuk (1994), §6.8. The text on printed p. 378 obtains the triviality of
  `H¹(K, G₀)` for a simply connected quasi-split group `G₀` of type `E₈` over a totally
  imaginary number field by iterating Theorem 6.29 (printed p. 378) along a tower of
  cyclic extensions of degrees 2, 3 and 5. The tower exists by Proposition 6.19 (printed
  p. 339: every class comes from a maximal torus), Proposition 6.21 and its Corollary
  (printed pp. 375–377: for type `E₈` the elements of `H¹(K, T)` have order
  `2^a 3^b 5^c`), and Proposition 6.20 and Lemma 6.20 (printed p. 341: cohomological
  dimension of the cyclotomic extension). The cases `p = 2, 3`
  of Theorem 6.29 are proved on printed pp. 378–382 (Proposition 6.22, Lemmas 6.31 and
  6.32). The case `p = 5` for type `E₈` is the paragraph "Groups of type E₈" on printed
  pp. 386–387, with Chernousov's Theorem 6.30 (printed pp. 387–393, Propositions 6.23 and
  6.24) and Proposition 6.25 (printed pp. 394–396). The result is due to V. Chernousov
  (1989).
- J. S. Milne, *Algebraic Groups* (2017), Theorem 25.64(a), printed p. 562: for a simply
  connected semisimple group over a number field the map
  `H¹(k, G) → ∏_v H¹(k_v, G)` is injective; the proof attributes the case `E₈` to
  Chernousov (1989). Over a totally complex field `H¹(k_v, G)` is trivial at the
  nonarchimedean places by Theorem 25.61(a) (printed p. 561) and at the complex places
  because `ℂ` is algebraically closed, so Theorem 25.64(a) gives the unconditional
  vanishing. Theorem 25.65 (printed p. 563), `H¹(k, G) ≃ ∏_{v real} H¹(k_v, G)` for
  simply connected `G` over a global field, implies the same vanishing when `k` has no
  real place.

## The reduction

`numberFieldTotallyComplexTypeE8_of_quasiSplit` proves

```
TypeE8QuasiSplitOfQuasiSplitCohomologyStatement.{u} →
  NumberFieldTotallyComplexQuasiSplitTypeE8Statement.{u} →
    NumberFieldTotallyComplexTypeE8Statement.{u}
```

Fix a totally complex number field `K` and a group `G` of type `E₈` over `K` with its
data `d` and `e`. The vanishing statement over `K` says that every quasi-split group of
type `E₈` over `K` has only trivial cocycles on finite Galois field covers; this is the
hypothesis of the quasi-splitness statement, which then gives `IsQuasiSplit G`. The
vanishing statement applied to `G`, now known to be quasi-split, gives the triviality of
every cocycle of `G` on a finite Galois field cover. The two facts are the two
conjuncts of `NumberFieldTotallyComplexTypeE8Statement`.

## Sources

- V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Academic Press,
  1994 (`platonov-rapinchuk-1994-algebraic-groups-number-theory`). In the registered
  file, printed page `p` is one-based PDF page `p + 10` in Chapter 6. Proposition 6.16 is
  on printed p. 335, Propositions 6.19 and 6.20 on printed pp. 339 and 341; §6.8,
  printed pp. 375–396.
- J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over a
  Field*, Cambridge University Press, 2017 (`milne-2017-algebraic-groups`), Theorems
  25.61, 25.64 and 25.65, printed pp. 561–563.
