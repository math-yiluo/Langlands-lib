# Totally complex quadratic splitting fields in type `E_7`: reduction to the totally complex vanishing

Module: `Langlands.GroupScheme.Rational.NumberFieldTypeE7QuadraticSplittingReduction`,
namespace `Langlands.GroupScheme`.

The module states and proves item (2) of Proposition 6.16 of Platonov and Rapinchuk in type
`E_7` over number fields: the quadratic splitting field statement
`NumberFieldTypeE7QuadraticSplittingFieldStatement` follows from the totally complex
vanishing `NumberFieldTotallyComplexTypeE7Statement`, both of module
`Rational/NumberFieldTypeE7HasseInputs`. This module does not prove the totally
complex vanishing.

## Declarations

### `IsAdjointQuotient.isCentralIsogeny`

```lean
theorem IsAdjointQuotient.isCentralIsogeny {k : Type u} [Field k]
    {G A : GroupScheme (Spec (CommRingCat.of k))} {q : G ⟶ A} (hq : IsAdjointQuotient q)
    (hG : IsSemisimple G) : IsCentralIsogeny q
```

The adjoint quotient of a semisimple field group is a central isogeny. Its kernel is
a scheme-theoretic centre, isomorphic to the finite centre supplied by
`IsSemisimple.hasFiniteCenter` (`isoOfIsRepresentedBy`), so it is finite over the
base; a flat, surjective, quasi-compact homomorphism with finite kernel is finite
(`isFinite_of_finite_kernel`); flatness, surjectivity, local finite presentation and
centrality of the kernel are fields of `IsAdjointQuotient`.

### `NumberFieldTypeE7QuadraticSplittingReductionStatement`

```lean
def NumberFieldTypeE7QuadraticSplittingReductionStatement : Prop :=
  NumberFieldTotallyComplexTypeE7Statement.{u} →
    NumberFieldTypeE7QuadraticSplittingFieldStatement.{u}
```

If every cocycle on a finite Galois field cover of a quasi-split simply connected
absolutely almost-simple group of type `E_7` over a totally complex number field is
trivial, then every simply connected absolutely almost-simple group of type `E_7`
over a number field `F` becomes quasi-split over some intermediate field `E` of
`SeparableClosure F` with `Module.finrank F E = 2` and `E` totally complex. The two
propositions are used exactly as stated in `Rational/NumberFieldTypeE7HasseInputs`;
"type `E_7`" means Tits index data `d` with a numbering `e : d.Vertex ≃ Fin 7`
carrying `d.cartan` to `CartanMatrix.E 7`.

### `numberFieldTypeE7QuadraticSplittingReduction`

```lean
theorem numberFieldTypeE7QuadraticSplittingReduction :
    NumberFieldTypeE7QuadraticSplittingReductionStatement.{u}
```

## Proof

Let `G` over `F` be as in the statement.

1. `quasiSplitInnerFormExistence` gives a presentation `qf : QuasiSplitInnerForm G`:
   a quasi-split model `H = qf.model`, its adjoint quotient `q : H ⟶ qf.adjoint`, a
   finite Galois carrier `L`, local isomorphisms from `H` to `G` over `Spec L`, and an
   adjoint cocycle `qf.cocycle` measuring their discrepancy.
2. `H` is simply connected and absolutely almost-simple
   (`QuasiSplitInnerForm.isSimplyConnected_model`, `isAbsolutelyAlmostSimple_model`),
   has Tits index data `dH` (`titsIndexExistence`), and its Cartan pairings agree with
   those of `d` under a bijection of simple vertices
   (`QuasiSplitInnerForm.exists_vertexEquiv_cartan`), so `dH` is numbered by
   `CartanMatrix.E 7`.
3. The kernel of `q` is the centre of `H`, isomorphic to `μ_2` in the form
   `splitRootsOfUnityProduct F (fun _ => 2)`
   (`TitsIndexData.nonempty_center_iso_of_typeE7`), and `q` is a central isogeny
   (`IsAdjointQuotient.isCentralIsogeny`).
4. After a finite Galois refinement `L'` of `L`, the cocycle has central lift data
   (`IsCentralIsogeny.exists_finiteGalois_refine_galoisLift`); refining the local
   isomorphisms and the cocycle along `Spec L' → Spec L`
   (`LocalGroupIso.HasDiscrepancy.refine`) gives a presentation `qf'` with carrier `L'`.
5. `IsCentralIsogeny.exists_quadratic_isComplex_lift_of_galoisLift` gives a totally
   complex quadratic `E` inside `SeparableClosure F`, a finite Galois `N/E`, and a
   cocycle `ζ` of `H_E` on `Spec N` whose image under `q_E` is the scalar extension of
   the refined cocycle.
6. `H_E` is simply connected, absolutely almost-simple and quasi-split
   (`isSimplyConnected_fieldExtension_iff`,
   `IsAbsolutelyAlmostSimple.baseChange_of_algebraicExtension`,
   `IsQuasiSplit.baseChange_of_algebraicExtension`), and
   `TitsIndexData.separableScalarExtension` carries the `E_7` numbering of `dH` to
   Tits index data of `H_E`. The totally complex vanishing over `E` makes `ζ` trivial,
   hence its image (`Cocycle.IsTrivial.map`), hence the base change of the cocycle of
   `qf'` to `E` on the pulled-back cover
   (`GaloisCocycle.isTrivial_baseChange_of_scalarExtension`).
7. `QuasiSplitInnerForm.isQuasiSplit_baseChange_of_trivial` concludes that `G_E` is
   quasi-split.

## Source

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (Academic Press,
1994), Proposition 6.16, item (2), and its proof, printed p. 335. The proposition assumes
that `H¹(P, G₀)` is trivial for the split simply connected group `G₀` over every
totally imaginary extension `P` of `K`, and concludes that every `K`-group of type
`B_n`, `C_n` or `E_7` is split over a suitable totally imaginary quadratic extension.
`NumberFieldTypeE7QuadraticSplittingReductionStatement` is its type `E_7` case, with
"split" read as "quasi-split" (the same for type `E_7`, whose Dynkin diagram has no
nontrivial symmetry) and the hypothesis taken for all quasi-split simply connected
groups of type `E_7` over totally complex number fields, which is what
`NumberFieldTotallyComplexTypeE7Statement` asserts. The book's proof uses the exact
sequence `H¹(L, G₀) → H¹(L, Ḡ₀) → H²(L, μ_2)` and the identification
`H²(K, μ_2) = Br(K)_2`; the Lean proof follows that route through the Library's
quasi-split inner forms, central lift data and relative unit cohomology.
