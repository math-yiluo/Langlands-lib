# Functor transformations of actual cokernel-complex comparisons

This internal extension of `CokernelComplex.LaxMap` proves that its constructed
residual, term and chain maps respect compatible natural transformations of
the original functor. It also constructs transport of the degree-zero and
chain maps along a natural isomorphism of that functor. Its intended use is
lifting an actual lax spatial comparison to the iterated-cokernel complex.

Let `A : Type u` and `B : Type u'` have morphisms in independent universes
`v` and `v'`. Let `T : A ⥤ A` and `T' : B ⥤ B` have coaugmentations
`η : 𝟭 A ⟶ T` and `η' : 𝟭 B ⟶ T'`. Let `Φ, Ψ : A ⥤ B` and let

```text
e  : Φ ⋙ T' ⟶ T ⋙ Φ,
e' : Ψ ⋙ T' ⟶ T ⋙ Ψ
```

satisfy the coaugmentation equations `he` and `he'` from `LaxMap`:
`η'(Φ(M)) ≫ e(M) = Φ.map(η(M))` and the corresponding equation for `Ψ`.
A natural transformation `α : Φ ⟶ Ψ` is compatible when

```text
T'.map(α(M)) ≫ e'(M) = e(M) ≫ α(T(M)).
```

This is the argument `hα`; it is an equation of actual degree-zero morphisms.
It supplies neither a higher comparison nor an inverse for `α`.

## Transformation squares

All declarations are in `Langlands.Cohomology.CokernelComplex.Lax`.
`termMapOf_transformation` first proves the analogous square for a pair of
residual comparisons `ρ` and `ρ'`. It applies `T'` to the residual square
`hρ`, then uses `hα` at the residual object. This lemma only requires the
two categories and the displayed functors and maps.

For the remaining residual, term and chain constructions, `A` and `B` are
abelian and both `Φ` and `Ψ` preserve zero morphisms. The endofunctors
`T` and `T'` need not be additive. Write `R_n`, `R'_n` for the residual
functors, `K_n`, `K'_n` for the term functors, and `r_n^Φ`, `t_n^Φ` for the
constructed `residualMap e he n` and `termMap e he n`, with the corresponding
notation for `Ψ`.

`residualMap_transformation` and `termMap_transformation` prove

```text
R'_n.map(α(M)) ≫ r_n^Ψ(M) = r_n^Φ(M) ≫ α(R_n(M)),
K'_n.map(α(M)) ≫ t_n^Ψ(M) = t_n^Φ(M) ≫ α(K_n(M)).
```

The residual proof is induction on `n`, generalizing the input object. The
zero case is the identity equation. At the successor, the actual source
cokernel projection is an epimorphism in the functor category and remains
an epimorphism at each object. Precomposition with it reduces the goal to
the preceding term square. The quotient equations from `LaxMap` and the
naturality of `α` at the target quotient complete that step. This uses no
preservation of cokernels by `Φ` or `Ψ`.

`complexMap_transformation` proves the actual chain square

```text
(functor T' η').map(α(M)) ≫ complexMap e' he' M
  = complexMap e he M ≫ α_complex(complex T η M),
```

where `α_complex` is Mathlib's `NatTrans.mapHomologicalComplex α
(ComplexShape.up ℕ)`. The proof is extensionality on degrees followed by
the term square. The transformation `α` is not required to be invertible.

## Actual isomorphism transport

For `β : Φ ≅ Ψ`, `transport e β` constructs

```text
Ψ ⋙ T' ⟶ T ⋙ Ψ
```

by whiskering `β.inv`, then `e`, then `β.hom`. `transport_app` records
its component:

```text
T'.map(β.inv(M)) ≫ e(M) ≫ β.hom(T(M)).
```

`transport_comm` proves its coaugmentation equation using naturality of
`η'` and `β.hom`, the given equation `he`, and inverse cancellation.
`transport_hom_comm` proves its degree-zero transformation square with
`β.hom`, using functoriality and forward/inverse cancellation. These
transport declarations do not require abelian categories or preservation
of zero morphisms.

Under the abelian and zero-preservation hypotheses,
`transportComplexMap e he β M` constructs the actual chain map by applying
`Lax.complexMap` to this transported comparison and its proved
coaugmentation equation. `transportComplexMap_comm` applies the general
chain transformation square to `β.hom`. Thus it describes the relation
between the transported map and the original one without assuming such
a relation as input.

The module imports the existing actual iterated-cokernel construction and
Mathlib's pointwise epimorphism result for functor categories. This is
internal provenance: its proofs use functoriality, naturality, the existing
quotient equations and uniqueness of cokernel descent. It asserts no new
external source result, exactness, acyclicity, quasi-isomorphism, derived
identification, or geometric specialization.
