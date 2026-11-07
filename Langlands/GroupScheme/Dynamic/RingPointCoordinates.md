# Points of a corepresented group over algebras, and over base changes

Namespace `Langlands.GroupScheme.Corepresented.RingCoordinates`. Here R is a commutative ring,
given as a `CommRingCat`, and G = Spec B is a corepresented affine group over
Spec R (`Corepresented.groupScheme F e`). The module describes the points of G
with values in R-algebras. For an R-algebra K, it also describes the points of
the base change G_K with values in K-algebras.

## Provenance

These are internal helper results for the local-ring Isomorphism Theorem task
(ab10ec3c). They extend to an arbitrary base ring R and an arbitrary R-algebra K
the field-level constructions of the Library module
`Langlands.GroupScheme.Dynamic.BaseChangeCoordinates`: `testOver`,
`testOverHom`, `testOverInv`, `ofAlgHom` and `basePoint`, together with the
lemmas `testOverHom_comp_unitPoint` and `basePoint_conj` of
`Dynamic.BaseChangeComparison`. In the Library these assume that k and Ω are
fields. The definitions and proofs here follow those modules, with the field
hypotheses removed. The ring-general helpers use a separate namespace so
the field-level interfaces remain available under their existing names.

## Points over algebras

- `pointRing_comp`: the classifying ring map of y ≫ x is that of x followed by
  the ring map of y.
- `specOver R D` is Spec D over Spec R. `algHom x : B →ₐ[R] D` is the
  classifying algebra map of a point x over Spec D. `ofAlgHom F e φ` is the
  point given by an algebra map φ. `algHom_ofAlgHom` and `ofAlgHom_algHom` show
  that these are inverse, and `algHomEquiv` packages them as an equivalence.
- `specMapOver g` is the morphism Spec D' → Spec D over Spec R given by an
  R-algebra map g : D → D'. `algHom_comp`: restricting a point along it
  composes the classifying map with g.

## Points of a base change

Let K be an R-algebra, `baseMap R K : Spec K → Spec R`, and D a K-algebra with
the induced R-algebra structure (`IsScalarTower R K D`).

- `testOver K D` is Spec D over Spec K. `testOverHom R K D` and
  `testOverInv R K D` are the mutually inverse identity morphisms between
  Spec D over Spec R and Spec D over Spec K pushed forward to Spec R
  (`testOverHom_comp_testOverInv`, `testOverInv_comp_testOverHom`).
- `baseAlgHom z : B →ₐ[R] D` is the classifying map of the underlying point of a
  point z of G_K over Spec D: z is sent through the pullback point equivalence
  `GroupScheme.baseChangePointsEquiv`, and then composed with `testOverHom`.
  `baseAlgHom_bijective`: every R-algebra map B → D arises from exactly one
  such z.
- `specMapK g` is the morphism Spec D' → Spec D over Spec K given by a
  K-algebra map g. `baseAlgHom_comp`: restricting z along it composes the
  classifying map with g. `specMapOver_comp_testOverHom` is the corresponding
  statement for the underlying points.
- `testOverHom_comp_unitPoint`: the unit point u of 𝔾ₘ over Spec D, taken over K
  and transported to R, is the unit point u over R.
- `testOverHom_comp_conj`: for any group G over Spec R and cocharacter ν,
  conjugating a point of G_K by the base-changed cocharacter at the unit u
  corresponds to conjugating its underlying point by ν(u). The proof combines
  the multiplicativity of the pullback point equivalence with the Library's
  `Dynamic.baseChangePointsEquiv_baseChangeCocharacter`.

All results use only the standard axioms.
