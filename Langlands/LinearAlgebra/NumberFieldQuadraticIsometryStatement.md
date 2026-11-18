# The Hasse principle for isometry of quadratic forms over number fields

Worker 863.

`Langlands.NumberFieldQuadraticIsometryStatement.{u}` is a `Prop`-valued
definition. It states the classical local-to-global theorem for equivalence
of nondegenerate quadratic forms. The module contains no proof of it.

For every number field `F : Type u`, every natural number `n`, and every pair
`q₁ q₂ : QuadraticForm F (Fin n → F)`, assume that both polar bilinear forms
are nondegenerate. If the scalar extensions of `q₁` and `q₂` to each completion
of `F` are isometric, the two original forms are isometric over `F`.
Dimension zero and all positive dimensions are included.

`QuadraticMap.Equivalent` means that there exists an `IsometryEquiv`:
an invertible `F`-linear map carrying one quadratic form to the other.
There is no choice of orientation, determinant, discriminant, signature,
splitting field or matrix representative in the statement.
`q.polarBilin x y` is `q (x + y) - q x - q y`; its `Nondegenerate` predicate
says that a vector orthogonal to every vector is zero. In characteristic zero
this is the usual nondegeneracy of a quadratic form.

The places are the Library's actual `Global.Place F`, including all finite
places and all archimedean places. The scalar extension `q.baseChange F_v`
is Mathlib's quadratic form on `F_v ⊗[F] (Fin n → F)`. It is not a form on a
supplied abstract local model. The definition locally supplies the inverse of
`2 : F`, using the characteristic-zero instance of a number field, so the
tensor-product quadratic form requires no extra hypothesis on `F`.

## Source and correspondence

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Pure and
Applied Mathematics 139, Academic Press, 1994, Section 6.6, printed pp. 347–349.
Source ID `platonov-rapinchuk-1994-algebraic-groups-number-theory`, SHA-256
`c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`.
PDF pages are printed pages plus 10; PDF pp. 357–359 were read.

On printed p. 347 the authors define the weak Hasse principle for forms as
equivalence over the ground field following from equivalence over every
completion, and identify it with injectivity of first cohomology of the
orthogonal group. On printed p. 348 they conclude the Hasse principle for
quadratic forms. Page 349 describes the resulting classification by
discriminants, local Hasse–Witt invariants and real signatures.
No errata note for this source is present in the current project Library.

The provenance is derived. The source's number field `K`, quadratic forms in
`n` variables and completions `K_v` are represented by `F`, forms on
`Fin n → F`, and `Global.placeCompletion F v`. The equivalence of forms is
precisely a linear isometry, as required by `Equivalent`. Nondegeneracy is
expressed by the polar bilinear form, which agrees with the source's
nondegenerate quadratic spaces in characteristic zero. Choosing a basis
identifies every finite-dimensional quadratic space of dimension `n` with
this coordinate version.

## Role in the number-field cohomology problem

This is an independent arithmetic prerequisite for the orthogonal case of
`Langlands.GroupScheme.NumberFieldHassePrincipleStatement`, rather than
a proof of that group-cocycle statement. The cohomological interpretation
needs a separate comparison between orthogonal-group cocycles and descended
quadratic spaces. A proof intended for that use must avoid a circular
dependence on the number-field group-cocycle Hasse principle or its equivalent
finite-Galois-cover formulation. The source's cohomological proof route is not
mandated; a classical arithmetic proof can be used.
