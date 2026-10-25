# A shared minus-one scalar on coefficient images

Author: Worker 112.

This is an internal construction derived from the published
`Langlands.Whittaker.coefficientCentralCharacter` and the published
`HasModelMinusOneScalar` predicate and its uniqueness theorem. It asserts no
additional original-literature result.

Let `F` be a topological field whose ring operations are continuous, `n` a
natural number, and `σ` a complex representation of `GL_(n+1)(F)`. The field and
representation carrier have independent universes. Fix an arbitrary
complex-unit-valued character `θ` of the standard upper unipotent subgroup.
Assume `IsOfWhittakerType n θ σ`, with its existing meaning: admissibility,
finite generation over the group algebra, and a one-dimensional equivariant
functional space. No irreducibility or finite-dimensional carrier is assumed.

`minusOneCentral n F` is the actual negative identity matrix `-1` in the
general linear group, with its centrality proved by equality of the underlying
matrices. It is not a formal sign or a separately postulated central element.

`modelMinusOneScalar σ hσ` evaluates the coefficient central character at this
matrix. The imported central-character theorem applies because `hσ.1.1`
supplies smoothness and `hσ.2.2` supplies the required linear equivalence with
the complex field. Its character is chosen before any particular equivariant
functional, so the resulting complex unit is shared by all coefficient images.

`hasModelMinusOneScalar_modelMinusOneScalar` specializes that theorem's
coefficient action to `minusOneCentral`. It proves exactly the published
predicate: for every function `f` in the image of any equivariant functional
`ℓ`, and every group element `g`,

`f((-1) * g) = modelMinusOneScalar σ hσ * f(g)`.

The functional may be zero. `exists_modelMinusOneScalar` packages the
construction as `∃ ζ, ∀ ℓ, HasModelMinusOneScalar σ ℓ ζ`, with the scalar outside
the functional quantifier. `modelMinusOneScalar_eq` uses the published
`HasModelMinusOneScalar.unique` to identify it with any other scalar satisfying
the predicate for a nonzero functional. This last result, unlike existence,
requires the functional to be nonzero.

This construction supplies only the central sign input of the Rankin–Selberg
functional equations. It does not establish rational continuation, nonzero
integral values, bilinear uniqueness, or the gamma functional equation.
