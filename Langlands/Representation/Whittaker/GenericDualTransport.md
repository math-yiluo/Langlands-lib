# Explicit Whittaker-functional transport to the smooth dual

This internal construction supplies the functional-transport step needed by
`Langlands.GenericContragredientStatement`. It does not identify the
inverse-transpose representation with the smooth contragredient.

For a complex representation `rho` of the actual `GL_(n+1)(F)`, a supplied
complex linear equivalence `E : V ≃ₗ[ℂ] SmoothDual rho`, and a linear functional
`ell` on `V`, `explicitSmoothDualFunctional rho E ell` is the actual functional

`v ↦ ell (rho(w_(n+1)) (E.symm v))`.

Here the long Weyl element has ones on the anti-diagonal, and `SmoothDual rho`
is the published submodule of smooth vectors in the algebraic dual. No
replacement carrier or dual action is defined.

The application lemma is definitional. Nonvanishing follows by evaluating an
assumed zero functional at `E (rho(w) v)`, since `w * w = 1`. The covariance
lemma assumes that `E` intertwines the actual inverse-transpose pullback with
`smoothContragredient rho`; existence of such an `E` remains a separate theorem.
It applies the original functional's explicit upper-unitriangular covariance
to `w * inverseTranspose(g) * w`. The published `reflectedUnipotent` proves that
this matrix is upper unitriangular and its adjacent entries are the negatives
of those of `g`, in reverse order. Reindexing the finite product by `Fin.revPerm`
therefore gives exactly the inverse additive character, including the empty
product in rank one.

The construction works over any topological commutative ring. The covariance
law additionally assumes `IsTopologicalRing F`, to form the smooth dual action.
It needs no admissibility, irreducibility, continuity or nontriviality of the
additive character, or topology or finite-dimensionality on `V`. These weaker
hypotheses apply only to transport through a supplied equivalence; they do not
strengthen the Gelfand–Kazhdan existence theorem.

Provenance is derived/internal: composition of linear maps, the published actual
smooth-dual construction, and the matrix identities in
`Langlands.Representation.Whittaker.DualTransform` and
`Langlands.Group.GL.Maps`. This module exposes the explicit adjacent-entry
product convention of the existing target. It proves no new distribution,
trace-character or irreducible-duality theorem.
