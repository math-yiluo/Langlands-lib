# Existence of the integral inner-isomorphism torsor over a DVR

`Langlands.GroupScheme.genericInnerIsomorphismTorsorExistence` proves
`Langlands.GroupScheme.GenericInnerIsomorphismTorsorExistenceStatement.{u}`
in every universe `u`. Given any DVR `R` with specified fraction field
`K`, reductive group schemes `G` and `H` over `Spec R`, and an actual
generic isomorphism `f : G_K ≅ H_K`, it supplies
`Nonempty (GenericInnerIsomorphismTorsor R K G H f)`.

## Implemented proof

The Lean term applies
`genericInnerIsomorphismTorsorExistence_of_affineQuotient_and_outerGeometry`
to four published existence theorems.

- `relativeAdjointQuotientExistence` supplies the affine fppf quotient of
  `G` by its full scheme-theoretic centre. The reduction upgrades the
  quotient to a reductive adjoint group.
- `genericIsomorphismSchemeExistence` supplies the scheme `I` representing
  natural local isomorphisms between `G` and `H`.
- `genericOuterIsomorphismSchemeExistence` supplies the quotient `O` of
  `I` by the action of the selected adjoint group.
- `finiteGenericOuterClassExistence` supplies a finite carrier of the
  class in `O` of the point of `I` classifying the natural family of `f`.

The reduction passes the selected quotient to the outer-quotient and
finite-carrier theorems. Both apply to the Isom scheme and the prescribed
`f`. `GenericInnerIsomorphismTorsor.ofOuter` extends the outer class of `f`
across the DVR and takes the fibre of the class map over that section.
The fibre has an fpqc structure morphism and invertible shear.
Restriction of the universal isomorphism gives natural group isomorphisms
on every test scheme and the compatibility
`e(d • a)(g) = e(a)(inner(d⁻¹)(g))`. The quotient construction supplies
the compatible integral and generic inner actions. Evaluation at the
generic point recovers exactly `f` using the Isom representation inverse
and the base-change isomorphism round trip.

This proof composes the Library constructions for the geometric
intermediate described in the paired statement. Its source context is
Brian Conrad, *Reductive group schemes* (2014), Theorem 7.1.9(1) and its
proof, pp. 245–247, and the forms argument of Theorem 7.2.16, pp. 261–262.
