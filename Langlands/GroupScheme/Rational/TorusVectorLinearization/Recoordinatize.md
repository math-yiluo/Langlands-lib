# Changing natural vector coordinates by a natural additive transition

This module is an internal step in the proof that every torus action on a vector
group becomes linear in suitable coordinates. That proof does not keep the input
coordinates `e` of the vector group `V ≅ Ga^n`. It replaces them by `Y ∘ e`, where
`Y` is an additive automorphism of coordinate vectors that is natural in the
coefficient algebra. In positive characteristic, `Y` is given by a tuple of
additive polynomials with coefficients in `k`. This module
records what such a change of coordinates preserves, and how the scalar-linearity
test transforms under it. Everything is in namespace
`Langlands.GroupScheme.RelativeRoot` over a field `k`.

## The transition data

`NaturalCoordinateEquiv k n` consists of:

- `equiv A : (Fin n → A) ≃+ (Fin n → A)` for every commutative `k`-algebra
  `A : CommAlgCat (CommRingCat.of k)`;
- `naturality`: for every algebra map `f : A ⟶ B` and `x : Fin n → A`,
  `equiv B (f ∘ x) = f ∘ (equiv A x)`.

## The changed coordinates

- `recoordinatize e Y T` composes the coordinates `e T` of the points of `V`
  over a test `T` with `Y.equiv` at the global sections `Γ(T, ⊤)`, viewed as a
  `k`-algebra through `algΓ`. The composite is again a multiplicative equivalence
  `(T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T, ⊤))`. `recoordinatize_apply`
  unfolds this definition.
- `IsNaturalVectorCoordinates.recoordinatize`: if `e` is natural in the test
  scheme, so is `recoordinatize e Y`. Naturality of `e` moves the restriction map
  inside, and naturality of `Y` along the induced map of global sections moves
  it past `Y`.
- `vectorAffineCoordinates_recoordinatize`: on an affine test `Spec A`, the
  changed coordinates are `Y.equiv A` applied to the old ones. The proof applies
  naturality of `Y` to the comparison isomorphism
  `Corepresented.affineSectionsIso A` between global sections of `Spec A` and `A`.
- `vectorAffineCoordinates_recoordinatize_symm`: the inverse of the changed
  coordinates sends `z` to the point with old coordinates `(Y.equiv A).symm z`.

## The linearity criterion

`isAffineLinearVectorCoordinates_recoordinatize` gives the criterion. Let `a` be
an action of a group scheme `H` on `V`. Suppose that for every `k`-algebra `A`,
every point `h` of `H` over `A`, every scalar `c : A` and every `z : Fin n → A`,
the map

`z ↦ Y(e(h · e⁻¹(Y⁻¹ z)))`

sends `c • z` to `c` times the image of `z`. Then `recoordinatize e Y` satisfies
`IsAffineLinearVectorCoordinates a`, the published scalar-linearity condition on
affine tests. The proof writes an arbitrary point as the inverse coordinate image
of `z` and rewrites with the two coordinate lemmas above. The hypothesis is then
exactly the assumed identity.

## Provenance

This module is internal bookkeeping for the proof of
`TorusVectorActionLinearizationStatement`. It does not formalize a statement from
the literature. In Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, 2nd ed.,
Theorem B.4.3 (printed p.577, PDF p.603), the non-fixed factor receives a new
linear structure in which the torus acts linearly, and the proof of
Proposition B.4.2 obtains it through an equivariant automorphism `α` of a linear
representation. This module records the general fact that a change of coordinates
preserves naturality, which the formal proof uses in place of `α`. The criterion is
derived here from the published definitions `IsNaturalVectorCoordinates`,
`vectorAffineCoordinates` and `IsAffineLinearVectorCoordinates`.
