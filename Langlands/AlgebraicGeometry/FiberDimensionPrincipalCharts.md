# Principal polynomial charts and uniform fibre dimension bounds

This is a derived algebraic construction toward the fibre-geometry condition
in Conrad, *Weil and Grothendieck approaches to adelic points*, printed
pp. 5–6, Theorem 3.4(2). Conrad does not state this internal constructor.
It supplies a principal source neighbourhood with a bound on the total
dimensions of its actual residue-field fibres. It does not yet give the
bound by the local fibre dimension at the chosen source point.

## Constructed data

`FiberDimensionPrincipalChart R S q` extends the existing actual
`FiberQuasiFiniteCoordinates R S (q.comap (algebraMap R S))`. Its inherited
rank `n` and coordinates in `S` give a finite injective normalization of the
original base fibre of `S`, with `n` equal to that fibre's Krull dimension.
The inherited original polynomial map is quasi-finite at every point over
that base prime. The additional data are an element `r` outside `q`,
quasi-finiteness of the polynomial evaluation map
`R[X₁,…,Xₙ] → S[1/r]` at the localized coordinates, and

```
ringKrullDim (κ(p) ⊗[R] S[1/r]) ≤ n
```

for every prime `p` of `R`. Dimensions are compared in `WithBot ℕ∞`;
empty fibres are allowed. Since `r` is outside `q`, the localization is
an actual principal neighbourhood of `q` in `Spec S`.

`fiberDimensionPrincipalChart R S q` constructs all this data for arbitrary
commutative rings `R : Type u`, `S : Type v` with an `R`-algebra structure
and `Algebra.FiniteType R S`. The universes are independent. There is no
Noetherianity, domain or injectivity assumption. A source prime `q` is the
only point data supplied. The actual fibre over its contraction is nonzero:
its prime spectrum contains the image of `q` under
`PrimeSpectrum.preimageHomeomorphFiber`. Thus no separate nonzero-fibre
hypothesis is imposed.

## Implemented construction

First choose the proved normalization and quasi-finite coordinates of the
original fibre. Give `S` its algebra structure over their polynomial ring
`B`; finite type over `R` implies finite type over `B`. The inherited
quasi-finiteness at `q` then applies to this algebra structure.

`exists_away_quasiFinite_of_quasiFiniteAt` uses Mathlib's algebraic Zariski
main theorem to obtain a module-finite `B`-subalgebra `S'` of `S` and an
element of `S'` outside `q` whose localization maps bijectively onto the
corresponding localization of `S`. A finite algebra is quasi-finite;
localization, composition and a surjective algebra map preserve
quasi-finiteness. Consequently `S[1/r]` is quasi-finite over `B`.
Polynomial extensionality identifies this algebra map with evaluation at
the localized coordinates. Existence is proved in `Nonempty` before
classical choice produces the record; its substantive fields are conclusions,
not caller assumptions.

The auxiliary tensor-map result adapts Mathlib's finite tensor-map argument.
Tensor commutation and base-change cancellation identify extension of a map
with a base change followed by an algebra equivalence. Quasi-finiteness is
preserved by those operations. A second tensor commutation puts the changing
algebra in the right factor.

`fiber_dimension_le_of_quasiFinite_polynomial` applies that result to the
actual `κ(p)`-fibre map. The published
`Langlands.AlgebraicGeometry.ringKrullDim_le_of_quasiFinite` bounds the
source fibre dimension by that of the polynomial fibre. The equivalence
`MvPolynomial.algebraTensorAlgEquiv` identifies the latter with the
polynomial ring over `κ(p)`, whose dimension is exactly `n` by the existing
finite-variable polynomial dimension theorem. This proves the uniform
bound and completes every field of the constructor.

## Retained obligations

The rank here is the total dimension of the original fibre. To obtain a
bound by its local dimension at `q`, one still needs a principal source
neighbourhood realizing that local dimension. General relative-dimension
sublevel openness and retrocompactness, geometric-connectedness
constructibility, filtered descent, and Conrad Theorem 3.4(2) remain separate
obligations. This construction asserts none of them.
