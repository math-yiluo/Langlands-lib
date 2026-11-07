# The original integer lattice

This is an internal construction from the imported original reduced-norm
valuation, its compact integer set, the compatible division-algebra norm,
and Mathlib's finite-dimensional coordinate and Noetherian module results.

Let `K D : Type u`, where `K` is a nonarchimedean local field with its given
valuative relation and topology, and `D` is a finite-dimensional central
division algebra over `K`. There is no characteristic restriction. Write
`v = localReducedNormValuation K D` and `O = 𝒪[K]`.

The local norm on `K` is `LocalGalois.localNormedField K`. Where needed, the
normed structures on the original `D` are `localDivisionNormedRing K D` and
`localDivisionNormedAlgebra K D`. These retain the original ring and scalar
operations. The scalar action of `O` on `D` is the composite of its original
inclusion into `K` with the original algebra map from `K` to `D`.

`localDivisionIntegerLattice` is the `O`-submodule of the original `D` with
carrier exactly `v.integer`, namely the elements satisfying `v x ≤ 1`.
Addition is closed because this is the actual valuation integer subring.
For scalar multiplication, the original scalar-valuation formula gives

```
v ((c : K) • x) = (valuation K (c : K)) ^ n * v x,
```

where `n` is the reduced degree. Both factors are at most one for integral
`c` and `x`, proving closure. Thus the module structure uses the actual
integer set and the original scalar action.

`localDivisionIntegerLattice_span` proves that this set spans `D` over `K`.
For any original `x : D`, nontriviality of the base norm supplies a nonzero
`c : K` with `‖x‖ + 1 < ‖c‖`. The compatible scalar norm makes
`‖c⁻¹ • x‖ ≤ 1`. The imported exact norm-integrality equivalence places this
element in the actual lattice. Multiplying it by `c` recovers `x`.

`exists_localDivisionIntegerLattice_coordinate_bound` uses the original basis
`Module.finBasis K D` and proves that there exists a nonzero original `c : K`
such that every lattice element `x` and every original coordinate `i` satisfy

```
valuation K ((Module.finBasis K D).equivFun x.val i / c) ≤ 1.
```

The theorem installs the compatible normed structures in its type. Its proof
maps the actual compact integer set through the continuous coordinate
equivalence. The resulting compact set is bounded, so one real constant `C`
bounds all coordinate-vector norms. Each coordinate norm is at most that
vector norm. Choose `c` with `max C 0 < ‖c‖`; division by `c` then has norm
at most one. The original base norm-order equivalence makes each divided
coordinate an element of the original `O`.

`localDivisionIntegerLattice_finite` concludes

```
Module.Finite O (localDivisionIntegerLattice K D).
```

Using the preceding `c`, its proof defines the `O`-linear map sending `x` to
the function of divided original coordinates, with values in
`Fin (Module.finrank K D) → O`. Coordinate linearity and the original
scalar-action compatibility establish additivity and scalar compatibility.
The map is injective: equality of divided coordinates can be cancelled using
`c ≠ 0`, and the original coordinate equivalence is injective.
The base integer ring is Noetherian, and the target is finite free over it.
Mathlib's `Module.Finite.of_injective` therefore proves finiteness of the
original lattice.

This pair proves spanning and finite generation. It does not establish a
ramification formula, compare the actual residue degree with the reduced
degree, prove local SK1, or prove the full local Kneser–Tits proposition.
