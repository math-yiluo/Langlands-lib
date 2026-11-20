# The integer algebra of an actual embedded local subfield

Let `K` be a nonarchimedean local field with its given valuative relation and
compatible topology, and let `D` be a finite-dimensional central division
`K`-algebra. The carriers `K` and `D` have a common arbitrary universe. Let
`ι : L →ₐ[K] D` be an embedding, where `L` is a field in an independent
universe. The characteristic is unrestricted. All declarations are in
`Langlands.CentralDivision`.

Write `w = localDivisionSubfieldValuation K D ι`. Its integer ring `w.integer`
consists of the original elements `x : L` whose images under `ι` have
reduced-norm value at most one. `localDivisionSubfieldIntegerAlgebra K D ι`
is the `Algebra 𝒪[K] w.integer` given by
`(localDivisionSubfieldBaseIntegerMap K D ι).toAlgebra`. Use this definition
with `letI` to install the original scalar action.

`localDivisionSubfieldIntegerToLattice K D ι` sends each `x : w.integer` to
`ι x` in `localDivisionIntegerLattice K D` using
`localDivisionSubfieldIntegerMap`. Its subtype coercion to `D` is
recorded in `localDivisionSubfieldIntegerToLattice_coe`. The lattice has the
original division integer set as carrier. Integrality in `w` gives the image's
membership in this set. The lattice action is the original `K`-action
restricted to `𝒪[K]`. Linearity follows from `map_add`, `map_mul`, and
`ι.commutes`. Injectivity follows from
injectivity of `ι` and is proved in `localDivisionSubfieldIntegerToLattice_injective`.

The theorem `localDivisionSubfieldInteger_finite` proves
`Module.Finite 𝒪[K] w.integer` with this algebra structure. The base integer
ring is a discrete valuation ring by `IsNonarchimedeanLocalField` and hence
Noetherian. The target lattice is finite by
`localDivisionIntegerLattice_finite`. Mathlib's `Module.Finite.of_injective`
applied to the linear inclusion proves the claim for any embedded `L`.

This is an internal construction from `localDivisionSubfieldValuation` and
`localDivisionSubfieldBaseIntegerMap` in `LocalDivisionResidueSubfield` and
`LocalDivisionResidueLift`, and the finite module on the very same division
integer set in `LocalDivisionIntegerLattice`.
