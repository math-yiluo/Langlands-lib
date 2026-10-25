# The CM involution on adelic general linear groups

This module transports the CM involution `c` of a CM field `E` to the adelic
matrix groups `GL_n(𝔸_E)`, `GL_n(𝔸_{E,f})` and `GL_n(E ⊗ ℝ)`. It also gives
the restriction to the standard compact subgroup at infinity and the
corresponding map on the real matrix Lie algebra. These are the maps through
which Harris's condition `π ≅ π̌ ∘ c` is formulated in
`Langlands/Automorphic/ConjugateContragredient`.

## Setting

`E` is a number field with Mathlib's `IsCMField E`. `fieldConj E` is Mathlib's
CM involution `IsCMField.complexConj E`, viewed as a ring automorphism of `E`.
The adelic matrix groups are the Library's `AdelicGL E n`, `FiniteAdelicGL E n`
and `InfiniteAdelicGL E n` (`Langlands/Global/AdelicGL`). The transport of
adeles along a field isomorphism is the Library's arithmetic transport
(`Langlands/Global/AdelicFunctoriality`): `adeleEquiv`, `finiteAdeleEquiv` and,
for the CM involution at the infinite places, `infiniteComplexConj`. These
maps send the component at a place to the component at the transported place,
through the induced isomorphism of completions. For the CM involution every
infinite place is fixed (`infinitePlaceEquiv_complexConj`), and a finite place
goes to its conjugate place.

## Definitions

- `adelicConj E n`, `finiteConj E n` and `infiniteConj E n` are the
  topological group automorphisms of `AdelicGL E n`, `FiniteAdelicGL E n` and
  `InfiniteAdelicGL E n` that apply `adeleEquiv (fieldConj E)`,
  `finiteAdeleEquiv (fieldConj E)` and `infiniteComplexConj` to every matrix
  entry. The `_apply` lemmas record these entrywise formulas. Continuity in
  both directions comes from the continuity of the entry maps.
- `mixedConj E` is the real algebra automorphism of the mixed space
  `ℝ^{r₁} × ℂ^{r₂}` that is the identity on the real coordinates and complex
  conjugation on the complex coordinates.
- `compactConj E n` is the restriction of `infiniteConj E n` to the standard
  compact subgroup `standardInfiniteCompact E n`, as a group endomorphism.
- `lieConj E n` is the real Lie algebra endomorphism of
  `ArchimedeanGL.RealLieAlgebra E n` (matrices over the mixed space) that
  applies `mixedConj E` to every entry.

## Theorems

- `finite_adelicConj` and `infinite_adelicConj`: the finite and infinite
  components of `adelicConj E n g` are `finiteConj E n` and `infiniteConj E n`
  applied to the components of `g`.
- `adelicConj_rational`: a rational matrix `γ ∈ GL_n(E)` is sent to the
  rational matrix with entries `c(γ_{ij})`. In particular `adelicConj`
  preserves `GL_n(E)`.
- `not_isReal`: a CM field has no real places.
- `mixedSpace_infiniteComplexConj` and `coordinates_infiniteConj`: in the
  mixed coordinates `archimedeanGLCoordinates`, `infiniteConj` is entrywise
  `mixedConj`. Since there are no real places, this is entrywise complex
  conjugation at every complex place. The proof uses the Library's
  `infiniteComplexConj_coordinate`.
- `infiniteConj_mem_standardInfiniteCompact`: `infiniteConj` preserves the
  standard compact subgroup. At each complex place this subgroup is the unitary
  group `U(n)`, and the entrywise conjugate of a unitary matrix is unitary.
- `lieConj_apply`: the entrywise formula for `lieConj`.

## Relation to the group maps

The Lean module does not prove that `lieConj` is the differential of
`infiniteConj`; the following explains why this is the right map. The
coordinates `archimedeanGLCoordinates` identify `InfiniteAdelicGL E n` with
invertible matrices over the mixed space. In these coordinates `infiniteConj`
is the entrywise map `mixedConj` (`coordinates_infiniteConj`). This map is a
continuous real algebra automorphism of the matrix algebra, so it commutes
with the matrix exponential. Hence the differential of `infiniteConj` at the
identity is the same entrywise map on the real Lie algebra, which is
`lieConj`.

## Source and provenance

Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134 (1998), Theorem 1.2(ii), printed p. 185, PDF page 9
(retained TeX `math_9611226v1.tex`, condition (ii) at lines 530–533), uses
the condition `π ≅ π̌ ∘ c`.
There `E = E₀·K₀` with `E₀` totally real and `K₀` imaginary quadratic, and
`c` is the nontrivial element of `Gal(E/E₀)`. Such an `E` is a CM field with
maximal totally real subfield `E₀`, so `c` is the CM involution. Harris writes
`π̌ ∘ c` without spelling out how `c` acts on `GL_n(𝔸_E)`. The action used here
is the standard one: `c` acts on adeles by functoriality and on matrices
entrywise. The module is derived: it makes this implicit action explicit. It
works for an arbitrary CM field, which is more general than Harris's fields
`E₀·K₀`.
