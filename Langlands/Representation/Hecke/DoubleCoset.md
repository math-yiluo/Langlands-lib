# Actual compact-open double-coset Hecke operators

This module constructs actual compactly supported double-coset functions and
their operators on the existing fixed-vector space of a smooth representation.
Its provenance is internal: it combines Mathlib's `DoubleCoset.doubleCoset`,
compact/open set products, and the published `Hecke.TestFunction.characteristic`,
`HeckeAlgebra.Corner`, and `cornerAction` constructions. The new proofs use
group multiplication, topology of set products, and the already proved corner
action laws. No classification theorem is invoked.

## Group, topology, coefficients and measure

The group `G : Type uG` is arbitrary, with a topology making it a topological
group. `K : OpenSubgroup G` is an actual open subgroup with a proof `hK` of its
compactness. The double-coset set and its elementary invariance properties are
constructed before imposing a Hausdorff assumption. Construction of its test
function additionally assumes `T2Space G`, so compactness implies closedness.

All functions and representations have complex coefficients. For the Hecke
corner and action, `G` has its Borel measurable structure and a supplied genuine
Haar measure `μ`. The compact-open subgroup has strictly positive finite mass,
as already proved by `HeckeAlgebra.compactOpen_mass_pos`. The module does not
choose a Haar measure or assert independence from its choice.

Representation carriers `V : Type uV` and `W : Type uW` have independent
universes, complex module structures, and no finite-dimensionality or topology
requirements. Their representations must be smooth. Neither irreducibility,
admissibility nor nonzero fixed vectors is required for these constructions.

## Double-coset sets and test functions

The declarations in `Langlands.Hecke.TestFunction` are:

- `doubleCosetSet K g`: exactly Mathlib's set `K * {g} * K`.
  `mem_doubleCosetSet` identifies membership with the existence of `a,b ∈ K`
  satisfying `x = a*g*b`.
- `isOpen_doubleCosetSet` and `isCompact_doubleCosetSet`: openness follows from
  multiplying an open set by arbitrary sets; compactness follows from the
  product of the compact subgroup, a singleton and the compact subgroup.
  `isClopen_doubleCosetSet` combines openness with Hausdorff compactness.
- `mul_mem_doubleCosetSet_left` and `mul_mem_doubleCosetSet_right`: multiplying
  by an element of `K` on either indicated side preserves and reflects
  membership. The reverse implications multiply the appropriate witness by
  the inverse element of `K`.
- `doubleCosetSet_one`: the identity double coset is exactly `K`.
  `doubleCosetSet_eq_of_mem` proves that replacing `g` by any member of `K g K`
  gives the same set, by Mathlib's double-coset equality lemma.
- `doubleCosetIndicator K hK g`: the published characteristic test-function
  construction applied to this compact clopen set. Its pointwise value is
  exactly `1` on `K g K` and `0` off it. `support_doubleCosetIndicator` identifies
  its support with that set, and `doubleCosetIndicator_mem` proves membership
  in the existing bi-invariant submodule using the two membership equivalences.
- `doubleCosetIndicator_one` identifies the identity double-coset indicator
  with `subgroupIndicator K hK`. `doubleCosetIndicator_eq_of_mem` transports
  the preceding representative-independence equality to actual test functions.

## Normalized corner elements and operators

`Langlands.Hecke.HeckeAlgebra.Corner.doubleCoset K hK μ g` is the actual
bi-invariant function

`μ(K)⁻¹ · 1_(K g K)`.

Here `μ(K)` means the real mass `μ.real (K : Set G)`, embedded in `ℂ`, and the
inverse and multiplication are complex operations. The construction uses the
existing convolution corner carrier and proves its membership by scalar closure
of the bi-invariant submodule. It divides by the mass of `K`, not the mass of
the whole double coset. `doubleCoset_apply` states this pointwise formula;
`doubleCoset_apply_of_mass_one` reduces it to the unnormalized characteristic
function when `μ.real K = 1`.

`doubleCoset_one` proves that the identity double coset is the corner's actual
unit, namely the existing normalized subgroup indicator. The proof rewrites
the identity double-coset indicator. `doubleCoset_eq_of_mem` proves equality in
the corner after replacing the representative within its double coset.

`Langlands.Hecke.doubleCosetOperator K hK μ ρ hρ g` applies the published unital
`cornerAction` to this corner element. Its carrier is exactly
`fixedVectors ρ K.toSubgroup`; no replacement fixed-vector space is introduced.
`doubleCosetOperator_apply` identifies its value in the ambient module with
the existing integrated Hecke action. The integration convention is inherited
unchanged: the function weights `ρ(g)` in the integrated operator, while
convolution uses `f(y) h(y⁻¹ x)`.

`doubleCosetOperator_one` uses the unital algebra homomorphism law to obtain
the identity endomorphism. `doubleCosetOperator_eq_of_mem` proves independence
of the group representative. `doubleCosetOperator_intertwiner` specializes the
existing corner-action naturality: restricting an actual representation
intertwiner to fixed vectors commutes with these operators, including across
independent carrier universes.

These are operators for arbitrary compact open subgroups. No commutativity,
basis or generation assertion for the corner, scalar-eigenvalue assertion,
Cartan decomposition, or Satake normalization theorem is made. Specializing the
operators to the standard diagonal elements of `GL_n` and comparing their
eigenvalues with inducing spectra are separate steps.
