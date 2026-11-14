# Proof of the normalized inverse Whittaker realization

Module `Langlands.Representation.Conductor.OrderedUnramifiedWhittakerProof`.

## Statement

`Langlands.Conductor.orderedUnramifiedWhittakerRealization` proves
`Langlands.Conductor.OrderedUnramifiedWhittakerRealizationStatement.{uF}` (module
`Langlands.Representation.Conductor.OrderedUnramifiedWhittakerStatement`) at an arbitrary
universe `uF`. The statement is used unchanged. It covers:

* every nonarchimedean local field `F`, including positive characteristic, with a
  uniformizer `ϖ` and residue cardinality `q`;
* every rank `n + 1` and every `z : Fin (n + 1) → ℂˣ` with weakly increasing norms
  `‖z i‖`, so equal norms, repeated parameters and reducible principal series are included;
* every unitary additive character `ψ` of `F` with integer conductor.

For these data there is a functional `ℓ` in `glInverseFunctionals ψ n (principalSeries hϖ n hq z)`
with `ℓ.val ≠ 0`, an injective coefficient map, and coefficient map sending the normalized
spherical section to the explicit spherical Whittaker function
`Spherical.sphericalWhittaker hϖ (inverseStandardCharacter ψ n) q z`.

## Proof

The theorem is `OrderedUnramifiedWhittakerAssembly.realization_of_h411` applied to
Bernstein–Zelevinsky's Theorem 4.11 over all nonarchimedean local fields,
`Langlands.AllFieldBZ.Derivative.orderedCuspidalProductNoDegenerateSubmodules.{uF, uF} P T`,
for every local-field package `P` and topological data `T`. That theorem is the all-field
port of the Library's p-adic `Langlands.Derivative.orderedCuspidalProductNoDegenerateSubmodules`
and is published in the Library (module
`Langlands.AllFieldBZ.Representation.Derivative.OrderedCuspidalProductNondegeneracyProof`). It is used at `uV := uF` because the rank-one blocks live on `ULift.{uF} ℂ`.

The helper modules carry out the following steps:

1. `OrderedUnramifiedProductComparison`: `I(z)` is equivalent to the normalized product, over
   the singleton block shape, of the rank-one characters of `GL_1(F)`. On the upper Borel,
   the port's normalized product character agrees with the half modulus.
2. `OrderedUnramifiedRankOneBlocks` (Worker 222): the rank-one blocks, their action formula,
   and the Bernstein–Zelevinsky condition `χ_j ≇ ν χ_i` for `i < j`, which follows from
   `‖z_i‖ ≤ ‖z_j‖`.
3. `OrderedUnramifiedNondegeneracy`: by Theorem 4.11, every nonzero mirabolic subrepresentation
   of the product has nonzero standard Whittaker coinvariants.
4. `OrderedUnramifiedTopLine` (Worker 222): the standard coinvariants of the product are
   one-dimensional. This is the top derivative of a product of rank-one blocks.
5. `OrderedUnramifiedTransport`: coinvariants and their nontriviality transfer along
   equivalences of representations and along the identification of the inverse standard
   character of `ψ` with the standard character of `x ↦ ψ(-x)`.
6. `UnramifiedSphericalWhittaker` (Worker 5557, from the draft of Task 5680): every
   inverse-character functional sends the spherical section to `ℓ(f₀)` times the spherical
   Whittaker function (Shintani uniqueness).
7. `OrderedUnramifiedWhittakerReduction`: one-dimensional inverse coinvariants give a
   spanning functional. Nondegeneracy of every nonzero subrepresentation makes its
   coefficient map injective. Rescaling by `ℓ(f₀)⁻¹` normalizes the spherical image.
8. `OrderedUnramifiedWhittakerAssembly`: combines steps 1–7.

## Provenance

This follows Jacquet, *A correction to Conducteur des représentations du groupe linéaire*
(Pacific J. Math. 260 (2012), 515–525; registered `jacquet-2012-conductor-correction`), §1,
printed page 518: Lemma 2 and the spherical-image comparison after it. Jacquet attributes
injectivity to Jacquet–Shalika 1983, Proposition (3.2). Here injectivity is proved instead
from Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(Ann. Sci. ÉNS (4) 10 (1977), 441–472), Theorem 4.11, together with the kernel argument. The
proof does not use the analytic Jacquet integral.
