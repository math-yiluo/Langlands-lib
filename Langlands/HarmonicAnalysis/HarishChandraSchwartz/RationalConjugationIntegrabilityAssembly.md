# Assembly of actual split-central conjugation integrability

`RationalCuspidalConjugationIntegrabilityReductionStatement.{u}` is the
internal implication

```lean
RationalCuspidalConjugationBoundStatement.{u} →
  JointSpecialCompactBasisExistenceStatement.{u} →
  RationalCuspidalConjugationIntegrabilityStatement.{u}
```

`rationalCuspidalConjugationIntegrability_of_bound_and_jointSpecialCompactBasis`
proves this implication. Its premises are the actual VIII.3.1 target
`RationalCuspidalConjugationBoundStatement` and the joint structural target
`JointSpecialCompactBasisExistenceStatement`; its conclusion is the VIII.3.2 target.

The source motivation is Waldspurger, *La formule de Plancherel pour les
groupes p-adiques* (2003), registered as `waldspurger-2003-plancherel`, Corollary
VIII.3.2, printed pp.326–327 (PDF pp.92–93). The implemented route makes the
source's smoothness, compatible quotient-cell volumes, lattice summability
and Bochner measurability steps explicit through the named companion results.

The local theorem
`rationalCuspidalConjugationIntegrability_of_bound_and_uniformizerCover`
retains the original nonarchimedean field, affine locally finite type
connected reductive group, maximal split torus, structural subgroup `K0`
with `SimultaneousStandardBasisAt`, independent compact open Iwasawa subgroup
`K`, nonempty finite closed matrix realization, actual split component and
displayed Borel structures. It takes the supplied group Haar measure `muG`,
right-invariant central Haar measure `muA` and the compatible measure `muQ` on
the exact split-central left quotient. It assumes the local VIII.3.1
conclusion and `RationalSplitCentralUniformizerCover`.

Actual reductive unimodularity gives right invariance of the supplied `muG`
by the formula for pushforward under right multiplication. The canonical
rational-point topology supplies the second-countability and Hausdorff
hypotheses of that formula.
The index type consists of the actual cocharacters having nonnegative
simple-root pairings and uniformizer powers in `G¹`. This is a countable
subtype of the finite-rank cocharacter lattice. The helper theorem
`uniformizerPowers_mem_rationalMinimalChamber_of_dominant` uses the published
character-valuation formula for the common uniformizer to place every index
in the full ambient minimal chamber. Combining this with its `G¹` membership
gives an actual point of `rationalMinimalChamberInNormKernel`, read in the
actual minimal parabolic for the existing integrability adapter.

The supplied quotient cover chooses a compact open left factor `H` and a
compact right factor `Y`. The cells are exactly the images of `H * {a} * Y`
under the existing same-representative left-coset map. Their volume bound is
the companion
`exists_rationalSplitCentralQuotient_measure_compact_cell_le_inverse_modulus`
for the same `muQ`; its simultaneous-basis argument allows `H`, the structural
`K0` and the Xi-defining `K` to be distinct. The companion
`exists_summable_rationalHeight_uniformizerPowers` supplies summability on the
whole cocharacter lattice for some natural decay exponent. Restriction to
the injective subtype of dominant norm-kernel parameters gives the required
cell series for the original arbitrary matrix height.

For intrinsic cuspidal `f1` and Schwartz `f2`, their entire conjugate-function
families on `H` and inverse-conjugate families on `Y` are finite by the
published smoothness results. Translation stability of the actual Schwartz
space puts each conjugate back in that same Schwartz space. Intrinsic
cuspidality of a conjugate follows directly by reindexing the already
quantified left and right translates in its all-Haar unipotent kernel
condition. Apply the local VIII.3.1 bound to each pair and use
`conjugationIntegralBound_iff_rationalChamberBound` to match the existing
adapter's half-weight convention. The finite-family argument supplies a
uniform constant.

The published a.e. strong measurability theorem applies to the displayed
Borel structure of the same actual quotient for every measure. The existing
adapter combines it with the finite lower integral from the covering,
volume and series estimates to prove Bochner `Integrable`. The local theorem
retains the all-conjugators inner convergence component directly from the
local VIII.3.1 conclusion. Thus its conclusion is precisely
`RationalCuspidalConjugationIntegrability` for the supplied measures, with
both finite integral of the norm and a.e. strong measurability.

The reduction theorem specializes the assumed VIII.3.1 statement to every
choice in the original VIII.3.2 target and applies the companion cover
theorem to the assumed joint structural statement. The local result gives
both conclusions of the original proposition under these two premises.
`rationalCuspidalConjugationIntegrability_iff_right` supplies the
right-quotient formulation with its explicitly transported measure.
