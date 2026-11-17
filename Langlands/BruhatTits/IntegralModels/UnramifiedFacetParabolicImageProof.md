# Parabolic images and reduction preimages for descended facet models

Module `Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicImageProof`.

The theorem
`Langlands.BruhatTits.IntegralModels.unramifiedFacetParabolicImage` proves
exactly `UnramifiedFacetParabolicImageStatement.{u}` at arbitrary universe
`u`, with no additional premises.

For every incident pair of facets `Fc ≺ Fc'`, every pair of characterized
descended relative-component models `D`, `D'`, and every
`φ : RelativeComponentModelHom D' D`, it proves both
`φ.HasParabolicSpecialFibreImage` and `φ.HasParabolicReductionPreimage`.
The first is parabolicity of the actual schematic image of the neutral
special-fibre map. The second says that the inverse image of all residue-field
points of this image under target reduction is exactly the image of the
source integral sections under `φ.neutral.hom`.

The theorem retains all seven building hypotheses, all eight
apartment-descent hypotheses, the universal choices of building and zero data,
the incident facets, both smoothness hypotheses and both exact model
characterizations. Those characterizations use integral points after base
change to `fixedFieldIntegers F`, the integers of the maximal unramified
extension. Existence of the supplied building data or models is outside this
target.

## Implemented proof

The proof applies the published assembly theorem
`unramifiedFacetParabolicImage_of_generation_positive_modelKernel` from
`UnramifiedFacetParabolicImageReduction`. Its three full statement premises
are discharged by the imported proved theorems:

- `unramifiedUpstairsRadicalRootGeneration`, proving
  `UnramifiedUpstairsRadicalRootGenerationStatement`;
- `unramifiedFacetPositiveRadical`, proving
  `UnramifiedFacetPositiveRadicalStatement`;
- `unramifiedModelKernel`, proving `UnramifiedModelKernelStatement`.

Each is used at the same arbitrary universe `u`. There is no remaining
unproved global statement premise.

For the parabolicity conjunct, the assembly specializes the upstairs
root-generation theorem to the supplied model characterizations. Its
parabolicity reduction puts the incident facets in a common translated
apartment, applies the actual upstairs image criterion, and reflects
parabolicity through the residue-field extension.

For the reduction-preimage conjunct, the facet-kernel reduction constructs a
common apartment chart whose lower subset is nonempty, whose upper subset
is bounded under every real affine functional, and whose lower subset lies in
the affine-topological closure of the upper subset. It applies
`unramifiedModelKernel` to the actual extended neutral models and map and
reflects smoothness, connectedness and unipotence of the full scheme kernel.
This gives surjectivity on residue-field points of the projection onto the
actual schematic image. The positive-radical theorem gives containment of
the target positive subgroup in the source positive subgroup for every pair
of valid reductive quotients. The existing Henselian lifting criterion
combines these facts to obtain the exact equality of integral-section
subgroups. The local-field valuation ring is Henselian by
`henselianLocalRing_integer`, and its finite residue field is perfect.

Only this final composition is new in this module. The target statement and
its imports are unchanged.

## Provenance and source scope

The target is KP Axiom 4.1.22(2), (4), printed pp. 163–164 / PDF pp. 194–195
of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The upstairs source assertions are Theorem 8.4.19(2), (3), printed
pp. 308–310 / PDF pp. 339–341. Their descended forms are §9.3.2 and
Proposition 9.3.3, printed pp. 331–332 / PDF pp. 362–363, with the assignment
to the axioms explained in §9.5, printed pp. 363–364 / PDF pp. 394–395.
The kernel input uses Proposition 8.4.15.

The registered `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 37–38, supplies the perfect-residue hypothesis and the integral-model
map setup for §§8.3–8.4. The local-field target supplies perfect residue and
an actual model map. The faulty restricted kernel index in
Theorem 8.4.19(1), recorded in the
[KP source ledger](../../../notes/bruhat-tits/kp-source-ledger.md), is not used.
The unchanged target's
[paired explanation](UnramifiedFacetParabolicImageStatement.md) gives the
complete source comparison. This proof follows the published internal
parabolicity, full-kernel and positive-subgroup lifting reductions described
above.
