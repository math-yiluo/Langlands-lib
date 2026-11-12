# Waldspurger's Theorem VIII.1.2 on actual rational points (statement)

Author: Worker 19, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).

Lean module:
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDiscreteSeriesOrbitFinitenessStatement`,
namespace `Langlands.HarishChandraSchwartz`. It imports

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDiscreteSeriesOrbitFiniteness`
  (Worker 249): `rationalDiscreteSeriesFixedOrbits` (Waldspurger's `Θ^H_G` for `G(F)`), and
  through its imports `GroupScheme.rationalPoints`, `rationalPointTopology`,
  `rationalPoints_nonarchimedeanGroup`, `GroupScheme.rationalPoints.map`,
  `IsConnectedReductive`, `IsSplitComponent`, `IsSplitComponent.isCentralSplitTorus`,
  `IsCentralSplitTorus.isCentral`, `IsCentral.range_le_center`;
- `Langlands.GroupScheme.Dynamic.CentralizerReductiveProof`: `dynamicCentralizerReductive`
  (the proof of `DynamicCentralizerReductiveStatement`);
- `Langlands.GroupScheme.Dynamic.AffineRepresentability`: the actual closed representative
  `Dynamic.Affine.centralizerHom χ : Dynamic.Affine.centralizerScheme χ ⟶ G` of the centralizer
  `Z_G(χ)`, with `isClosedSubgroup_centralizerHom` and `isRepresentedBy_centralizerHom`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`). Printed page numbers; the
PDF page is the printed page minus 234.

The passages below are those quoted in the Library's `RationalDiscreteSeriesOrbitFiniteness.md`
(Worker 249). The present author could not open the PDF in this session and relies on these
quotations.

- I.1, printed pp. 238–239: "On note `F` un corps local non archimédien de corps résiduel fini
  `F_q`. [...] Soit `G` un groupe linéaire algébrique réductif et connexe." and, for a
  semi-standard Levi subgroup `M` (in particular `M = G`), "on note `A_M` le plus grand tore
  déployé dans le centre de `M`". On printed p. 239: "On pose `G¹ = ⋂_{χ ∈ Rat(G)} Ker |χ|_F`,
  `X(G) = Hom(G/G¹, ℂ*)`" and "On pose `Im X(G) = {χ ∈ X(G); Re(χ) = 0}`. C'est le
  sous-ensemble des éléments unitaires de `X(G)`."
- VIII.1, printed p. 321: "Notons `Θ_G` l'ensemble des orbites dans `E₂(G)` pour l'action de
  `Im X(G)`. [...] Soit `H` un sous-groupe ouvert compact de `G`. [...] On note `Θ^H` l'ensemble
  des `(O, P)` tels que cette propriété soit vérifiée pour un (ou pour tout) `(ω, E) ∈ O`. On pose
  `Θ^H_G = Θ_G ∩ Θ^H`." Then "Théorème VIII.1.2. Pour tout sous-groupe ouvert compact `H` de `G`,
  `Θ^H_G` est fini."

Here `E₂(G)` is the set of classes of irreducible representations of `G` square integrable modulo
`A_G` (III.1), and the elided property in the definition of `Θ^H` is that the representation has
a nonzero `H`-fixed vector (as the Library's `RationalDiscreteSeriesOrbitFiniteness.md`
records). Waldspurger uses Theorem VIII.1.2 for the Levi subgroups of `G` as well: Remark
VIII.1.3 (printed p. 321) deduces the finiteness of `Θ^H` from it by induction.

## The statement

`RationalDiscreteSeriesOrbitFinitenessStatement.{u, uV}` (a `Prop`) asserts:

for every nonarchimedean local field `F : Type u` (`[IsNonarchimedeanLocalField F]`, any
characteristic), every group scheme `G` over `Spec F` with `[IsAffine G.X.left]` and
`[LocallyOfFiniteType G.X.hom]` that is connected reductive (`IsConnectedReductive G`; no split
or quasi-split hypothesis), every commutative group scheme `T` and split component
`s : T.toGrp ⟶ G` (`IsSplitComponent s`), with

- `G(F) = rationalPoints G` carrying the canonical topology `rationalPointTopology F G.X` and the
  Library's nonarchimedean-group structure `rationalPoints_nonarchimedeanGroup G`,
- `A_G(F) = (rationalPoints.map s).range`, central and hence normal
  (`Subgroup.normal_of_le_center`),
- the Borel measurable structure on the quotient `G(F) ⧸ A_G(F)`,

every Haar measure `mu` on `G(F) ⧸ A_G(F)` and every subgroup `H` of `G(F)` that is open and
compact, the set

`rationalDiscreteSeriesFixedOrbits.{u, uV} G s mu _ H`

is finite.

`rationalDiscreteSeriesFixedOrbits G s mu _ H` (defined in `RationalDiscreteSeriesOrbitFiniteness`)
is the set of orbits, under twisting by the unitary unramified characters of `G(F)` (the Library's
`unitaryUnramifiedCharacters` of the rational norm characters `|ψ|_F`, `ψ ∈ Rat(G)`: the source's
`Im X(G)`), of discrete-series classes of `G(F)` modulo `A_G(F)` with respect to `mu` (irreducible
admissible classes, on carriers in the universe `uV`, with a unitary central character on `A_G(F)`
and square-integrable coefficients on `G(F)/A_G(F)`; the Library's `DiscreteSeriesClass`) that
contain a class with a nonzero `H`-fixed vector. This is the source's `Θ^H_G`; the orbit structure
makes the statement the finiteness of twist orbits, not of the individual classes.

### Correspondence with the source

- `G`, `F`: the source's connected reductive group and nonarchimedean local field with finite
  residue field, of arbitrary characteristic.
- `A_G`: the source's largest split torus in the centre, given by any split component `s`
  (`IsSplitComponent s`); the statement quantifies over every such `s`.
- Haar measures: the source's discrete series do not depend on the choice of Haar measure; the
  statement quantifies over every Haar measure `mu` on `G(F)/A_G(F)`.
- `H`: the source's compact open subgroup, as a `Subgroup` with `IsOpen` and `IsCompact`.
- Carriers: representations act on complex vector spaces in an arbitrary universe `uV`,
  independent of the field universe `u`.

### Levi subgroups

The statement quantifies over all connected reductive `G`, so it applies to every actual Levi
subgroup that is realized as a connected reductive group scheme over `F`. For the Levi
subgroups `Z_G(χ)` of the dynamic parabolic subgroups `P_G(χ)` (`χ` a cocharacter), the module
proves:

- `isConnectedReductive_centralizerScheme`: for a field `k`, a group scheme `G` over `Spec k`
  with `[IsAffine G.X.left]` and `IsConnectedReductive G`, and a cocharacter
  `χ : Gm ⟶ G`, the actual centralizer scheme `Dynamic.Affine.centralizerScheme χ` is connected
  reductive. Proof: the Library's `dynamicCentralizerReductive` applied to its closed
  representative `Dynamic.Affine.centralizerHom χ` (`isClosedSubgroup_centralizerHom`,
  `isRepresentedBy_centralizerHom`).

The affineness and finite-type instances needed to apply the statement to
`Dynamic.Affine.centralizerScheme χ` follow from the closed immersion
`Dynamic.Affine.centralizerHom χ` into `G` (as in the Library's
`DynamicOppositeStandardIntertwining`); this module does not restate them.

## Status and relation to the Library

This is a statement target; it is not proved here. The Library reduces it to the finite
dimensionality of `p_χ(°C_H)` (Waldspurger's Proposition VIII.4.1 with Theorem VIII.4.2):
`finite_rationalDiscreteSeriesFixedOrbits_of_finiteDimensional` proves the finiteness of
`Θ^H_G` for `G(F)` from a finite-dimensional space containing the `H`-bi-invariant coefficients of
the discrete series with central character `χ` on `A_G(F)` (for every continuous unitary `χ`
trivial on `A_G(F) ∩ H`), and `finite_rationalDiscreteSeriesFixedOrbits_of_finite_central` proves
it from the finiteness of the sets `E₂(G)^H_χ`. Neither input is proved for actual groups in the
Library. This statement is the exact target for a later proof, either through Waldspurger's route
(VIII.4.1, VIII.4.2, which use Theorem VII.2.5) or through a verified alternative route.
