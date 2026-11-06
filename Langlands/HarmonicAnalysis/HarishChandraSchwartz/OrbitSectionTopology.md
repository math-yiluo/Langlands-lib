# The topology of the space `C^∞(O,P)` of smooth sections over a unitary orbit (Waldspurger, VI.3)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionTopology`. The
torus helpers are in namespace `Langlands.HarmonicAnalysis.TorusFourier`, the rest in
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.Representation.Plancherel.ProductInducedOrbitCompactAction` (Worker 200): the
  action `productInducedOrbitRepresentation` of `G × G` on orbit sections, the compact
  restriction `productInducedSmoothOrbitCompactRestriction` (written `R` below) with
  `productInducedSmoothOrbitCompactRestriction_injective`,
  `productInducedOrbitRepresentation_restriction` (`R` intertwines the action of `K × K` with
  `productInducedCompactRepresentation`), and
  `productInducedSmoothOrbitSections_exists_product_stabilizer`; through its imports the space
  `productInducedSmoothOrbitSections` of smooth orbit sections (`C^∞(O,P)` of VI.1), the
  compact picture `ProductInducedCompactPicture h K π.obj` (`L_K(ω,P)`),
  `productInducedFamilyRestriction`, `productInducedOrbitPullback`, the submodule
  `finiteSmoothFamilies` with `mem_finiteSmoothFamilies_iff` and
  `mem_finiteSmoothFamilies_linearMap`, the subalgebra `smoothFiniteTorusFunctions`, and the
  smoothness predicate `IsSmoothFiniteTorusFunction f` (`f ∘ finiteTorusExp` is `C^∞` on
  `J → ℝ`, with `finiteTorusExp θ = (e^{iθ_j})_j`);
- `Langlands.HarmonicAnalysis.TorusFourierDecay` (Worker 249): the angle derivative
  `torusPartialDeriv j f z = d/dθ f(z · e^{iθ}_j)` at `θ = 0`, `hasDerivAt_torusTranslate` and
  `isSmoothFiniteTorusFunction_torusPartialDeriv`;
- `Langlands.HarmonicAnalysis.TorusFourierSynthesis` (Worker 249): the iterated derivative
  `torusPartialDerivList l = ∂_{j₁} ∘ ⋯ ∘ ∂_{jₖ}` along a list `l = [j₁, …, jₖ]`;
- from Mathlib: `SeminormFamily.moduleFilterBasis`, `WithSeminorms` with
  `WithSeminorms.continuous_of_continuous_comp`, `norm_withSeminorms`,
  `isTopologicalAddGroup_sInf`, `continuousSMul_sInf`, `LocallyConvexSpace.sInf`,
  `LocallyConvexSpace.induced`, `T2Space.of_injective_continuous`,
  `Module.forall_dual_apply_eq_zero_iff` and `ContinuousMap.norm_le`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234.

VI.3, printed p. 301 (PDF p. 67): "On munit `C^∞(Im X(M))` de sa topologie usuelle. Fixons
provisoirement `(ω, E) ∈ O`. Pour tout sous-groupe ouvert compact `H` de `K`, l'espace des
invariants `L_K(ω,P)^{H×H}` est de dimension finie, donc muni d'une topologie canonique.
L'espace `C^∞(Im X(M)) ⊗_ℂ L_K(ω,P)^{H×H}` est muni de la topologie produit. Grâce à la
description donnée en VI.1, son sous-espace `C^∞(O,P)^{H×H}` se retrouve muni d'une
topologie. On munit `C^∞(O,P)` de la topologie limite inductive des topologies de ces
sous-espaces quand `H` décrit l'ensemble des sous-groupes ouverts compacts de `K`."

The description of VI.1 (printed pp. 295–296) is the Library's compact restriction `R`: a
smooth orbit section `q` gives the family `z ↦ R q z` in the compact picture over the
coordinate torus `J → Circle` of `Im X(M)` (coordinates `e`), and `R q` is a finite sum
`∑ᵢ fᵢ(z) vᵢ` with smooth scalar `fᵢ` (`finiteSmoothFamilies`).

How the Lean construction renders the paragraph:

- The level `C^∞(O,P)^{H×H}` is `OrbitSectionLevel … H`, the smooth orbit sections fixed by
  `productInducedOrbitRepresentation` of every element of `H × H`.
- Its topology is the topology of the seminorms
  `q ↦ sup_{z ∈ J → Circle} |∂_l (ℓ ∘ R q)(z)|`, for all lists `l` of coordinate directions
  and all linear functionals `ℓ` (algebraic dual) on the whole compact picture `L_K`. The same
  family of seminorms is used for every level.
- `C^∞(O,P)` is `OrbitSectionSpace`, with the locally convex inductive-limit topology over the
  open subgroups `H` of `G` with `H ≤ K` (since `K` is compact, these are the compact open
  subgroups of `K`). VI.3 says "topologie limite inductive" without further specification; the
  module uses the locally convex inductive limit, the convention of III.6 for `C(G)` in
  `Langlands.HarmonicAnalysis.HarishChandraSchwartz.Basic`, and builds it the same way (Mathlib's
  construction of the LF topology on test functions). The final topology of the inclusions,
  `originalTop`, which is the inductive limit in topological spaces, is also defined; it is
  finer (`originalTop_le`).

What is not formalized: Waldspurger's level topology is the product topology on
`C^∞(Im X(M)) ⊗ L_K(ω,P)^{H×H}` for the finite-dimensional space `L_K(ω,P)^{H×H}`, restricted
to the subspace. The module does not prove that its seminorm topology on the level coincides
with that topology. The comparison needs the finite dimensionality of `L_K(ω,P)^{H×H}`, which
is not proved here (it comes from the admissibility of the induced representation), and the
commutation of the partial derivatives `∂_j` (the seminorms are indexed by ordered lists rather
than multi-indices), which is not proved here either. The module proves the remaining
ingredient: for `H ≤ K` and `q` in the level, `R q z` lies in the `H × H`-invariants of the
compact picture (`productInducedCompactRepresentation_orbitSectionCompactRestriction`). Given
these facts the comparison is the usual one: coordinate functionals of a basis of
`L_K(ω,P)^{H×H}` extend to functionals on `L_K(ω,P)`, and each functional restricted to the
invariants is a finite combination of them. The "usual topology" of `C^∞(Im X(M))` is read in
the coordinates `e` and the angle derivatives `torusPartialDeriv`.

The helpers in namespace `Langlands.HarmonicAnalysis.TorusFourier`
(`isSmoothFiniteTorusFunction_of_mem_finiteSmoothFamilies`, `smoothTorusToContinuousMap`,
`hasDerivAt_torusTranslate_zero`, `torusPartialDeriv_add`, `torusPartialDeriv_smul`,
`torusPartialDerivLinear`, `torusPartialDerivListLinear`), the coefficient and derivative maps
`orbitSectionCoefficient`, `orbitSectionDerivative`, the inclusion maps, the type synonyms and
the instances are derived constructions used to state the topology; they are not statements of
the paper.

## Scope and hypotheses

Namespace `Langlands.HarmonicAnalysis.TorusFourier`: a finite type `J`; `[DecidableEq J]` for
`hasDerivAt_torusTranslate_zero`, `torusPartialDeriv_add`, `torusPartialDeriv_smul`,
`torusPartialDerivLinear`, `torusPartialDerivListLinear` and
`torusPartialDerivListLinear_apply`.

Namespace `Langlands.HarishChandraSchwartz` (the variables of
`productInducedSmoothOrbitSections`): a group `G` with a topology, `[LocallyCompactSpace G]`,
`[NonarchimedeanGroup G]`; subgroups `P`, `M`, `U` of `G` with
`h : IsSemidirectDecomposition P M U`, `hU : IsClosed U`, `hP : IsClosed P`,
`hr : Continuous h.projection`; a type `I` with `ν : I → (M →* ℝ≥0ˣ)` and
`hν : ∀ i, Continuous (ν i)`; `π : IrreducibleAdmissibleRep ℂ M`; a finite type `J` with
`[DecidableEq J]` and torus coordinates `e : unitaryUnramifiedCharacters ν ≃* (J → Circle)`;
an open subgroup `K` with `hK : IsCompact K` and `hPK : ∀ g, ∃ p : P, ∃ k : K, g = p k`. No
continuity of `e` is assumed. The results whose statements do not involve derivatives omit
`[DecidableEq J]`. Further hypotheses of individual results:

- `orbitSectionSeminorm_le_iff`: a real `C` with `hC : 0 ≤ C`;
- `orbitSectionLevelSubmodule_antitone` and `OrbitSectionLevel.inclusion`,
  `toSections_comp_inclusion`, `continuous_inclusion`: open subgroups `H' ≤ H`;
- `productInducedCompactRepresentation_orbitSectionCompactRestriction`: an open subgroup `H`
  with `hHK : H ≤ K`, a smooth orbit section `q` in the level of `H`, `x ∈ H × H`, `z`;
- `OrbitSectionSpace.continuous_iff_continuous_comp`, `mkCLM`, `coe_mkCLM`: a complex vector
  space `V` that is also a real vector space with `[IsScalarTower ℝ ℂ V]`, a topology with
  `[IsTopologicalAddGroup V]`, `[ContinuousSMul ℂ V]` and `[LocallyConvexSpace ℝ V]`, and a
  complex-linear `T : OrbitSectionSpace … → V` (for `mkCLM`, with the continuity of every
  `T ∘ ofLevel H`, `H ≤ K`).

## Definitions

Namespace `Langlands.HarmonicAnalysis.TorusFourier`:

- `smoothTorusToContinuousMap : smoothFiniteTorusFunctions J →ₗ[ℂ] C(J → Circle, ℂ)`, the
  inclusion of the smooth functions into the continuous functions (sup norm).
- `torusPartialDerivLinear j`: `∂_j` as a linear endomorphism of `smoothFiniteTorusFunctions J`.
- `torusPartialDerivListLinear l`: `∂_{j₁} ∘ ⋯ ∘ ∂_{jₖ}` as a linear endomorphism, for
  `l = [j₁, …, jₖ]`.

Namespace `Langlands.HarishChandraSchwartz`:

- `orbitSectionCoefficient … ℓ : C^∞(O,P) →ₗ[ℂ] smoothFiniteTorusFunctions J`,
  `q ↦ (z ↦ ℓ(R q z))`, for `ℓ : Module.Dual ℂ (ProductInducedCompactPicture h K π.obj)`.
- `orbitSectionDerivative … l ℓ : C^∞(O,P) →ₗ[ℂ] C(J → Circle, ℂ)`,
  `q ↦ ∂_l (ℓ ∘ R q)`.
- `orbitSectionSeminorm … (l, ℓ)`, the seminorm `q ↦ ‖∂_l (ℓ ∘ R q)‖ = sup_z |∂_l (ℓ ∘ R q)(z)|`.
- `orbitSectionLevelSubmodule … H`, the submodule of orbit sections that are smooth and fixed by
  every element of `H × H` (`Representation.invariants` of the restriction of
  `productInducedOrbitRepresentation` to `H × H`).
- `OrbitSectionLevel … H` (the level `C^∞(O,P)^{H×H}`) and `OrbitSectionSpace …` (the space
  `C^∞(O,P)`), type synonyms of `orbitSectionLevelSubmodule … H` and
  `productInducedSmoothOrbitSections …`, with their additive group and module structures.
- `OrbitSectionLevel.toSections H`, the inclusion of the level into `C^∞(O,P)`;
  `OrbitSectionLevel.seminormFamily H`, the seminorms `orbitSectionSeminorm (l, ℓ)` restricted
  to the level; `OrbitSectionLevel.topologicalSpace H`, the topology they define (instance);
  `OrbitSectionLevel.inclusion H hHH'`, the inclusion of the level of `H` into the level of
  `H' ≤ H`.
- `OrbitSectionSpace.toSections`, the identity of `C^∞(O,P)` viewed as a linear map to
  `productInducedSmoothOrbitSections`; `OrbitSectionSpace.ofLevel H`, the inclusion of the level
  of `H`; `OrbitSectionSpace.originalTop`, the supremum over `H ≤ K` of the coinduced
  topologies (the final topology of the inclusions); `OrbitSectionSpace.topologicalSpace`
  (instance), the `sInf` of all topologies coarser than `originalTop` that make
  `OrbitSectionSpace` a topological additive group with continuous complex scalar
  multiplication, locally convex over `ℝ`; `OrbitSectionSpace.ofLevelCLM H` (`H ≤ K`), the
  inclusion as a continuous linear map; `OrbitSectionSpace.mkCLM T hT`, a continuous linear map
  from a linear map continuous on every level.

## Results

Namespace `Langlands.HarmonicAnalysis.TorusFourier`:

- `isSmoothFiniteTorusFunction_of_mem_finiteSmoothFamilies`: every `F ∈ finiteSmoothFamilies J ℂ`
  is smooth.
- `smoothTorusToContinuousMap_apply`, `torusPartialDerivListLinear_apply`: the defining formulas
  (`(torusPartialDerivListLinear l f).val = torusPartialDerivList l f.val`).
- `hasDerivAt_torusTranslate_zero`: for smooth `f`, `θ ↦ f(z · e^{iθ}_j)` has derivative
  `torusPartialDeriv j f z` at `θ = 0`.
- `torusPartialDeriv_add`, `torusPartialDeriv_smul`: `∂_j` is additive and complex-homogeneous
  on smooth functions.

Namespace `Langlands.HarishChandraSchwartz`:

- `orbitSectionCoefficient_apply`, `orbitSectionDerivative_apply`
  (`orbitSectionDerivative l ℓ q z = torusPartialDerivList l (y ↦ ℓ(R q y)) z`),
  `orbitSectionSeminorm_apply`: the defining formulas.
- `norm_torusPartialDerivList_le_orbitSectionSeminorm`:
  `|∂_l (ℓ ∘ R q)(z)| ≤ orbitSectionSeminorm (l, ℓ) q` for every `z`.
- `orbitSectionSeminorm_le_iff`: for `C ≥ 0`, `orbitSectionSeminorm (l, ℓ) q ≤ C` if and only if
  `|∂_l (ℓ ∘ R q)(z)| ≤ C` for every `z`.
- `eq_zero_of_forall_orbitSectionDerivative_nil`: if `ℓ ∘ R q = 0` for every `ℓ`, then `q = 0`.
- `mem_orbitSectionLevelSubmodule_iff`: membership in the level is smoothness together with
  invariance under every `x ∈ H × H`; `orbitSectionLevelSubmodule_le`: the level consists of
  smooth sections; `orbitSectionLevelSubmodule_antitone`: for `H' ≤ H` the level of `H` is
  contained in the level of `H'`.
- `exists_mem_orbitSectionLevelSubmodule`: every smooth orbit section lies in the level of some
  open subgroup `H ≤ K`, so `C^∞(O,P)` is the union of the levels (`OrbitSectionSpace.exists_ofLevel`).
- `productInducedCompactRepresentation_orbitSectionCompactRestriction`: for `H ≤ K`, `q` in the
  level of `H`, `x ∈ H × H` and `z`,
  `productInducedCompactRepresentation h K π.obj x (R q z) = R q z`.
- `OrbitSectionLevel`: `toSections_injective`; `withSeminorms` (the topology of the level is the
  topology of `seminormFamily`); instances `IsTopologicalAddGroup`, `ContinuousSMul ℂ`,
  `LocallyConvexSpace ℝ` and `T2Space`; `continuous_orbitSectionDerivative`: each
  `q ↦ ∂_l (ℓ ∘ R q) ∈ C(J → Circle, ℂ)` (sup norm) is continuous on the level;
  `toSections_comp_inclusion`, `continuous_inclusion`: for `H' ≤ H` the inclusion of levels is
  continuous.
- `OrbitSectionSpace`: `toSections_ofLevel`, `exists_ofLevel`; instances
  `IsTopologicalAddGroup`, `ContinuousSMul ℂ`, `LocallyConvexSpace ℝ` and `T2Space`;
  `originalTop_le`; `topologicalSpace_le_iff` (a locally convex vector space topology is
  coarser than the topology of `C^∞(O,P)` if and only if it is coarser than `originalTop`);
  `continuous_ofLevel` (every inclusion of a level `H ≤ K` is continuous);
  `continuous_iff_continuous_comp`: a complex-linear map `T` from `C^∞(O,P)` to a locally convex
  space `V` as in the hypotheses is continuous if and only if `T ∘ ofLevel H` is continuous for
  every open `H ≤ K` (the universal property of the locally convex inductive limit, the analogue
  for `C^∞(O,P)` of III.6(1) for `C(G)`); `coe_mkCLM`; `continuous_orbitSectionDerivative` and
  `continuous_orbitSectionSeminorm`: every derivative map and every seminorm is continuous on
  `C^∞(O,P)`.

## Proof notes

1. `isSmoothFiniteTorusFunction_of_mem_finiteSmoothFamilies`: by
   `mem_finiteSmoothFamilies_iff`, `F = ∑ᵢ fᵢ vᵢ` with `fᵢ` smooth and `vᵢ ∈ ℂ`, an element of the
   subalgebra `smoothFiniteTorusFunctions`.
2. `torusPartialDeriv_add`, `torusPartialDeriv_smul`: `hasDerivAt_torusTranslate` at `θ = 0`
   (`hasDerivAt_torusTranslate_zero`) and `HasDerivAt.add`, `HasDerivAt.const_mul`.
   `torusPartialDerivListLinear_apply` by induction on the list.
3. `orbitSectionCoefficient` lands in the smooth functions by
   `mem_finiteSmoothFamilies_linearMap` (applied to `ℓ`) and step 1; it is linear because `R`
   and `ℓ` are.
4. `orbitSectionSeminorm_le_iff`: `ContinuousMap.norm_le`. `eq_zero_of_forall_…`: by
   `productInducedSmoothOrbitCompactRestriction_injective` it suffices that `R q z = 0` for every
   `z`, which follows from `Module.forall_dual_apply_eq_zero_iff`.
5. `exists_mem_orbitSectionLevelSubmodule` is
   `productInducedSmoothOrbitSections_exists_product_stabilizer`.
   `productInducedCompactRepresentation_orbitSectionCompactRestriction` is
   `productInducedOrbitRepresentation_restriction` for `x` viewed in `K × K`, together with the
   invariance `x · q = q`.
6. The level topology: `SeminormFamily.moduleFilterBasis.topology`, so `WithSeminorms` holds by
   definition and gives the group, scalar-multiplication and local-convexity instances.
   Continuity of `∂_l (ℓ ∘ R ·)` and of the inclusions:
   `WithSeminorms.continuous_of_continuous_comp` (with `norm_withSeminorms` for the target
   `C(J → Circle, ℂ)`), because each seminorm of the target composed with the map is a seminorm of
   the family. `T2Space`: `q ↦ (ℓ ↦ ℓ ∘ R q)` is continuous into a product of Hausdorff spaces
   and injective by step 4 (`T2Space.of_injective_continuous`).
7. The inductive-limit topology follows `HarishChandraSchwartz.Basic` line by line: the `sInf`
   instances (`isTopologicalAddGroup_sInf`, `continuousSMul_sInf`, `LocallyConvexSpace.sInf`),
   `topologicalSpace_le_iff` by `sInf_le`, and `continuous_iff_continuous_comp` by
   `continuous_iff_le_induced` applied to the induced topology of `T`, which is again a locally
   convex vector-space topology (`isTopologicalAddGroup_induced`, `continuousSMul_induced`,
   `LocallyConvexSpace.induced` for `T` restricted to `ℝ`), and `continuous_coinduced_dom`.
   Continuity of `∂_l (ℓ ∘ R ·)` on `C^∞(O,P)` is then `continuous_iff_continuous_comp` with
   step 6, and `T2Space` is as in step 6.
