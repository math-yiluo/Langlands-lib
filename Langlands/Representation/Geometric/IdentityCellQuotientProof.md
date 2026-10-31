# Proof of the identity-cell quotient of the normalized geometric lemma

Author: Worker 787.

`Langlands.Geometric.padicIdentityCellQuotientTheorem.{uF,uV}` proves exactly the
published proposition `Langlands.Geometric.PadicIdentityCellQuotientTheorem.{uF,uV}`
from `Langlands.Representation.Geometric.IdentityCellQuotientStatement`. The theorem's
type is that proposition. Its level parameters are `uF` and `uV`, kept independent, and
it has no hypotheses beyond those in the statement. The statement pair and every
published pair it imports are unchanged. The theorem depends only on the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

The conclusion is the statement's conclusion. For every prime `p`, finite p-adic field
`F`, compatible topology `T`, positive rank `n`, block shapes `B`, `C`, and identity
refinements `S`, `R` with `hS`, `hR`, the theorem gives a natural transformation
`η : jacquetInductionFunctor T B C ⟶ geometricPieceFunctor T B C 1 S R hS.2.1 hR.2.1`.
For every smooth representation `A`, the component `(η.app A).hom` is surjective. The
proof adds no admissibility, finite-length, irreducibility or cuspidality premise.

## Mathematical route

The proof follows Zelevinsky's derivation of Corollary 1.3. It orders the
`P_C`-orbits on `P_B \ GL_n(F)` under the right action so that every initial union is open and the
closed identity orbit `P_B \ P_B P_C` comes last. The top successive quotient of the
support filtration is then the identity piece. The quotient map from the whole functor
onto that top piece is the required surjection.

The published `PadicGeometricLemmaTheorem` alone does not give this. Its `IsGluedFrom`
filtration uses an unspecified order. The proof therefore reruns the support-filtration
construction with an explicit order. It uses the published graded-piece theorem
`PadicParabolicSupportGradedTheorem` and does not reprove it.

## Auxiliary declarations

The module adds these declarations:

| Declaration | Content |
| --- | --- |
| `Langlands.RepSubfunctor.fromFull` | If a subfunctor `S` of `F` is `⊤` at every object, then `F ⟶ S.toFunctor`, given by `v ↦ ⟨v, _⟩` at each object. |
| `Langlands.RepSubfunctor.fromFull_surjective` | Every component of `fromFull` is surjective. |
| `Langlands.RepFunctorFiltration.lastGradedProjection` | For a filtration `s` and an index `i` with `i.succ = Fin.last n`: `fromFull` of `s.step i.succ`, which is `⊤` by `s.top`, followed by `quotientNatProjection`. This is a map `F ⟶ s.graded i`. |
| `Langlands.RepFunctorFiltration.lastGradedProjection_surjective` | Every component of that map is surjective, by `quotientProjection_surjective` and `fromFull_surjective`. |
| `Langlands.surjective_app_comp_iso_hom` | Following a natural transformation with surjective components by a natural isomorphism keeps the components surjective. |
| `Langlands.Geometric.cosetOrbit_one_eq_image` | `cosetOrbit P_B P_C 1` is the image in `P_B \ GL_n(F)` of `P_C ∩ GL_n(O)`. |
| `Langlands.Geometric.isClosed_cosetOrbit_one` | `cosetOrbit P_B P_C 1` is closed in `P_B \ GL_n(F)`. |
| `Langlands.Geometric.identityRepresentative` | The identity permutation as an element of `MinimalRepresentatives B C`. |
| `Langlands.Geometric.geometricPieceFunctor_refinement_congr` | Equal refinements give the same `geometricPieceFunctor`, for any equality witnesses. |

`identityRepresentative` uses `index_strictMono` from `WeylMinimalRepresentativeProof`:
the identity permutation is strictly monotone on every block of `B` and of `C`.

### The identity orbit is closed

Here `P = B.parabolic F` and `Q = C.parabolic F`. The library defines `cosetOrbit P Q w`
as the set of cosets `P (w⁻¹ q)` with `q ∈ Q`, so for `w = 1` it is the image of `Q`.
For `q ∈ Q`, `Iwasawa.exists_mul_upperTriangular` gives an integral `k ∈ GL_n(O)` with
`q k` upper triangular. Upper-triangular matrices lie in every standard block parabolic
(`mem_parabolic_of_isUpperTriangular`), so `q k ∈ P ∩ Q`. Hence `k ∈ Q` and
`P q = P k⁻¹`, with `k⁻¹ ∈ Q ∩ GL_n(O)`. Conversely, every element of
`Q ∩ GL_n(O)` lies in `Q`. This proves `cosetOrbit_one_eq_image`.

`Parabolic.isCompact_integralRange` shows that `GL_n(O)` is compact. Its intersection
with the closed subgroup `Q` (`isClosed_parabolic`) is compact. The continuous quotient
map sends it to a compact set. `P \ GL_n(F)` is Hausdorff because `P` is closed
(`QuotientIntegration.leftQuotient_t2Space`), so this compact set is closed.

### Main proof

1. The proof installs the field topology, valuative relation and local-field structure,
   and the nonarchimedean, locally compact, Hausdorff and sigma-compact structures on
   `GL_n(F)`.
2. `padicParabolicBruhat` makes `parabolicDoubleCoset F B C` a bijection from
   `MinimalRepresentatives B C`. Hence there are finitely many double cosets.
3. `closedSubgroupOrbitOrdering_of_finiteOrbitOrdering`, applied to the proved
   `Langlands.Topology.finiteOrbitOrdering`, gives an ordered decomposition
   `s : OrderedDoubleCosets P Q m`.
4. `OrderedDoubleCosets.exists_openCut` is applied to the open complement of
   `cosetOrbit P Q 1`. The predicate marks the indices `i` whose double coset
   `P (s.representative i)⁻¹ Q` differs from `P 1⁻¹ Q`. `quotientMap_mem_cosetOrbit_iff` verifies that a point of orbit `i` lies in
   the complement exactly when index `i` is marked. The result is a reordering
   `t : OrderedDoubleCosets P Q (a + b)` whose first `a` orbits have union equal to the
   complement.
5. Disjointness of the orbits of `t` gives `htail`: the double coset of the `i`-th
   representative of `t` is the identity double coset exactly when `a ≤ i`.
6. `minimalPermutationOrdering B C t hBruhat` gives an equivalence
   `e : Fin (a + b) ≃ MinimalRepresentatives B C`. It also gives a decomposition `u`
   with the same orbits whose representatives are the permutation matrices of `e i`.
   The identity
   `(Equiv.ofBijective _ hBruhat).apply_symm_apply (t.doubleCosetEquiv i)` shows that
   `parabolicDoubleCoset (e i)` is the double coset of the `i`-th representative of `t`.
   Because `parabolicDoubleCoset` is injective, `e i = identityRepresentative` exactly
   when `a ≤ i`. Since `e` is surjective, `b ≥ 1`. So the last index
   `i = a + b - 1`, with `i.succ = Fin.last (a + b)`, satisfies `e i = 1`.
7. `padicStandardIntersectionsTheorem` chooses refinements `S₀ w` and `R₀ w`, with
   their intersection witnesses, for every minimal permutation `w`. The families `S'`
   and `R'` take the given `S` and `R` at the identity and `S₀ w`, `R₀ w` elsewhere.
   Their witnesses come from `hS`, `hR` and the chosen ones. This satisfies the
   hypotheses of the graded theorem while using the supplied `S` and `R` at the
   identity.
8. `padicParabolicSupportGradedTheorem` applied to `e`, `u`, `S'`, `R'` gives a natural
   isomorphism `iso` from the `i`-th successive quotient of
   `parabolicJacquetSupportFiltration T B C u` to the geometric piece at `e i` with
   refinements `S' (e i)`, `R' (e i)`.
   `geometricPieceFunctor_refinement_congr` shows that this piece is
   `geometricPieceFunctor T B C 1 S R hS.2.1 hR.2.1`, since `e i = 1`, `S' 1 = S` and
   `R' 1 = R`. The proof first proves this for every `w` equal to the identity
   representative and then specializes to `e i`.
9. The witness is `η = lastGradedProjection i hi ≫ iso.hom`. Its components are
   surjective by `lastGradedProjection_surjective` and `surjective_app_comp_iso_hom`.

The filtration's source functor is `jacquetInductionFunctor T B C` by the definition of
`parabolicJacquetSupportFiltration`. Its last step is `⊤`, which is the `top` field of
`RepFunctorFiltration`.

## Source correspondence

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II*, Ann. Sci.
ENS 13 (1980), registered as `zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`. Corollary 1.3 is
on printed p. 171. It derives the quotient from Theorem 1.2 (printed p. 170). It orders
the orbits by Bernstein–Zelevinsky 1977, Theorem 5.2, with the closed coset
`P_β P_γ` last. I. N. Bernstein and A. V. Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), registered as `bernstein-zelevinsky-1977-induced-i`,
SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`: Theorem 5.2
is on printed p. 460, and the support subfunctors of 5.3–5.4 are on printed p. 461.

The proof differs from the sources in two places. The sources take closedness of the
identity coset as known. Here closedness comes from the Iwasawa factorization and compactness of
`GL_n(O)`, as described above. Zelevinsky gives a quotient for each representation.
Here the quotient is a single natural transformation, and it works for every pair of
identity refinements `S`, `R`. This is the derived form recorded in the statement's
Markdown.

## Dependency audit

The module's direct imports, as published in Library commit
`4c0ab0f3966f1a1836901963afb04dca21607ffb`, are listed below. Proved inputs name the
proof artifact and task that published them. Definition modules name their
definition artifact.

- `Geometric.IdentityCellQuotientStatement`: the target statement, artifact
  `cc17ce3e-9779-48f1-a877-dd12ba29ebe7`, task `704eb687-951c-4c3e-96f1-717ba6d80179`.
- `Geometric.ParabolicSupportGradedProof`: `padicParabolicSupportGradedTheorem`,
  artifact `62ae1acc-327e-447c-be32-7a11b79d8dd2`, task
  `1e160a16-f7f4-4d17-b9ee-4fd2e6e0fb34`. It is imported, not duplicated.
- `Geometric.PadicParabolicBruhatProof`: `padicParabolicBruhat`, artifact
  `66197c1e-5b06-4e40-beb3-58bb0d70ae1d`, task
  `b2c9fb09-d2c7-4895-8320-b447e3cc98c6`.
- `Geometric.StandardIntersectionsProof`: `padicStandardIntersectionsTheorem`, artifact
  `454f2f13-4e58-4601-a2a6-bc94e9c6b6a2`, task
  `5f658ba6-5c6d-46e0-a5c1-6d15317f8a1d`.
- `Geometric.WeylMinimalRepresentativeProof`: `index_strictMono`, artifact
  `be673197-862b-407d-a1a8-251a31419cda`, task
  `6e35399b-9029-438e-9663-5ce96ab02576`.
- `Topology.GroupAction.FiniteOrbitProof`: `Langlands.Topology.finiteOrbitOrdering`,
  artifact `d152e80f-831a-4f00-89d7-2ae3209d5c86`, task
  `72152240-c606-4fc3-87a0-e6d5972c32fa`.
- `Parabolic.QuotientCompactProof`: `Parabolic.isCompact_integralRange`, artifact
  `6e7b4c94-bf7d-4648-b410-d3c2c64ee631`, task
  `400d2277-4574-4aea-a50c-da70cb1702f2`.
- `Group.GL.CountabilityProof`: the sigma-compact instance on `GL_n(F)`, artifact
  `dd877404-a836-4910-a283-5e253b492da2`, task
  `67ebcf61-3d58-4499-9c0c-c847e90aaeb4`. Only this countability lemma is used, not the
  geometric lemma proved in that task.
- `Geometric.CosetOrbitOrdering`: `closedSubgroupOrbitOrdering_of_finiteOrbitOrdering`,
  definition artifact `a8dc116e-9481-4d5c-b25f-9e0bf5efb0dc`.
- `Geometric.OpenOrbitCut`: `OrderedDoubleCosets.exists_openCut`, definition artifact
  `ae0784fe-13b5-45b8-80f1-3e08e0a80ad6`.
- `Group.GL.CompactOpen`: the nonarchimedean structure on `GL_n(F)`, definition
  artifact `e921a8ad-efb0-42eb-adac-f64003b71ec6`.

The transitive imports also supply `minimalPermutationOrdering`,
`quotientMap_mem_cosetOrbit_iff` and `doubleCosetEquiv` (`Geometric.OrbitRepresentatives`,
artifact `d05fb744-4e65-4dfc-baec-dc03c851a1e8`), and `Iwasawa.exists_mul_upperTriangular`
(`Whittaker.Iwasawa`, artifact `e4518542-8a62-4515-a2a4-ef85a5d8e46e`). They supply
`mem_parabolic_of_isUpperTriangular` (`Group.GL.TriangularParabolic`), the quotient
topology lemmas (`Analysis.Local.QuotientTopology`), the filtration API
(`Filtration.Definitions`), and the support filtration
(`Geometric.ParabolicSupportFiltration`).

Independence check: the transitive `Langlands` import closure of the direct imports has
282 modules,
computed from the import lines at Library commit `4c0ab0f3`. It contains no module about
socles, segments, multisegments, derivatives, square-integrable or tempered
classification, or special heads. The only `Classification` modules are
`Supercuspidal`, `SupercuspidalTwist`, `SupercuspidalContragredientStatement` and
`SupercuspidalContragredientAux`. These hold basic supercuspidality definitions and
contragredient laws. They enter the closure through
`CuspidalSupport.LeviDefinitions`, `Parabolic.RefinementCharacter` and
`Smooth.SmallRealizationProof`. None of the excluded results appears in the closure:
`LinkedSegmentSocleReverseProductQuotientHom`,
`JuxtaposedSegmentSocleReverseProductStructure`,
`LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`,
`SegmentSocleProductIrreducibility`, `AdjacentUnlinkedSegmentSocleSwap`,
`TwoSegmentSocleCommutation`, `LinkedSegmentSocleGluing`,
`OrderedMultisegmentSocleExistence`, `SquareIntegrableLanglandsClassification`,
`SegmentHeadProductIrreducibility`, the socle and special-head exhaustion results,
segment analytic classification, quotient coverage, and tempered block uniqueness. The
proof uses no derivative work. It does not import or duplicate
`PadicParabolicOrbitJacquetComparison` directly; that comparison enters only through
the published graded-piece theorem. It does not duplicate `PadicGeometricLemmaTheorem`.

## Scope

The theorem holds for actual finite p-adic fields with their supplied compatible
topology and for positive rank, as in the statement. It gives only the quotient onto the
identity piece. It does not identify the other successive quotients and states nothing
about the kernel of `η`.
