# Mixed mirabolic two-orbit coverage and open-first ordering

Author: Worker 1012.

`Langlands.GeneralLinear.Mirabolic.MixedOrbit.MirabolicMixedOrbitCoverageStatement`
is a proposition definition. It asserts the two geometric orbit enumerations
from Bernstein–Zelevinsky (1977), §7.2, for 4.13(b),(c), at GL rank
`K = k+1 ≥ 1` and source mirabolic rank `m = r+2 ≥ 2`. It supplies no proof
of either enumeration. The published group data alone also supply no such proof.

## Complete type and hypotheses

The complete declaration type is

```lean
{p : ℕ} → [Fact p.Prime] →
  (F : Langlands.PadicField.{uF} p) → (T : F.TopologicalData) → Prop
```

There is only the field universe `uF`. No representation universe, character,
admissibility, finite-dimensional representation, or theorem hypothesis occurs.
Both sides quantify over every `k r : ℕ`, including `k = 0` and `r = 0`.
The positivity conditions are built into `K = k+1` and `m = r+2`.

The definition installs `letI := T.topology`. For each pair of ranks it
installs the published certificate `T.generalLinearTopologicalGroup (k+r+3)`
and its ordinary mirabolic subgroup instance. These are certificates for the
topology supplied in `T`, not additional premises or a choice of the canonical
topology. The general linear topology is the matrix-unit topology over
`T.topology`; the mirabolic and quotient topologies are the inherited ones.

## The actual groups and the asserted conjunction

Write `MixedOrbit` for
`Langlands.GeneralLinear.Mirabolic.MixedOrbit` and `Geometric` for
`Langlands.Geometric`. The total matrix rank is `n = k+r+3`, and

```text
G = GeneralLinear.mirabolic (k+r+2) F.Carrier = P_n
Q = GeneralLinear.Mirabolic.plusSubgroup (k+r+1) F.Carrier = P_(n-1) V_n.
```

The only direct import is
`Langlands.Group.GL.MirabolicMixedOrbitData`. Its Lean and Markdown are
unchanged. In particular, `leftInducing` and `rightInducing` retain their
actual rank transport from the published `leftSubgroup (k+1) (r+1)` and
`rightSubgroup (k+1) (r+1)`, via the explicit matrix reindexing `rankCast`
along `totalRank_eq k r`.

The proposition is exactly the conjunction of:

- For all `k r`, there exists
  `s : Geometric.OrderedDoubleCosets (leftInducing k r F.Carrier) Q 2`
  with `s.representative = leftRepresentative k r F.Carrier`.
- For all `k r`, there exists
  `s : Geometric.OrderedDoubleCosets (rightInducing k r F.Carrier) Q 2`
  with `s.representative = rightRepresentative k r F.Carrier`.

These equalities concern the complete functions `Fin 2 → G`. They fix both
indices, rather than merely specifying the set of representatives.

For either inducing subgroup `H`, the published `OrderedDoubleCosets` has
four fields:

| Field | Required content |
| --- | --- |
| `representative` | A function `Fin 2 → G`, fixed by the displayed equality. |
| `covers` | Every point of the actual left quotient `H \ G` belongs to `cosetOrbit H Q (s.representative i)` for some `i`. |
| `disjoint` | Distinct indices have disjoint actual `cosetOrbit` sets. |
| `initial_open` | For each `j : Fin 3`, the union of orbits with index less than `j` is open in `H \ G`. |

Coverage, disjointness and openness are conclusions inside the existential
witness. None is an added hypothesis. The initial unions at `j = 0, 1, 2`
are the empty set, the orbit at index `0`, and the whole quotient, respectively.
Thus the assertion requires the first orbit to be open. Together with
coverage and disjointness, this identifies the second orbit as its closed
complement. Both specified orbits are nonempty by the definition of
`cosetOrbit`, using the identity element of `Q`. No orbit property is proved
in this file.

## Source correspondence and orientation

Original: I. N. Bernstein and A. V. Zelevinsky, *Induced representations of
reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472.
Registered source ID: `bernstein-zelevinsky-1977-induced-i`.
Retained PDF:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
SHA256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

The text and page image of §7.2, printed p.471 (one-based PDF p.32), were
read. The definitions and diagrams of §4.12(II),(III), printed pp.456–458
(PDF pp.17–19), were also read and visually inspected. A bounded search of
the supplied literature and project/Library note filenames found no
BZ77-specific erratum; the usual `notes/errata` paths were absent. This
records the extent of that search, not a global absence claim.

In the two-orbit case of 4.13(b), the source takes `G = P_n`, the mixed
subgroup `P = MU` of 4.12(II), and `N = P_(n-1)`, `V = V_n`. It describes
the closed orbit of `P e` and the open orbit of `P w₀⁻¹`, with the descending
cycle starting at its GL rank `K`. For 4.13(c), it uses 4.12(III) and the
descending cycle starting at `m-1`. The source's `P` is our inducing subgroup
`H`; its right acting group is our `Q`.

The published matrix convention is `w₀ e_j = e_(σ j)`. In zero-based indices,
the two source cycles are

| Case | One-based cycle | Published representative at `0` |
| --- | --- | --- |
| 4.13(b), 4.12(II) | `K ↦ n-1 ↦ n-2 ↦ … ↦ K` | `leftCycleElement k r F.Carrier`, from `descendingCycle (k+r+1) k _` |
| 4.13(c), 4.12(III) | `m-1 ↦ n-1 ↦ n-2 ↦ … ↦ m-1` | `rightCycleElement k r F.Carrier`, from `descendingCycle (k+r+1) r _` |

Both cycles fix the final coordinate `k+r+2`. Both published representative
functions are `![cycleElement, 1]`. The published convention
`cosetOrbit H Q w = range (fun q : Q => H (w⁻¹ * q))` therefore puts the
source's open-orbit point `H w₀⁻¹` at index `0` and `H e` at index `1`.
The inverse in the quotient point does not replace the representative
matrix by its inverse. The source does not itself specify a permutation
matrix convention; this statement uses exactly the convention fixed and
explained by the published data pair.

The existential `OrderedDoubleCosets` packaging and the conjunction of the
two cases are internal translations of this geometric source assertion.
They are not a claim that BZ77 uses these Lean structures. The initial-union
form expresses the open-first order of the two complementary orbits. No
coefficient or derivative assertion from the same source page is included.

## Direct and transitive import audit

The sole direct import is
`Langlands.Group.GL.MirabolicMixedOrbitData`. Its complete project import
closure, including that dependency but excluding the present statement,
has 21 modules:

- `Langlands.Group.GL.Basic`
- `Langlands.Group.GL.Maps`
- `Langlands.Group.GL.Mirabolic`
- `Langlands.Group.GL.MirabolicMixedOrbitData`
- `Langlands.Group.GL.MirabolicMixedProductSubgroups`
- `Langlands.Group.GL.MirabolicProjection`
- `Langlands.Group.GL.MirabolicRadical`
- `Langlands.Group.GL.Padic`
- `Langlands.Group.GL.RankMaps`
- `Langlands.Group.GL.RankReindex`
- `Langlands.Group.GL.UpperUnipotent`
- `Langlands.LocalField.Canonical`
- `Langlands.LocalField.Definitions`
- `Langlands.LocalField.Topology`
- `Langlands.Representation.Category.Basic`
- `Langlands.Representation.Filtration.Definitions`
- `Langlands.Representation.Geometric.ClosedSubgroupDefinitions`
- `Langlands.Representation.Induction.Definitions`
- `Langlands.Representation.Smooth.Definitions`
- `Langlands.Representation.Smooth.SmoothPart.Definitions`
- `Langlands.Representation.Twist.Definitions`

Every import edge was followed. All 42 dependency Lean/Markdown files were
compared byte for byte with Library commit
`2003a7a6a41b5e54c3f790e0887743ed616ed614` and remain unchanged.
The closure consists of actual matrix/local-field constructions and elementary
representation definitions and their construction laws. Its seven representation
modules are inherited through `ClosedSubgroupDefinitions`; they introduce no
geometric-lemma theorem, derivative theorem, or coinvariant-finiteness theorem.
The existence of an ordered enumeration is asserted here, rather than obtained
from a theorem in those modules.

The statement body uses only the published `PadicField`, `TopologicalData`,
the topology and group certificates, `mirabolic`, `plusSubgroup`, the two
inducing subgroups, their representative functions, and `OrderedDoubleCosets`.
The latter uses the actual quotient, actual `cosetOrbit` sets, disjointness
and openness. The quoted group, matrix and topology construction laws introduce
no representation-theoretic premise.

## Audit against the complete inherited exclusions

The checks below cover mathematical conclusions, proof successors and
transitive dependents as well as the named modules/tasks. No theorem proving
any excluded conclusion is imported or used. There is no proof of the new
orbit assertion whose dependencies could be replaced by a consumer premise.

1. **Plus functors and compatibility.** No plus functor, adjunction, BZ77
   4.13(d), general Leibniz proof or derivative compatibility is imported.
   `plusSubgroup` and its elementary matrix maps occur as permitted group
   infrastructure. No derivative functor module is in the closure, and no
   BZ77 derivative conclusion is assumed.
2. **Geometric and analytic comparisons.** No geometric-lemma proof,
   restriction-sequence theorem, exactness, character matching,
   stabilizer-to-stages containment, Haar scaling, integration or induction
   comparison is used. The imported support and induction definitions are
   constructions, not proofs of those comparisons.
3. **Whittaker finiteness.** No `Langlands.Whittaker` module is imported.
   In particular the closure avoids
   `SupercuspidalCoinvariantFinitenessStatement`
   (`62de5903-b616-4b5c-88eb-a066b77c5467`),
   `IrreducibleCoinvariantFinitenessStatement`
   (`5ab445dc-d2b4-4072-80d1-6370870a4a26`),
   `LeviCuspidalCoinvariantFinitenessStatement`
   (`3ff5c8fb-397c-4345-bcb3-5d98a0993d18`) and the dependent finite-length
   route `5428fe2c-013c-482d-aa6e-7df43e7191aa`. No arbitrary-character or
   degenerate-character finiteness conclusion is used.
4. **Segment-pair structure, commutation and gluing.** The closure has no
   segment, head, socle or Jacquet module. It avoids
   `UnlinkedSegmentSocleProductIrreducible`
   (`23e98d90-6055-4e35-91a9-b0f5d8a84961`),
   `LinkedSegmentSocleReverseProductStructure`
   (`a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`),
   `LinkedSegmentSoclePairReducible`
   (`8fa9f68b-fa1b-431a-97f6-5b163964d1fc`),
   `JuxtaposedSegmentSocleReverseProductStructure` and
   `LinkedSegmentSocleReverseProductQuotientHom`
   (`7ff2a1e9-89dc-439e-a861-a567b3db92bf`),
   `SegmentSocleProductIrreducibility`
   (`2ae5cbe5-0701-4509-88a0-db8cbeb35be4`),
   `AdjacentUnlinkedSegmentSocleSwap`
   (`e3634665-571b-4852-9f4c-bab8a1053434`,
   `cded83f3-df9c-4018-bc61-dc54f5c1f9ab`),
   `TwoSegmentSocleCommutation`
   (`426911b4-6620-413f-8065-04b25287f3bd`,
   `66e3b87c-647e-41e4-af18-df4d436765f0`) and
   `LinkedSegmentSocleGluing`
   (`c84cd52c-3ff3-4024-be50-8b84dd480888`,
   `6780b79c-9526-46aa-b8b4-00377d68b1ea`).
5. **Individual and ordered existence, criteria and exhaustion.** The same
   closure avoids individual special-head/reverse-socle existence
   (`67279e36-f3c2-42e3-9302-11729784042e`), individual
   segment-socle/reverse-head existence
   (`4ca79bbd-589e-476b-9f65-661e799984b5`),
   `OrderedMultisegmentSocleExistence`
   (`23189526-80b0-4828-a6d4-7ebec2cbeef5`), socle exhaustion
   (`f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`),
   `SegmentHeadProductIrreducibility`
   (`8364e73f-14ec-4d14-8f2b-1555a7c1ce95`),
   `GenericSegmentProductUniqueness`
   (`30341ae4-65f2-4a0e-9283-763db01a409e`), multisegment special-head
   exhaustion (`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`), ordered strong-head
   existence (`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`), quotient coverage
   (`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`) and ordered conversion
   (`8252833d-c269-41a9-824c-5879e531b23b`).
6. **Classification and square integrability.** No classification module
   is imported. The closure avoids analytic segment classification
   (`aca8805b-054f-4d56-8045-12db7f623404`),
   `SegmentSpecialEssentialSquareIntegrability`
   (`5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`), tempered uniqueness
   (`52e97845-36bb-457d-b76f-70753334b88c`),
   `SquareIntegrableLanglandsClassification`
   (`1cb45da2-7007-4351-a694-594fb148b8d1`), square-integrable exhaustion
   (`cd8ab97c-0b78-4bce-97c4-d307a28159a4`) and regular exhaustion
   (`bf433f0a-921a-428c-b0c0-6475438125ac`).
7. **Segment derivatives, Jacquet formulas and Ze80.** No segment derivative
   formula, segment existence/Jacquet formula, or segment classification is
   used, including parts (b),(d),(e),(f) of the inherited six-statement
   contribution. The closure avoids `SegmentFullJacquetFormula`
   (`ed48ae06-964c-4c84-9e62-978f5a953ca7`),
   `SegmentHeadJacquetFormula`
   (`55ad1e10-62d8-46b7-a081-909ef0056426`),
   `SegmentSocleJacquetFormula`
   (`b95105c6-f8bb-4641-ae53-2f49d1e7f034`) and
   `SegmentSpecialJacquetExponentNormFormula`
   (`92aea10f-62ac-4e0b-bd4a-9a80909797c5`).
   Ze80 §§3.5, 9.6, Theorems 4.2, 9.3, 9.7 and classification/exhaustion
   results are not used.
8. **Two-supercuspidal conclusions.** No supercuspidal theorem is imported.
   The closure avoids `TwoSupercuspidalNonadjacentProductIrreducible`
   (`3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`) and
   `TwoSupercuspidalProductStructure`
   (`ab61f565-1427-4746-ba77-46097563e962`).
9. **Dependency and control boundaries.** Pending statements, citations,
   conditional assemblies and proof tasks are not proved orbit inputs.
   Missing derivative or tensor inputs are not replaced by assumptions
   from consumers. The inherited operator pause of Worker 127, suspension
   of Worker 8 and hold of Worker 114 remain intact; this work grants no
   authority to resume them. No contact with Worker 127 was made.

The exact proof successor must retain all inherited restrictions directly
and transitively and prove this unchanged Library proposition. Statement
acceptance and source correspondence alone do not supply orbit geometry to
the host mixed-minus proof or its consumers.

## Development validation

The exact proposition declaration compiled and was inspected in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. The inspection reports a
Prop-valued definition with only universe `uF`, no errors or warnings, and
only `propext`, `Classical.choice` and `Quot.sound` in its axiom closure.
This is development evidence. Independent semantic acceptance and publication
remain required, and neither compilation nor statement acceptance proves the
orbit assertion.
