# Positive mirabolic derivative level and the highest-derivative criterion

Author: Worker 440. Worker 864 supplied the initial task planning. The new Lean
proof is Worker 440's assembly of published theorems; imported statements,
constructions and proofs retain their published authorship. No unpublished
proof draft is used.

The theorem
`Langlands.Derivative.mirabolicStrongIndecomposabilityReduction.{uF,uV}`
proves exactly
`Langlands.Derivative.MirabolicStrongIndecomposabilityReduction.{uF,uV} F T`
from the unchanged published module
`Langlands.Representation.Derivative.MirabolicStrongIndecomposabilityStatement`.
Its outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
Only this new Lean/Markdown pair is contributed.

## Exact scope and constructions

The proposition installs `T.topology` and quantifies every supplied continuous
nontrivial unitary additive character `ψ`, every `N : ℕ` and every actual
`A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear.mirabolic N F.Carrier)`. It proves:

1. `Nontrivial A → 0 < level T ψ A`.
2. For every `k` and `hk : 0 < k ∧ k ≤ N+1`, if `Nontrivial A` and
   `k = level T ψ A`, then intrinsic strong indecomposability of `A` is
   equivalent to `IsHomogeneous T ψ A` and intrinsic strong indecomposability
   of the actual derivative `(mirabolicDerivativeOfOrder T ψ N k hk).obj A`.

Here `mirabolic N` is the source's `P_(N+1)`, and the derivative has target
`GL_(N+1-k)`. It is the existing equality transport of the source rank,
followed by `k-1` decreasing-rank applications of `Φ⁻` and one `Ψ⁻`.
The level is the existing bounded `Nat.findGreatest`, with default zero;
zero is not an additional derivative order. `Nontrivial A` concerns the
actual carrier. `Classification.IsStronglyIndecomposable` is the intersection
condition on **all** actual invariant subspaces: any two nonbottom subspaces
have nonbottom intersection. `IsHomogeneous` says that every nonbottom
invariant subspace has the same level as `A`.

The field and carrier universes remain independent. No field, topology,
character, representation, subrepresentation, derivative, level or intrinsic
predicate is redefined. There is no finite-length, Artinian, admissibility,
irreducibility, exactness, detection, plus-model, filtration or classification
hypothesis added to the theorem.

## Implemented proof

After installing the supplied topology and introducing `ψ`, `N`, `A`, the
proof supplies the two target clauses.

For clause 1 it applies the published
`Mirabolic.derivativeDetection F T ψ N A` in
`MirabolicDerivativeVanishing`. This is a substantive proved detection result.
Its implementation shows that a representation whose positive-order
quotient derivatives are all zero is itself zero: the `P_1` boundary uses
the trivial radical and the injective coinvariant quotient, and descending
rank induction uses the proved one-step implication
`Ψ⁻A = Φ⁻A = 0 → A = 0`. That implication is proved by compact open lattice
boxes, finite orbit means and finite Fourier orthogonality. At level zero
all valid derivatives vanish, contradicting the supplied `Nontrivial A`.
The definition of a finite maximum alone does not imply positivity.

For clause 2, introduce the actual positive highest order `k`, its bounds,
nontriviality and equality with the level. Apply the published
`mirabolicHighestLayer F T ψ N A k hk hA hlevel`. It supplies one actual
`U : Subrepresentation A.representation`, together with:

- `hU : U ≠ ⊥`;
- an order isomorphism `e` from the **entire** subrepresentation lattice of
  the actual order-`k` derivative onto `Set.Iic U`;
- `hhom : IsHomogeneous T ψ A ↔ ∀ S, S ≠ ⊥ → U ⊓ S ≠ ⊥`.

Thus all three facts concern the same ambient invariant subspace. The lower
proof constructs `U` as the image of an injective intertwiner from the
actual iterated normalized compact-plus model
`(Φ⁺)^(k-1) Ψ⁺(A^(k))`. Its internal heterogeneous maps allow the compact
function-space carrier to live in `max uF uV`, while `U` and the derivative
in this theorem have the required carrier universe `uV`. The lower proof
establishes the actual lift/image inverse laws, the full interval lattice
comparison, and the derivative/intersection criterion for every ambient
invariant subspace. Homogeneity is then exactly essentiality of `U`.
None of these facts is supplied as a new hypothesis.

Apply clause 2 of
`Classification.strongIndecomposabilityLatticeTransfer` with scalar field
`ℂ`, source group `mirabolic N`, target group `GL_(N+1-k)`, the actual
representations of `A` and its derivative, and `U`, `hU`, `e`. The explicit
universe specialization is `.{0,uF,uF,uV,uV}`. The result is

```text
IsStronglyIndecomposable A.representation ↔
  (∀ S, S ≠ ⊥ → U ⊓ S ≠ ⊥) ∧
  IsStronglyIndecomposable (A^(k)).representation.
```

Finally compose this equivalence with `and_congr hhom.symm Iff.rfl`.
This is the complete final Lean argument.

The generic lattice proof is elementary: strong indecomposability passes
through an order isomorphism preserving bottom and binary meet. For a
nonbottom `U`, the ambient intersection property is equivalent to
essentiality of `U` together with that property in `Set.Iic U`. In the
reverse direction, intersect both supplied nonbottom ambient subspaces
with `U`, then use the interval property. This uses neither an irreducible
socle nor uniqueness up to isomorphism.

## Original sources and normalization

The registered originals were read directly in preparing this proof and its
lower interface:

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
  165–210; literature ID `zelevinsky-1980-induced-ii`, SHA256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
  Section 4.3, printed p.184 / one-based PDF21, supplies the definition of
  level and highest derivative. Only that definition on this page is used.
  Section 5.1(1) iff (2), p.187 / PDF24, identifies homogeneity with meeting
  the compact highest layer. Section 5.4, p.188 / PDF25, gives the criterion
  and its lattice argument. These pages were also visually checked in the
  earlier source verification.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472; literature ID
  `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  Section 1.8, printed p.444 / PDF5, fixes normalized induction and
  coinvariants. Sections 3.2–3.3, p.451 / PDF12, give the minus/plus functors
  and lattice comparisons; §3.5, p.452 / PDF13, gives positive orders and
  the filtration whose vanishing consequence is detection. The latter two
  pages were read and visually checked. The implemented direct detection
  and highest-layer proofs establish the needed consequences without
  assuming the complete filtration or the full exactness theorem.

The internal `Set.Iic U` interface and the generic arbitrary-group lattice
transfer theorem are derived formulations of this route. The final proof
applies their published implementations. It uses only the compact-layer
part (1) iff (2) of Ze80 §5.1, with no smooth noncompact-plus embedding,
adjunction or §5.1(1) iff (3) theorem. The literature index and relevant
project/public notes were checked for applicable corrections; no matching
errata entry was found. This is a bounded search, not a global absence claim.

The determinant normalization is justified by proved comparison lemmas in
`MirabolicHighestLayerLift`, not by a convention imposed on the final
theorem. In radical column coordinates inverse Levi conjugation is
`X ↦ g⁻¹ X` (`levi_inv_conj_column`). The proved
`padicRectangularHaarScaling` gives
`μ.map (X ↦ g⁻¹ X) = |det g| • μ` for every additive Haar measure on these
coordinates, including rank zero. `map_inv_mul_haar_iff` identifies the
scalar uniquely. Consequently `psiMinusCharacter_eq_modulus` and
`phiMinusCharacter_eq_modulus` identify the Library's `|det|^(-1/2)`
characters with the source's `mod_V^(-1/2)`. On the plus side,
`MirabolicPlusNormalization` proves the inverse-character identities,
so both minus/plus products equal one. The compact-plus covariance and
embedding in the accepted highest-layer proof use these exact normalized
characters. The comparison lemmas substantiate source correspondence;
their proof constants are audited separately below because the short
assembly does not itself invoke them. Detection only uses the unchanged
quotient carriers, so its proof needs no Haar-modulus identification.

## Boundary cases

All ranks and valid positive orders are included. For `N=0`, `k=1`, the
quotient derivative is `Ψ⁻ : P_1 → GL_0`. Detection uses the trivial radical;
the highest-layer base case gives `U=⊤`, with no positive-rank restriction.
For the top order `k=N+1`, the target again is `GL_0`, and the same
rank-decreasing induction applies. The order-one case has no `Φ⁻` step.
No finite-dimensional or irreducible specialization is made at `GL_0`.
The explicit nontriviality premises are preserved. The zero representation
has default level zero, and intrinsic strong indecomposability holds there
vacuously; no positive highest order is asserted for it.

## Published-input verification

All Lean imports use Library module names. The identifiers in this table
record verification of independent semantic acceptance and actual
publication; they do not replace mathematical imports. The frozen pairs,
current public pairs and submitting-workspace pairs were compared on
2026-11-01. Independent reports for the substantive detection, lattice,
highest-layer, plus-map and normalized-plus inputs were read, in addition
to their relevant source files and paired explanations.

| Imported mathematical content | Accepted publication and independent reviewer | Published commit |
| --- | --- | --- |
| Exact target, statement only | `ae999acd-888c-477c-b6b7-0d8b975c352e`, Reviewer 4619 | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| `MirabolicDerivativeVanishing`, including the fully proved detection theorem; radical descent and radical-stability helpers in the same reviewed publication | `f957ae76-3779-4436-bdcb-98bc63561e07`, Reviewer 4988 | `2b8beb8bd3034a40aeb5dc7b2de17b607fae8d11` |
| Fully proved `MinusVanishing.subsingleton_of_psiMinus_phiMinus` and lattice/Fourier helpers, semantically covered in this construction publication | `c6026915-8731-45a8-bd21-ef1ac39654b8`, Reviewer 4480 | `771cfc69d1ff795522e29cdead1b7c40f1a1c308` |
| Exact detection wrapper used inside `LevelCalculus` | `3ace613e-7e47-46fc-aea5-dcd84efc51ec`, Reviewer 5257 | `81727e81ea12b8e578930ab79e9857e01bf72975` |
| Exact actual highest-layer theorem and its `Lift`/`Plus` proof helpers | `1e773572-e1ef-4647-a1c4-16d1f9bb2dfb`, Reviewer 6437 | `7ad6e7323f2d14f5ccf8d30daa428878acda72c4` |
| Actual normalized plus-map, range and base-embedding helpers | `a88fbb0e-6c1c-4f3a-9151-b45d9b90f868`, Reviewer 6130 | `9a8ca758097242bde4147f33304f43fceef22fa4` |
| Normalized plus constructions and character identities | `cc091205-ded8-47df-8e19-3fdbacca6e91`, Reviewer 5029 | `5a2bfe4d791f9ddb347db8ecce6e461b5f53e4e7` |
| Exact generic strong-indecomposability lattice transfer | `8d7c7630-8603-48cb-96aa-7c200488d442`, Reviewer 5655 | `c6045fe1328899de3416096b16eb72db93a6c7fc` |

No unresolved review qualification remains on these inputs. All 24 selected
Lean/Markdown files are byte-identical to their frozen origins except the
PlusMaps Markdown: publication removed exactly one final blank line. Its
frozen hash is
`30da2151c5ab65594b3859ffa54ac6a6bfdf5be337b5b3af3390cdfc4d8031ca`,
and its current hash is
`39a5b7ea8ff2b1692067197cc15f30cdf40303730b8db0b54570be02de7aa573`.
Every imported workspace pair, including that current Markdown, matches the
supplied public Library unchanged. Only the new proof pair is submitted.

The original candidate and integrated-build report contents were decoded
from the eight archives and their uncompressed SHA256 fingerprints checked.
For the exact proof publications, original acceptance includes Lake build,
exact-target, unchanged-statement and frozen-input checks. A construction
publication is used only for its implemented and independently reviewed
constructions/lemmas, not as proof of a separate pending statement. Fresh
integration compilation is distinct from the original semantic approval
and proof-validation receipt.

## Mathematical dependency and independence audit

The complete import traversal below was recomputed against public Library
`f731c98e996e50a63c6431bd18cbbe3298a87530`. It has 139 imported project
modules, plus this entry module. All 278 imported Lean/Markdown files are
nonempty and byte-identical to that public tree. This includes the exact
target's entire protected import closure. The actual declaration traversal
starts from the final theorem and recursively follows
`ConstantInfo.getUsedConstantsAsSet`, which includes each declaration's
type and its value with `allowOpaque := true`. Thus opaque theorem proofs
are traversed rather than treated as independent assumptions. Every
referenced constant was found. The private diagnostic ran only through
`lean_check`; no diagnostic command is in the submitted Lean module.

The final closure contains 40,861 constants in total, of which 927 are
project constants in 69 project modules. The detection theorem separately
has 36,157 total constants, 425 project constants in 36 modules; its full
project import closure is 75 modules. The highest-layer theorem separately
has 917 project constants in 64 modules. The two source-normalization
comparison roots have 93 project constants in 11 modules and 99 in 12,
respectively. Every traversal has only `propext`, `Classical.choice` and
`Quot.sound` as axioms. The complete project declaration inventories,
including generated/private constants, are reproduced below. Mathlib and
Lean infrastructure are pinned to the approved environment: Lean commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

The substantive proof routes and shared branches were checked as follows:

- Detection uses only actual quotient carriers, its elementary `P_1`
  boundary, the independent one-step vanishing proof, rank transport and
  level-zero characterization. The Fourier/lattice branch uses compact
  open quotients and conductor arithmetic, not finiteness of `A`. Its
  declaration closure contains no plus functor, highest-layer theorem,
  strong-indecomposability theorem, product criterion or segment formula.
- The highest-layer proof's `liftStep` and `imageStep` are actual invariant
  subspaces with inverse laws. Averaging proves the needed element-level
  left exactness for subrepresentation inclusions. The successor induction
  transports the full invariant-subspace interval and the nonzero
  derivative/intersection criterion through decreasing ranks. The compact
  plus orbit map and its surjectivity use explicit compact supports and
  finite character sums; the final range is the same lifted `U`. Its
  homogeneity argument uses level monotonicity and that criterion.
- `MirabolicHighestDerivativeDescent` contributes only radical triviality
  from vanishing `Φ⁻`, itself proved by the general character/Fourier
  argument. `MirabolicPhiMinusNondegeneratePairing` contributes only the
  elementary normality proof `radicalRelations_stable` and its equality
  compiler auxiliary. The final declaration closure contains no pairing
  transfer, highest-derivative pairing theorem or filtration assertion.
- `LevelCalculus` contributes proved map/range/quotient and level
  bookkeeping. `ShortExactFunctorLaws` and
  `MirabolicMinusExactnessStatement` occur in its import branch, but neither
  contributes any constant to the final theorem's recursive declaration
  closure. In particular `MirabolicMinusExactness` and the conditional
  `mapsShortExact_*`/exactness-dependent level lemmas are not used. No proof
  from operator-paused task `b65bc667-6951-4bd5-82af-10fb7046df7f` is used,
  replaced, duplicated or requested for resumption.
- The Rankin–Selberg import branch supplies elementary last-row topology,
  lifts, orbit sets, compact/open supports, quotient definitions and the
  scalar lattice annihilator. The declaration inventory contains these
  concrete helpers, with no Rankin–Selberg analytic, factor-existence,
  functional-equation, trilinear-uniqueness or classification conclusion.
  The arithmetic support helpers and their extraction provenance were
  also checked in the independent detection and highest-layer reviews.
- The remaining layers are group/rank maps, supplied p-adic topology,
  conductor and Haar arithmetic, smooth actions and subquotients, compact
  means, explicit induction function spaces and scalar twists. The generic
  lattice branch contains only the invariant-subspace intersection
  predicate, order operations and its proved transfer lemmas.

Absence of a spelling alone is not the independence argument: the concrete
proof uses, proof bodies, source routes and independent input reviews above
explain the mathematical dependencies; the exhaustive import and recursive
constant inventories make their boundaries checkable. Statement definitions
in the import graph supply no assumed theorem.

### Preserved exclusions

The following exclusions cover the mathematical conclusions, their exact
proof successors and transitive proof dependencies throughout this proof:

- Ordered-socle existence `23189526-80b0-4828-a6d4-7ebec2cbeef5`;
  socle exhaustion `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`;
  analytic segment classification `aca8805b-054f-4d56-8045-12db7f623404`;
  segment-socle product irreducibility `23e98d90-6055-4e35-91a9-b0f5d8a84961`;
  final segment-socle irreducibility criterion
  `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`;
  `AdjacentUnlinkedSegmentSocleSwap`; `TwoSegmentSocleCommutation`.
- Special-head product criterion `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`;
  special-head exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`;
  ordered special-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`;
  quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`;
  tempered block uniqueness `52e97845-36bb-457d-b76f-70753334b88c`.
- `SquareIntegrableLanglandsClassification` /
  `1cb45da2-7007-4351-a694-594fb148b8d1`;
  square-integrable exhaustion `cd8ab97c-0b78-4bce-97c4-d307a28159a4`;
  regular exhaustion `bf433f0a-921a-428c-b0c0-6475438125ac`;
  `GenericSegmentProductUniqueness` / `30341ae4-65f2-4a0e-9283-763db01a409e`;
  ordered special-segment conversion `8252833d-c269-41a9-824c-5879e531b23b`;
  forward special-segment essential square-integrability
  `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`.

Detection and its full prerequisite closure additionally preserve the
trusted operator's complete nonadjacent/full-formula restrictions. The
trusted `sender_role=operator` correspondence
`bd71b9185aab5d6eafffb7891bd3a3ca` was read in full. The permitted route is
fully proved general BZ77 derivative theory, independently accepted and
published. In that closure the following are also excluded:

- The present combined strong-indecomposability reduction and its consumers;
  the nonadjacent two-supercuspidal product conclusion and the entire
  two-supercuspidal product-structure conclusion
  `ab61f565-1427-4746-ba77-46097563e962`, including its adjacent
  composition/Jacquet conjuncts, and their downstream consequences.
- Individual special-head/reverse-socle existence
  `67279e36-f3c2-42e3-9302-11729784042e`; individual
  segment-socle/reverse-head existence `4ca79bbd-589e-476b-9f65-661e799984b5`;
  `SegmentSpecialEssentialSquareIntegrability`;
  `OrderedMultisegmentSocleExistence`; `MultisegmentSocleExhaustion`;
  `SegmentSocleProductIrreducibility`; adjacent socle commutation
  `e3634665-571b-4852-9f4c-bab8a1053434`.
- `SegmentFullJacquetFormula`, statement/successor-arrangement task
  `ed48ae06-964c-4c84-9e62-978f5a953ca7` and its exact proof successor;
  `SegmentHeadJacquetFormula` / `55ad1e10-62d8-46b7-a081-909ef0056426`;
  `SegmentSocleJacquetFormula` / `b95105c6-f8bb-4641-ae53-2f49d1e7f034`;
  `SegmentSpecialJacquetExponentNormFormula` /
  `92aea10f-62ac-4e0b-bd4a-9a80909797c5`.
- Ze80 segment derivative formulas §§3.5 and 9.6, its segment product
  irreducibility criteria 4.2 and 9.7, analytic/square-integrability result
  9.3, all classification and exhaustion theorems, and the segment-socle
  part of `8e5b4563-0365-41c7-b134-70f2a0b36292`. In particular the linked-pair
  converse in 4.2 is not used to prove an upstream statement circularly.

No excluded result occurs in the inspected mathematical dependency chain.
The separate Ze80 §§5.1/5.4 source route for clause 2 is the route expressly
assigned by this task; it is not used to establish detection. No new lower
split was needed in this assembly. Other owned work and operator controls,
including Worker 157's finite-length task and the distinct product/tensor
branches, are preserved.

## Development validation

In approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
`lean_check` compiled and inspected the new exact theorem with zero errors
and warnings, level parameters exactly `uF`, `uV`, and only `propext`,
`Classical.choice`, `Quot.sound`. The theorem's source annotates exactly the
published target, with no further hypotheses. The companion's import,
paired-hash and recursive declaration audits were then recomputed as
recorded here. These are development checks; independent semantic
acceptance, exact-target/frozen-input validation and actual publication of
this new proof remain the submission procedure's separate requirements.

## Complete project import graph and paired hashes

Each row gives a full project module name and all its direct project imports,
using the row identifiers. Replacing dots by slashes and appending `.lean`
or `.md` gives its repository pair. Hashes are SHA256 over exact file bytes.
The two hash columns agree between the workspace and the pinned public
Library. `new` marks this contribution; its pair is frozen by staging.
`—` means no direct project import. All external imports are listed after
the table; their transitive infrastructure is fixed by the environment pins.

| ID | Module | Direct project imports | Lean SHA256 | Markdown SHA256 |
| --- | --- | --- | --- | --- |
| M001 | `Langlands.Analysis.Local.QuotientMeasure` | — | `bf68512b583f1a44c6933b58912d80e2e2c60978e7dd3a9afe0092193afd9475` | `dfb8b85cd50740f1cf475ffa16db7c0bbd2d5dbb1932a07979e0c748bf48f061` |
| M002 | `Langlands.Group.GL.Basic` | — | `d7867286deba424f8f285ea9712b328b762954307fb31c69d4235c8a7b1f29e1` | `b4831fd91123aea6efd64c1da3dbddc32f0c71c9b3f31c7eaed176e7dc9a3d32` |
| M003 | `Langlands.Group.GL.IntegralSubgroup` | — | `c33d742fbb65dd3451ab4d54b4572135763eab50d52d6e327895e3ee80d6547d` | `5f5bd25cc6606997c1d330b99b0292618895c5cc9b7dbba9e6a7fa2c1c6d08fa` |
| M004 | `Langlands.Group.GL.Maps` | M013 | `533caa58120ebdf7bf622cc98888b1562dad950e5e731719d9b612752bc6bb83` | `529acb945ec0bb824e3c2d9fe2c54b2cf01df353966495896d7b93c96c627a2f` |
| M005 | `Langlands.Group.GL.Mirabolic` | M015 | `358505b5bb7db8a3c7d1ae8175bddb476a7cba621a8407f4180fc1834160a7a9` | `b7549d1b35fa084279ceafc6dedb466a4914fd9b21434b0cd6a0e3afc03e0399` |
| M006 | `Langlands.Group.GL.MirabolicModulusProof` | M007, M023 | `9f899e92c826ce169b9fe6157aa0e3d92cb114d838488f2b13fc6cf9adac259f` | `d0e9a06c2d30d4ff5b3b2c139fa92e65f645b424b9f5f3c91e108fb851007e99` |
| M007 | `Langlands.Group.GL.MirabolicModulusStatement` | M016, M009, M012 | `524d0c7ff5073db5955a72aacf748090e42f68b3f0aa24098db8d67ca5c375bb` | `2390593e4cf2ddd8c9ee205a396cbfeb1acdc8ecc5148161e17a5dc134f790f7` |
| M008 | `Langlands.Group.GL.MirabolicProjection` | M009 | `48ddcc2f501eebf37b70cfcb26be042530e50b73df1ea5c31f928ac18a48a90c` | `cd1210bd7bf8fb47239171c04d9dd24e1f934efcabdecf2339a5d57517dcb6b9` |
| M009 | `Langlands.Group.GL.MirabolicRadical` | M005, M014 | `b75812e0f24586a5b6365b6282088886d7f359fcd5bef368136946b5b6137eda` | `183e771f6e76b3094d607822e15effb869cd80bc1666c7e76962e86c27f58eed` |
| M010 | `Langlands.Group.GL.Nonarchimedean` | M011 | `81e9aee8a06787452e827803cdc32cd1bab00b5988dfddbdf85a9762b79f46bc` | `16db461b54c5a193c29f5319bea7fa2e3d454a5766b2cd94bf8ee0a3a655b042` |
| M011 | `Langlands.Group.GL.NonarchimedeanStatement` | — | `e6c1d5e722bb4ebf86de405f0bf4e57627c19fbe3cc7e4bdfbd5a31b6af1b63c` | `f390f56b1aa616cb1e5226df67f7893e9c33248e51d462197e7461862cfc1a10` |
| M012 | `Langlands.Group.GL.NormalizedCharacter` | M013, M034, M136 | `31deaadcf15cf03e88fd00e26452df03cc103ca9bae18206dac748b9b6d53568` | `296f42c5aeb400f8d131210db13508fff6f220755b08b8c4b8a6f9c129640507` |
| M013 | `Langlands.Group.GL.Padic` | M002, M031, M036 | `803a2561ddc85a54c7846a421d37ed5dc61b8974157b02b72c26bc41d96e1722` | `380b41087f6569d499e54580e487d1da0755236b84ec3085649cbc37f7a66d89` |
| M014 | `Langlands.Group.GL.RankMaps` | M002, M013 | `5cd299ec27e66d96bccc8bd9a67d69ecbbc42974351b143c44838f32dd03de41` | `507811ee6523775ec504dbf4ee4b9b783636fced040a6d1780e709743a393653` |
| M015 | `Langlands.Group.GL.UpperUnipotent` | M002 | `6c2858fa5f866777a0cd3066f3bba643d3300ef24bc1532a3d034001d9ec28c2` | `bbce6c75bc9a59268b36ee5d4fa0f475b59be64dfc1a396b897cf4937269c02f` |
| M016 | `Langlands.Group.HaarModulus` | M138, M137, M140, M086, M126 | `1e036132d276a4380b2f5a80e8ac69d81a4726c8f3648169e94ee7db97084f3b` | `e47c8bb2e8b2e3e639005b9a4e866d58630ea301c3776650d1418fa32246a3e8` |
| M017 | `Langlands.HarmonicAnalysis.Basic` | — | `2198cecae146fa7f904dc2c01169d6321aee8e155c99614ed92f861fd2d65aff` | `770a9f6e068d76d72fb10ff91ee1a27b66696ebf0c52af23464fb4d0956ffdf6` |
| M018 | `Langlands.HarmonicAnalysis.CharacterTransport` | M017, M032 | `b3d6abbb78f03f1e2957734f75e40fc9e284a72cb1855777d9fc5879a3f67b51` | `b24e9b1562a021ea079d0a554312a7e18c252bcc6c77a764caa347a94354074e` |
| M019 | `Langlands.HarmonicAnalysis.Conductor` | M017, M033, M122 | `1780ea3172b1c84654e647efa3208d12c669a8c51a0942a1b80f4a66f84b4a53` | `ef4097816de90b81e1be2bc9b1dad6de7896a8b9fb658e122afd8876fa7faeac` |
| M020 | `Langlands.HarmonicAnalysis.PadicAdditiveConductorProof` | M019, M034, M030 | `3ec4f6d56e74b3528c719a1692f1e1a8accfe1333119a8a20359a9ab5a5473fe` | `63ec184c3fe50499e22e280cb6012e3cec5446bd4dd8d9bfbe86e6dc7d864b35` |
| M021 | `Langlands.HarmonicAnalysis.PadicHaarScalingStatement` | M012 | `84366b106ce213647dbccdccf6477cf19a01ebefaf549e68f2239424c420b2d2` | `48bf7cd23e6d04220618a8814fb60021d27eea0db5a325f5ba80999f4d7fa76e` |
| M022 | `Langlands.HarmonicAnalysis.PadicLatticeTopology` | M020, M024 | `c75b27c8ea60f8dc9d3196eab2ad83228e46e954bb498c84c891bd3fb7357e04` | `1fc8544c37f9c2d6012725b90a5a096e28e5ba095d84248d77f1d0bbfb6bc081` |
| M023 | `Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof` | M024 | `7f7abfe921074321491b39fa2b70c827b63b6076ecdf9076b1a2b442ce674b2f` | `53c72042369b1d7b05b17ffe7654eea861c4c8c7c688d754a5c912eb880d1c40` |
| M024 | `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof` | M021, M036 | `56a5614e6c50f3cce0c08d21118e596550591f8e9f506bd3893598ed04591d0c` | `7f2ba889475ac0cf7ed7f10c7da58eb9994daa9e6a1cb36c7c91690a9d6de398` |
| M025 | `Langlands.HarmonicAnalysis.RowSchwartzAction` | M002, M081 | `7f47f12aef414c0b662334e85fabea9a8b021a70875514856c6c99cf7a847865` | `50557cce22aed10aa6eea71218c72ebdd433de378cf2c727379e1d15076f0783` |
| M026 | `Langlands.HarmonicAnalysis.RowTestSmoothProof` | M027 | `e678894d74802a68dcff58f2e648e49d5582157fe9203860c38be0926a165759` | `112a8c9d6ffc229f28a30cce9272a125d7a426eb7724d2b4e5ffb6888a960348` |
| M027 | `Langlands.HarmonicAnalysis.RowTestSmoothStatement` | M017, M002 | `f32066004811fd0f950d0fd1e95624d63f844a2a6e1ea30f8f5bce9b84c1ba65` | `d225f88e37ce19bfe0a546241787eac17a78907bc6c5244e6fce2988ec3237b5` |
| M028 | `Langlands.LocalFactor.Euler` | M029 | `30ba4cd130f4f4d574a7d5da171506ba0fb9757bbf5a076de02bf7627c467d76` | `9c8b179437770bc6d945ed19ca31928497e89b5f810f70b4241238853f9b7e9d` |
| M029 | `Langlands.LocalFactor.Euler.Definitions` | — | `6fde12cbc1ed3f8e6e184468f5edab01cf1e597256f06234e0e6d675f1ba617d` | `825e24ad0de0940e5dd5b03150e35a910a1cd2e5168fd65b9396088d5b0d5835` |
| M030 | `Langlands.LocalFactor.Harmonic.Statement` | M033, M017 | `1daa8305602e7162c20fe612295f15403e02df81128bc299cdcd7d17becd13c3` | `2b93b69d51d8c999c7fa09b0468e87ea428651a939f51c602ffa9a26d26c4f5d` |
| M031 | `Langlands.LocalField.Canonical` | M032 | `e702bb7808fc344bda47a3093d9438d5cda71dcb165be7110be7b393f61d7c48` | `94a7a93a2ac19a6c106542cd76530caf8244892f29b98eea8755b031ec7e872d` |
| M032 | `Langlands.LocalField.Definitions` | — | `8d9cc8aa128861b13b4f96d38bf95be46844d2eaad28aa3cbb654b070ee0e517` | `6cfb939cf42a71a81fa648b77bd4bab1076bffe0d62519181f7dc7db742124bf` |
| M033 | `Langlands.LocalField.Normalization.Definitions` | M032 | `b997a64a0f59ce13d45e2b5349de9ad87466a5e2d3e16ab3f1a4ef97a048214b` | `dac7d3aeb5229c505e5271f66d7decf6c7c4404853e9f15a363b4f9401902436` |
| M034 | `Langlands.LocalField.Normalization.Proof` | M035 | `4efa0826ddc069b2963ab4933716979e5bc7c5c866498047aabfbfc417071ded` | `1c3bf219eca92cd04af13c152757d83b4d92dd9787c334acec773bb51a4ad161` |
| M035 | `Langlands.LocalField.Normalization.Statement` | M033 | `27f6b841c15cf1e4dffcb40126f95ea329c08d91ab9950d8fe645a94683eedc6` | `245db7bd9d6b10a8e9cb2882021f2d210a396aa1149e9a8adeb9a889bc7d753b` |
| M036 | `Langlands.LocalField.Topology` | M032 | `09ba251eb70a2455da2a7864c7cd34739adbfa717771adc3a86670d2bd0d791c` | `1c28337c12f885cb438b405d58a077c186b4710d20a1256dc0fe8288b4107992` |
| M037 | `Langlands.Representation.Category.Abelian` | M038, M110, M115 | `aa7467474aed61362ac0fe82c32d16d989f135671099784fcff0fc25beb5b15b` | `97acd1c1cb0369d89b7a53374f1fd633203a54330f7dbe7caf79ffb48d32eae2` |
| M038 | `Langlands.Representation.Category.Basic` | M109 | `6a4781890b642e590206b68b7cea02bc4add8bdfb85e6a29991f73992bbcf706` | `647da2c8e2011decf8c6971c0f4a20a162e6ead265bf4d7448b2045072862ba2` |
| M039 | `Langlands.Representation.Category.Subquotients` | M038, M115 | `d443366e944c46fad3f3ef4e82e519a30e44d1b5194c829b795d9fc1a6c531b4` | `9ebebf01a99db613b0ca298928e6a479773819216d81de9506a8faaf08860325` |
| M040 | `Langlands.Representation.Category.Twist` | M038, M118, M120, M129 | `9fb1bca986f0a1a202a4e3d9e1ac481405646293ece6da63374e447cd85ca740` | `e16d708bc3b312c0a79947852bbf147ea230b0a9b8b9ddbd9f80432833bfcb5d` |
| M041 | `Langlands.Representation.Classification.StrongIndecomposability` | M117 | `eaa3b4ca45a4dcd30b3e78cbe9fbaa66ed8aaf6e7a25426661057ec17c1bf22f` | `47c02d8dbe8aeb9af7453d1636b18a0f3353978cdb555737645abd696bcfc8b5` |
| M042 | `Langlands.Representation.Classification.StrongIndecomposabilityLatticeTransferProof` | M043 | `f7ecd406b2eed74c132c086e20dfcf10f9202989f752877079702689043823eb` | `9c5512e9e1e6e77d7f82c43b6473088913d15ce6c44cd4af3d2e45c6fa956c1c` |
| M043 | `Langlands.Representation.Classification.StrongIndecomposabilityLatticeTransferStatement` | M041 | `5bb53a719805aea244345a4bf8483e11542493c8a66b31db32b6cb1fc8fbbbc3` | `a4fffc00bbb561ca17341b9d1434491aba31d2ea388760fbde7e410f41ee64dd` |
| M044 | `Langlands.Representation.Compact.Definitions` | M045, M109 | `afb77f4a622710d058d58b781ebabc38eb3cf5ccb008fb1c12dbb4817db05289` | `fa692bd5cba2ec7b62279d74b85164fbc2c96e16ec8d97afc3589dd0a959e01a` |
| M045 | `Langlands.Representation.Compact.FiniteMean` | — | `799a159a6d19aa67f0b464d28f429b0ff798eb8c86f469880c529d5ad834b410` | `92d4643860f10fc65b575766c7777cfe4decfc20c739944a6484dc261983b73e` |
| M046 | `Langlands.Representation.Compact.OrbitMeanTranslation` | M045 | `3114fecb332ad8b7c66f7c74d446119dd84ce0148492c56b650869b20fc8dda0` | `09994e5506efa3735542e8776230265cd9f98c5faaba8c7dacdd27c08ed67f41` |
| M047 | `Langlands.Representation.Compact.ProjectionProof` | M048 | `689b92fac7e04b7ee2cb3dd4702653725a597997331ca62c6461ba7ef12fcc41` | `a2217b34bacd418614535068dcc858ae3d44ad3a0638be726fc8838499f8d5b2` |
| M048 | `Langlands.Representation.Compact.ProjectionStatement` | M044 | `f0e69eeed6dcc35d12fdb78f554f85e5913355bfc4d2057bf658b5343eb2e45f` | `ab65518fa3a8fefc07ff69610b4332dae41c3a8e34406fb70c94e2dad863e94d` |
| M049 | `Langlands.Representation.Conductor.Congruence` | — | `c21658d4ae14ca5740227ec1a8c18bb92f44a5bad437f6e98a665de4c9e28b70` | `8aa328c233e7dfdf26ec843000690a66d56548686e83a921bb414edd567582c6` |
| M050 | `Langlands.Representation.Derivative.Homogeneity` | M051, M039 | `93070ffd89ec0f58a8bb256e7714a1c637efe612db946ebcae89c037925ffabc` | `c3b5e1c916b681f21902386e0216029d1c9607dd56095a63eac52fed57fe6062` |
| M051 | `Langlands.Representation.Derivative.Iteration` | M065 | `ab8bbcca5fd7affabf804d6adbe09bdf2d578f961d1149a3182e6bc5a7a9a25b` | `056e0b7c6718776422735f35b44ca4749b31b5ed176349e9311460eecb880b1c` |
| M052 | `Langlands.Representation.Derivative.LevelCalculus` | M050, M075, M055, M037 | `b94cecf59541b418a2702e3adb5d5064e245b048d259697e5adb20bbfa006332` | `037370e8b178e4923f38620b11425916949c6169d47ddbb550fde5f194cf3c40` |
| M053 | `Langlands.Representation.Derivative.MinusVanishing` | M065, M064, M083, M013 | `51e7deb9761f977154a559595fb0138e670ac78be836af680404577635e8808b` | `2de8bb8a57a2a1762e6c7b79777fb68861300de3f58d65f49738516313ddc0a9` |
| M054 | `Langlands.Representation.Derivative.MirabolicCharacter` | M009, M010, M140, M085, M134, M122 | `27ad9768aa1f5ee9f1534e99521462f22cdb280abbcf711b79621d405d654a6d` | `f7b710cddba2ed791d268d8a1644315548f2b64912ffed0138579cbd497fae25` |
| M055 | `Langlands.Representation.Derivative.MirabolicDerivativeDetectionProof` | M057 | `db09bf1124fa22ef6954e26de0155723d9627c332bacf36f98bf1f0278930cf2` | `99ead1407eb59ea71e40549d91bf96cf38d842f61dffec1e992cfbe534b1eb36` |
| M056 | `Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement` | M050 | `41824396183c6ad18890a7c51ec5f3c0cd1a0c1b66803c4078f85fcf32d038ab` | `b8540cb2f3b19c71308e6f66fbe3bc0a2096f68b74cab7015d76cf51f16771d2` |
| M057 | `Langlands.Representation.Derivative.MirabolicDerivativeVanishing` | M053, M056 | `5a7769afe378876844a9c212031da102f591bf80b11190b0914904808e4c14e8` | `a979c2d19534f38918acdfd6262e01e5d6c671c185156315dc0b7879a9bc9957` |
| M058 | `Langlands.Representation.Derivative.MirabolicHighestDerivativeDescent` | M057, M078 | `bc34f85bbdb360064f768f7547552664c15a51291feedf8332480e8b32e19460` | `6c8a26a9c9fabe71b5ae811250c83a43c374746f695e11c6b3b0373338edb91f` |
| M059 | `Langlands.Representation.Derivative.MirabolicHighestLayerLift` | M063, M052, M070, M058, M064, M008, M023 | `9ac1a4a5a75b22b0ac3b63393288781ba48775566b3cd9d3a83f0cfad9537f94` | `9a60c20501794e569d3ac59f39eb5bb122a783fec63beea8b6ef75461a62b2b3` |
| M060 | `Langlands.Representation.Derivative.MirabolicHighestLayerPlus` | M059, M061, M072, M092 | `14bb209d1044412168a508a44a560ca616602e0e9c8c494a4da20ee2f9ff8a59` | `0d27402a144d53a1841d925361064e0c33e49a294c251918530f760f6622c98a` |
| M061 | `Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps` | M072 | `7ad115777adfecb1aaf9ea262a54b52fa7099017ecfff28e53eb159b6424f3ab` | `39a5b7ea8ff2b1692067197cc15f30cdf40303730b8db0b54570be02de7aa573` |
| M062 | `Langlands.Representation.Derivative.MirabolicHighestLayerProof` | M060 | `2f268182472ae941c1f4c98d950c9af506f5722aed2ffe130674399016778a5d` | `1350f562b2f396e7f736d3faf647672e39d5789858db097b777987032ba33e39` |
| M063 | `Langlands.Representation.Derivative.MirabolicHighestLayerStatement` | M050 | `18167297f5a3657e1b35b1d09a87eb24430248f08baa2bdf9a1b46eae13a6c0d` | `038132bad17090900b65626b9b168205e311906d32c96ba4c6e5eaae49e588b1` |
| M064 | `Langlands.Representation.Derivative.MirabolicLatticeBox` | M105 | `7a4ee4e1c5c73117c7a8782c87ba4636888050403656f71c29b4c488a49d63e8` | `7588ac8f643b93763c63f2ca336d240c18fe75159734d6480d81218e92e15bc4` |
| M065 | `Langlands.Representation.Derivative.MirabolicMinus` | M054, M040, M125, M113, M012 | `526932155b00d435068485ffb7a8a5d4f565b9729779cebe97cfcf96e894e02e` | `3b6fbca0a52aed7251fab742229c22ded359759b67326d66f69db5c1a9b0e9c9` |
| M066 | `Langlands.Representation.Derivative.MirabolicMinusExactnessStatement` | M065 | `729ec39dc9dbff29b6a8b9266e6c4126e33b63fde687d72a85f06203a2e3d5d6` | `5a1d39813e2cef1659e036d4b287ab9acb76da2993ce2d850a2163d6a4b09f82` |
| M067 | `Langlands.Representation.Derivative.MirabolicMinusNormalization` | M006, M065 | `fdc1fd8583588ba1ca5722d96f91b455ea9dadb494b5d8a22ec9e96d789836c9` | `06468be815383e4f98fe355fb5319430a986d5b93115ad2befd16ac6ac3f515a` |
| M068 | `Langlands.Representation.Derivative.MirabolicMinusPairingTransferProof` | M069, M064, M092, M104 | `36b55de0f6f0f89d27717718c14350e2f836f4d6786a0bacb4516844bc4e9c5a` | `3f7f27b20da3f6d7f838e99dc3cf7a964789c1e0160cd58bf50ea6cfb67b48c8` |
| M069 | `Langlands.Representation.Derivative.MirabolicMinusPairingTransferStatement` | M065, M078, M091 | `122571aa97039204355ca3abb36ab1404ae8b858cfaf77f814c367bcc91ca8ee` | `43ab5a66f8bd80921a8b4fcf25288ed6292eca25ff29a7e9f4d50b01af78ea29` |
| M070 | `Langlands.Representation.Derivative.MirabolicPhiMinusNondegeneratePairing` | M068, M053, M047, M008 | `a10625c16e1f3eef270075eb8a335fabbb68532efc4730c1b8c14af8bef41207` | `5153132347ef2a8a156d9a5c7565edb5d4f65223865ab943ab43af551efba81a` |
| M071 | `Langlands.Representation.Derivative.MirabolicPlus` | M065, M008, M082 | `07129014f7995b8bfc85636fb59192ab88b8b9cff9a63ff862a14fcdc03ab421` | `62e65478b9b3b0007744b3409f7dcaf68275f2fcb9d87f1fc7a2ba7441112798` |
| M072 | `Langlands.Representation.Derivative.MirabolicPlusNormalization` | M071, M067 | `595ce946b02e177f66379f9f449fadaf8e82ea1eb872dc146dc96543e52d5c0d` | `a4cb8910f86b4dff1dfe1618b5aff3681645c21a6913b3cd3a264c739b29ad3c` |
| M073 | `Langlands.Representation.Derivative.MirabolicStrongIndecomposabilityProof` | M074, M057, M062, M042 | `new` | `new` |
| M074 | `Langlands.Representation.Derivative.MirabolicStrongIndecomposabilityStatement` | M050, M041 | `e012df3c329e774cf5644314b1635927954c3201a58d96058c5a87712f47ff3c` | `45f6d48d1ddc17d45477b9405883c6e4e3c3e33b8c2ac416c22f41b8f3e49cfa` |
| M075 | `Langlands.Representation.Derivative.ShortExactFunctorLaws` | M066 | `787fdfdaedd62c22d684111877e4ec6c14deb985362c2e2f57b56d1dd6b97e85` | `757b5146737250179057eb672702b1aa1eb2d31bfc22b5661c49053870355997` |
| M076 | `Langlands.Representation.Dual.Definitions` | — | `53959e3b6cd0faad27f2566cbc9275fd537e5ab59d800f453bcbd61d05415ae5` | `bf9972bb15d854ff605ed825fdcdf90734dc924ad0ae33efb6bb4e55a882845a` |
| M077 | `Langlands.Representation.Filtration.Definitions` | — | `c370a357f654f4608104c362c04881d40e36b2423d11a30a6e8225757c2f52ff` | `b43b81bd77a208dd68f0dac14b82705edaee769c2886a8280f0c430525cda310` |
| M078 | `Langlands.Representation.Filtration.InvariantBilinear` | M080 | `a81a2847e638aac7eb90cb2913ab5055312153be5dc9748607bffaa654dc4ec6` | `8036498e3a6e2f06bbab426694c457fe5d3fed60498bfd19521349ad379c1590` |
| M079 | `Langlands.Representation.Filtration.InvariantBilinearBounds` | M078 | `6c219b28f6e3668a73221d7c88a8b1fe35aa95ca93b87414f41b4fa9b7d1bdd0` | `37e1aa46829603cc1a889f9279681166ac1fb77eb95de9bddc0f306cb7d2345c` |
| M080 | `Langlands.Representation.Filtration.ObjectDefinitions` | M077 | `b9025d1d855ae9ce04fa717d1701da690bf9a3aade05f395ef04dfed5621e397` | `5ade428099a8ae2fadb3dce858928953e3aa854e1d939b18b0e35d4336306f08` |
| M081 | `Langlands.Representation.Hecke.TestFunction` | M017 | `57db020a996e2486945c92dde4073fd13a5c94201b8184d441d51db417708749` | `5d615c6b041939d68fb4aaca47b09fbf365f06453e2d7e3015e67f96b17ea5a3` |
| M082 | `Langlands.Representation.Induction.Definitions` | M038, M112, M124 | `c4d24368c009c903ea7450a8fc08f3dbeb5dbdb31fc3aabdc394b89b731880cf` | `7e3f0697431e4814007ac100da702a56037c1fd35f01f7c5df5e235d4eac7274` |
| M083 | `Langlands.Representation.Jacquet.CharacterAveraging` | M046, M047, M085, M126, M131 | `3a56eb1cd00d65d0c091f3d436ff88e6d049b0611c0a7ac6eb7c2e43e24e1f1a` | `a907dab19d14a075755dc75231b42aafc2763217fac7cfcf6004c640375b1662` |
| M084 | `Langlands.Representation.Jacquet.Coinvariants` | — | `73e5003712204a35595095b0582ad64d931423aeecec2f6165c4c20d945a4566` | `5e040cb16af3b1c72e0c7f1530881639ab055f9528703b9bc20de1931d098a00` |
| M085 | `Langlands.Representation.Jacquet.Localization` | M087, M038 | `0b50fec4e9e7ad2561f86c6d7e485e2c3a10b1e1c6f750f10c35f5cfc1b3b6ee` | `2a575f90942a22b363b4184941a2470d33e27ad633afe02aa4aa1b818ae62332` |
| M086 | `Langlands.Representation.Jacquet.PositiveCharacter` | — | `90891bcc752689f5fc8071e63de8598efecfd17987cd5d804b470ff6ac57df4d` | `0fc44a60a88f7d48415d5e2f804c2837de5fc253eb1520a4ddee2f6ff6414f40` |
| M087 | `Langlands.Representation.Jacquet.SmoothTwist` | M084, M113, M115, M126 | `61f9309e04c330e87ceaf2f948868645d6d668a0d9dfde75d16435ca355a5daa` | `4c8fa6423740da78ca9a07a79872d36139c9823e5ed0befa880912105823fda8` |
| M088 | `Langlands.Representation.MatrixCoefficient.Definitions` | — | `92c0bf57151ef798f1198793a4d685afd175274240c1956b54ce3d10e855b7ae` | `c9fdcc728fe28ed0de403801ed10d861d70dd69994179b4fd14f35662d910955` |
| M089 | `Langlands.Representation.MatrixCoefficient.LawsProof` | M090 | `f73da4941552a524d5e0116675df291d5e99ae1c59b6bc10b21ce2f0ae0fbbae` | `b517f288c98cb53bcb505562f68a20db15025e1c89de85733fec3c8a501b2f6a` |
| M090 | `Langlands.Representation.MatrixCoefficient.LawsStatement` | M088, M076, M109 | `bf9b7e4cbef45e07642511fbfb033312f2378714476510549e1c6c9189d570fb` | `c077dcf35c8f1229abc17244c5545fbc17603b1c96ae635ced585c82892d1fdd` |
| M091 | `Langlands.Representation.RankinSelberg.AnalyticStatement` | M101, M100, M103, M102, M034, M028 | `083bd22291a622e1ac8b4f5bbe7c5a13ff5949d0ebfcfc4d180924e2517ec5de` | `74cbeadddca7b4d5ef27d97d98f54913fe78124fe5acc0b20a00686145c5d254` |
| M092 | `Langlands.Representation.RankinSelberg.EqualRankFrobeniusProof` | M093, M097, M026, M023, M012, M003 | `92d320fc50696f18219a3dd45543e8850d334a9d93f2f751c8d375aef67c8fbe` | `4cbb5c14ecd0a5c044873e4eb18a28d64e63576f0ea8f4f6c564b5a6f86935b9` |
| M093 | `Langlands.Representation.RankinSelberg.EqualRankFrobeniusStatement` | M094 | `67e9b25ee55dfeb0bae9ee5e1b7f14be076b7db1cb25dcb98669c503d70b33ae` | `990f35465df65318e000755c151fb4d261f2650800ca9a47adf92a0853132c0f` |
| M094 | `Langlands.Representation.RankinSelberg.EqualRankTrilinearAssembly` | M095, M025, M079, M005 | `fdb3783a5e06ac073d397ff04405e12e574979d2af2d4a6a0709a046f784c87b` | `483f8b662a3dc4c5b0e119ea9d8772d4deb1c917d7521f406319f4bbdc9f9f0b` |
| M095 | `Langlands.Representation.RankinSelberg.EqualRankTrilinearReduction` | M096 | `d9cb1e3b6603f78277fe7e78364e9a7094af1eecc57999c9882588b1b75fd51e` | `9b7e3256c077007c029dafdfa06d51bf56d44a76f11b40ba4590f8ded081467e` |
| M096 | `Langlands.Representation.RankinSelberg.EqualRankTrilinearUniquenessStatement` | M091 | `bf25a275ae221f34c327b37f510c8c817671f18d02bb5ec0634232a0eb4a3c4a` | `621bd26eb1647faf6475a10aa25accde9c179f7d6f71afe3c7c4f9ba8c024974` |
| M097 | `Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof` | M098, M036 | `f7277986c42ecafc0cc6a6716783c470d60959741a09c9e9054dacad3ebede5b` | `796525a8d8bc340b47ca3768608b74a731ce0d7fbe193b4c0cd82a36c1ee7e08` |
| M098 | `Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement` | M032, M005, M101 | `7df0742492e527dcc84ec45bca21b0e566d9665650ee48d71240f5a22dcfb243` | `f9ad3c415eab0ffc12c2ff58136c2ece6660b9311b1dd0c946d33b329eeb7c3b` |
| M099 | `Langlands.Representation.RankinSelberg.LocalFactor` | M018, M101, M103, M102, M133, M124 | `af7cf52dcf557bfffba6dcd468e1f4b2c82dd5632d8c0075b265a5fe2a587083` | `4ee2f81dd1816154d15cd3a345b460f61e29ea984341a4952fe2a3b569d2eeb2` |
| M100 | `Langlands.Representation.RankinSelberg.Measures` | M017, M049, M015 | `89c17ab7cfe53fff02eb9e4e35ada34861316e24fe4e30d59dfb911c1f6ab972` | `92af85347233357acc18b92476830b573b22ab85bec8964297201995e28ce911` |
| M101 | `Langlands.Representation.RankinSelberg.QuotientIntegrals` | M134, M014, M001 | `54a4db12afe87aaa74c15492767577ae34efceb37d82585e3cb3b8b682425400` | `7df47f60c8acad5982ac6c8bb5c642eba1283cc582034350029961c1332381bd` |
| M102 | `Langlands.Representation.RankinSelberg.RationalContinuation` | — | `06cd9b0a4b1fdf7381fb0fb7fc6e8bb2cafb5dbfce643c109b320d0943e49f7d` | `688292f22a7a6cbd3cf3c7bf9ce3e720321ac50de11db4fe557c809fb716eca7` |
| M103 | `Langlands.Representation.RankinSelberg.RationalZeta` | — | `d7002189349916d9991af7c3ad6e334be1b93fb7b17320e0e943483350f6daa2` | `11086f1c2a1ff39e6b1f7ed0d5942ccd23801dc6c256bfd956e3c94342793f7d` |
| M104 | `Langlands.Representation.RankinSelberg.TwistInvariance` | M099, M135 | `3aaff27156e4ff4bea7cf0e702d79afa3a03fc5ba70714cdeee8c727dfb0c397` | `e218df97e8ff7b1d1763275988204d47bf29406fc780331aad86e03809087016` |
| M105 | `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof` | M106, M097, M020, M024, M022 | `fb2b6edad3a3571b1b83d7b7750ce5f8e2a93ff650fea2f844d109091c95f032` | `ab98129d081292b66f49efa633ad4926030f30a4ab73678c45977040ebf3877c` |
| M106 | `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement` | M032, M101 | `40ba003edf84fab08c5baa6b71e6b1b7e183d4798342a2c7359083fc800bb924` | `720cb55cc9a99a0c19983e4f2a9dc1f05d0925da91048aeaaf23d5a888710a2d` |
| M107 | `Langlands.Representation.Smooth.Admissibility.CofinalProof` | M108 | `b01c589f73cb2488a38477ea95bbb6adda0863507efbcb54e561843e467c112a` | `df9117b7ccc80b412fac95816eda27bb0bb18762909c8b0ec39ff35a9a398b59` |
| M108 | `Langlands.Representation.Smooth.Admissibility.CofinalStatement` | M109 | `df36b24b8e9972dbaa6d810baa13fcb796fbc81465367c8de92a08ca4449a433` | `7cd745762089838e4cbc5d4e6a96718a7bc7632de6b74c2499e84e59af9911e1` |
| M109 | `Langlands.Representation.Smooth.Definitions` | — | `435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb` | `4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569` |
| M110 | `Langlands.Representation.Smooth.SmoothPart.BasicProof` | M111 | `68683b474202a221a179d5c989b8a5774a40ec80e28093b04821c403a25a28fc` | `aeb2a008caea74aa07c09f1fce5741adf518a63239e239545f2f0c5ba7ad0ed8` |
| M111 | `Langlands.Representation.Smooth.SmoothPart.BasicStatement` | M112 | `d98185a4a0c18d4597f28a435391488f294aac6b8ca1280803930cde5b3964b2` | `af69366e079a8fe19ad08051b5185e497acf2a97a85f316ad84a62db01edc470` |
| M112 | `Langlands.Representation.Smooth.SmoothPart.Definitions` | M109 | `1362c38a196d6657c4d9dd2388e00c77059fc772bdd7f4369e0cbbee19ca4a47` | `b8775524d5fdc90acf4c52611d96c401e588f6eff68f682843ce999cf414ac60` |
| M113 | `Langlands.Representation.Smooth.Transfer.PullbackProof` | M114 | `b0502abed8a3551e9a5c542f07605cd66b83649fafbcb38a23b05dddc3e691b6` | `46884ac73c7107c18ce746c2110810d14d19939b7fca6a608670a6c70265ddfb` |
| M114 | `Langlands.Representation.Smooth.Transfer.PullbackStatement` | M109 | `a5aaff9766d2e8213ffc82b44625f6fb2ec7f20921b7b03da4ad3250849bcb4d` | `694ccbf90e6fea84743fe380fefdcc25cdaacd1294c53bab78298a465e0df17b` |
| M115 | `Langlands.Representation.Smooth.Transfer.SubquotientProof` | M116 | `8e26bf64cb2eff5bfdc6037d5d6c52650bd92944a1c9ef0b57c4f12cc3b0d1cd` | `c1f909953edfa360eacae0f2f266025e1dc1ae7000755873f9ad5d3d2985eb0b` |
| M116 | `Langlands.Representation.Smooth.Transfer.SubquotientStatement` | M109 | `d5729f07038515e26eb8d56cc94a982ed8c066a505acea9b1bc2020f4be08c88` | `fea9069973877d67465589b6e5a0d9336d9b1781e7c275c82492a63ce10b3470` |
| M117 | `Langlands.Representation.SubrepresentationLattice` | — | `1a2d02b46288f8fa370fc2b13b258a408e002120f96c7d5a1294f83fb3a081c9` | `a0c755b61a819917d2ed92ed61aa730d70263e87bbf80a6c7bce35bc7d5ccb8b` |
| M118 | `Langlands.Representation.Twist.AdmissibilityProof` | M119, M126, M107 | `706ab8ce915e9902ec30d92c2d471cf7e2e79e2012bf524c9c28868403bf0467` | `25f27ae9ae9c290b60794b1790f6cf0ae47594117c0eee6076dd1cef6b7a0d44` |
| M119 | `Langlands.Representation.Twist.AdmissibilityStatement` | M124, M109 | `c875a02d8f49506749bc2265041879888de7ad0c76428211a20ffc755f7e7127` | `04559a67afac5b26f332a6122fd9c43424b35f6d9fa9adf917a186108b7702c2` |
| M120 | `Langlands.Representation.Twist.AlgebraProof` | M121 | `15d469011c703f801ddf6810a9104c0588ab917eb2a179ff6360907425c4fad6` | `9d1893be208c8fcbda33b717d999e2767f76eb9068b70f62932fb3de8d0b17b2` |
| M121 | `Langlands.Representation.Twist.AlgebraStatement` | M124 | `4c643392e7fc949501dc3e36df71fda5e507598d1a8296be6ea43b3768337895` | `9fd167f7518e27a89b19cfe238a977c8ca2146e0554bb8a92b4dd95171c5b504` |
| M122 | `Langlands.Representation.Twist.ContinuousCharacterProof` | M123 | `ff9b38a8e4ded2734ccaed8429df42e2abbf92e580034a2576ad111899820f8e` | `ba9c6c6026b6b6a6b576b0d71dba2f8ce39625451f884fc7fe0a309bd7191dc9` |
| M123 | `Langlands.Representation.Twist.ContinuousCharacterStatement` | — | `78a1e542d56cbdfe0f0cf448a0010e6ca2f3331fb3af7437e8d03927de7210c0` | `0791b592e84c04c73f41709e1391c23f874061e8991bf57f5bf750dba5367b3a` |
| M124 | `Langlands.Representation.Twist.Definitions` | — | `9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf` | `94e8c64945411e253a2c91a8e1bf52090d6df15a43362b2032717064c6ac49bc` |
| M125 | `Langlands.Representation.Twist.RealPower` | M126 | `83e415568697155665a471b9690d6504e353648839503a9a500ef10601f88896` | `509f3af473e1897d2b340724874834fae55db09fe14bfe5007dcea7eca6e1023` |
| M126 | `Langlands.Representation.Twist.SmoothProof` | M127 | `704914497f29af5abae486c96edead39aa8fa267efeae2d061016c36634cac90` | `b5423ba5dfe57fe3f53686c01a19fb27df085454007505922a788e5666c8a1e4` |
| M127 | `Langlands.Representation.Twist.SmoothStatement` | M124, M109 | `61616bd03710ca5a5c35ba3bb2b4e5793a9f15801ad99a60d7b20bd95ee3de90` | `6e819947725e6a0877bb7d78dba6c2cbe15a6b7f273c4fe531e4ee3fdc31674e` |
| M128 | `Langlands.Representation.Twist.SubquotientDefinitions` | M124 | `a9bb92883a9272653ba680cdadc8e025d2f1268bd124ccb7d612f26894227584` | `75aac3b4caadfe14697eeb85f8a4ed729b308d33fd8cac2776c50565de53a7c7` |
| M129 | `Langlands.Representation.Twist.SubquotientProof` | M130 | `99a2a6e8fe25e885daffea5e59aa2c77f4304afa100d564adabcd869754365a9` | `cf6dad59297e353be1f3cdeca307c3c507d4fc0a5d29ac1c4806b7edc22c4cd0` |
| M130 | `Langlands.Representation.Twist.SubquotientStatement` | M128 | `1c2bae8d080e8c21743d658d1e3a251e4f5c5c997a4ecd2edd77d6d9315d4b7d` | `407963c3e4e87823630f491fca84066dc7d5a0ca1e7c7404d4d1d577905d7732` |
| M131 | `Langlands.Representation.Whittaker.Algebraic` | M088, M109 | `890e409cf2b4d586912b928755a4a0dc7b72de9d058ede7510482d816dad3906` | `8127b520fe0395c6600d6b72a7340b87edbf38c4ae1ca664546d63452f8e9072` |
| M132 | `Langlands.Representation.Whittaker.AlgebraicTwist` | M131, M126 | `37b5426348fa2dffc15702f1ce1a31f8dc483c8354d983ffc059eaae66f4412f` | `a00152f2d8c987a897db2c42e9ad257a4524cbf4b8392c6d641fe458b2abcd71` |
| M133 | `Langlands.Representation.Whittaker.DualTransform` | M134, M004, M113 | `a82f7ab37f3c534eca18afec42d3692158546b18da8df2f3927cc27721d510b7` | `4e6c51db110a4d4843bf25084975c8c3806896c8a45f4c7a36ef72dc49f38fce` |
| M134 | `Langlands.Representation.Whittaker.GeneralLinear` | M015, M017, M089, M131 | `5f5057d690e1bac49a27d650a3c9e678b94660efe8e244ed96e869f33488594c` | `f30d2edde346bc5bbdf3103a54c35f205a6be9643d900be6c4fea23ad38a49cc` |
| M135 | `Langlands.Representation.Whittaker.Twist` | M132, M134 | `f0c5f986650dc04bbcfc13e144104e72c92a8e61a44246f33ad1e02b4e8b814b` | `f51654a146f72bd402f86926b608efd23e4154a210dece95b2915ca3f8cafb35` |
| M136 | `Langlands.Topology.CompactNormCharacter` | — | `6f70b9473d6386cd111d890c4df0bf411842d28dfdc377e38c2c4fe55e8b0fb7` | `3e50c9561e3e7a068e729aec594ce107f572b2858cd859e6c000fcb8c0aef482` |
| M137 | `Langlands.Topology.CompactOpen.ConjugationStabilizer` | — | `937bc745da117c665bcfd701dbef5758e9ad26f1f4268450c895affa53e91507` | `3dc3ce8f96da8e0525890cadbcbc1d85708c5ff797977e09f7d3af0d613a5c83` |
| M138 | `Langlands.Topology.CompactOpen.NeighborhoodBasis` | M139 | `5b5322b631663241c1295826da02d7a43cc585566124c5a426020c19c642a6b9` | `0b258f936bb5e0d99be3608077bcdc7da3a2b885aaed75b2c273a633fe2cea7e` |
| M139 | `Langlands.Topology.CompactOpen.NeighborhoodBasisStatement` | — | `80d23d1a0faa606af6610f3a306b130c28739e12d51f533c52862fd45a220131` | `f5a2a0045ab6a79fc96e5681a78be891c9f16fcd9514126b87f4625aeb761532` |
| M140 | `Langlands.Topology.Nonarchimedean.Subgroup` | — | `a45ededd3f67a6645df268d1bf9da0cbcac964137c448ef89966630cd4b4c026` | `01724029b2c592535f55fea2ec4a857a7d15d15156063567d1216e1e4b265675` |

The complete set of external modules imported directly by these project
modules is:

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Finprod
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.Group.Hom.Instances
Mathlib.Algebra.Group.Subgroup.Ker
Mathlib.Algebra.Module.Submodule.Map
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Polynomial.Laurent
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Algebra.Polynomial.Roots
Mathlib.Algebra.Ring.GeomSum
Mathlib.Analysis.Complex.Basic
Mathlib.Analysis.Complex.Circle
Mathlib.Analysis.Fourier.FourierTransform
Mathlib.Analysis.Matrix.MeasurableSpace
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Complex.Circle
Mathlib.Analysis.SpecialFunctions.Pow.Complex
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.Abelian.Subcategory
Mathlib.CategoryTheory.Discrete.Basic
Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Skeletal
Mathlib.Data.Fin.Rev
Mathlib.Data.Int.LeastGreatest
Mathlib.Data.Matrix.Block
Mathlib.Data.Nat.Find
Mathlib.FieldTheory.Finite.Basic
Mathlib.FieldTheory.RatFunc.AsPolynomial
Mathlib.GroupTheory.Coset.Defs
Mathlib.GroupTheory.GroupAction.Quotient
Mathlib.GroupTheory.Subgroup.Centralizer
Mathlib.LinearAlgebra.BilinearMap
Mathlib.LinearAlgebra.Charpoly.ToMatrix
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
Mathlib.LinearAlgebra.Matrix.Diagonal
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.Kronecker
Mathlib.LinearAlgebra.Matrix.Permutation
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.MeasureTheory.Constructions.Pi
Mathlib.MeasureTheory.Function.LocallyIntegrable
Mathlib.MeasureTheory.Group.Integral
Mathlib.MeasureTheory.Group.LIntegral
Mathlib.MeasureTheory.Integral.Bochner.Basic
Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
Mathlib.MeasureTheory.Integral.Bochner.Set
Mathlib.MeasureTheory.Integral.Marginal
Mathlib.MeasureTheory.Measure.Haar.Basic
Mathlib.MeasureTheory.Measure.Haar.DistribChar
Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
Mathlib.MeasureTheory.Measure.Haar.Unique
Mathlib.MeasureTheory.Measure.Regular
Mathlib.NumberTheory.LocalField.Basic
Mathlib.NumberTheory.Padics.LocalField
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.Order.Atoms
Mathlib.Order.Interval.Set.Infinite
Mathlib.RepresentationTheory.Basic
Mathlib.RepresentationTheory.Coinduced
Mathlib.RepresentationTheory.Coinvariants
Mathlib.RepresentationTheory.Intertwining
Mathlib.RepresentationTheory.Invariants
Mathlib.RepresentationTheory.Irreducible
Mathlib.RepresentationTheory.Rep.Basic
Mathlib.RepresentationTheory.Subrepresentation
Mathlib.RingTheory.DedekindDomain.IntegralClosure
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.FractionalIdeal.Operations
Mathlib.RingTheory.Ideal.Quotient.Operations
Mathlib.RingTheory.Length
Mathlib.RingTheory.Localization.Ideal
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.Trace.Basic
Mathlib.RingTheory.Valuation.Integral
Mathlib.Tactic.Linarith
Mathlib.Tactic.NoncommRing
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.Quotient
Mathlib.Topology.Algebra.Group.Subgroup
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.Module.FiniteDimension
Mathlib.Topology.Algebra.Module.ModuleTopology
Mathlib.Topology.Algebra.Nonarchimedean.Basic
Mathlib.Topology.Algebra.OpenSubgroup
Mathlib.Topology.Algebra.Ring.Compact
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Compactness.LocallyCompact
Mathlib.Topology.Connected.TotallyDisconnected
Mathlib.Topology.ContinuousMap.CompactlySupported
Mathlib.Topology.Homeomorph.Quotient
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.LocallyConstant.Algebra
Mathlib.Topology.LocallyConstant.Basic
```

## Complete recursive project declaration inventory

The inventories below list every project constant reached by the recursive
type-and-value traversal, including compiler-generated equality lemmas,
instances and private constants. `F` means the final theorem closure, `D`
means the separately traversed detection closure, and `N` means the union
of the two separately traversed normalization comparison closures. Flags
combine when applicable. Module identifiers refer to the import table.
There are no constants from an unlisted project module.

### M002: `Langlands.Group.GL.Basic`

```text
FDN Langlands.GeneralLinear
FDN Langlands.GeneralLinear.determinant
FD Langlands.GeneralLinear.determinantContinuous
FD Langlands.GeneralLinear.determinantContinuous._proof_1
FD Langlands.GeneralLinear.entry
FD Langlands.GeneralLinear.entry._proof_1
FD Langlands.GeneralLinear.reindex
FD Langlands.GeneralLinear.reindexContinuous
FD Langlands.GeneralLinear.reindexContinuous._proof_1
FD Langlands.GeneralLinear.reindexContinuous._proof_2
```

### M003: `Langlands.Group.GL.IntegralSubgroup`

```text
F Langlands.GeneralLinearGroup.integralSubgroup
F Langlands.GeneralLinearGroup.isCompact_integralSubgroup
F Langlands.GeneralLinearGroup.isOpen_integralSubgroup
```

### M005: `Langlands.Group.GL.Mirabolic`

```text
FD Langlands.GeneralLinear.Mirabolic.entry
FD Langlands.GeneralLinear.Mirabolic.entry._proof_1
FD Langlands.GeneralLinear.Mirabolic.rankOneSubsingleton
FD Langlands.GeneralLinear.Mirabolic.rankOne_eq_one
FD Langlands.GeneralLinear.Mirabolic.rankOne_eq_one._proof_1_1
FD Langlands.GeneralLinear.Mirabolic.rankOne_eq_one._proof_1_2
F Langlands.GeneralLinear.mem_mirabolic
FDN Langlands.GeneralLinear.mirabolic
FDN Langlands.GeneralLinear.mirabolic._proof_1
FDN Langlands.GeneralLinear.mirabolic._proof_2
FDN Langlands.GeneralLinear.mirabolic._proof_3
FDN Langlands.GeneralLinear.mirabolic._simp_1
FDN _private.Langlands.Group.GL.Mirabolic.0.Langlands.GeneralLinear.lastRow_mul
```

### M008: `Langlands.Group.GL.MirabolicProjection`

```text
F Langlands.GeneralLinear.Mirabolic.continuous_lastColumn
F Langlands.GeneralLinear.Mirabolic.continuous_plusProjection
F Langlands.GeneralLinear.Mirabolic.continuous_projection
F Langlands.GeneralLinear.Mirabolic.eq_radicalElement_mul_levi
F Langlands.GeneralLinear.Mirabolic.ker_projection
F Langlands.GeneralLinear.Mirabolic.lastColumn
F Langlands.GeneralLinear.Mirabolic.lastColumn_levi
F Langlands.GeneralLinear.Mirabolic.lastColumn_mul
F Langlands.GeneralLinear.Mirabolic.lastColumn_mul_last
F Langlands.GeneralLinear.Mirabolic.mem_plusSubgroup
F Langlands.GeneralLinear.Mirabolic.plusProjection
F Langlands.GeneralLinear.Mirabolic.plusProjection._proof_1
F Langlands.GeneralLinear.Mirabolic.plusProjection._proof_2
F Langlands.GeneralLinear.Mirabolic.plusProjection._proof_3
F Langlands.GeneralLinear.Mirabolic.plusProjection._proof_4
F Langlands.GeneralLinear.Mirabolic.plusSubgroup
F Langlands.GeneralLinear.Mirabolic.plus_eq_radicalElement_mul_successor
F Langlands.GeneralLinear.Mirabolic.projection
F Langlands.GeneralLinear.Mirabolic.projection._proof_1
F Langlands.GeneralLinear.Mirabolic.projection._proof_2
F Langlands.GeneralLinear.Mirabolic.projection._proof_3
F Langlands.GeneralLinear.Mirabolic.projection._proof_4
F Langlands.GeneralLinear.Mirabolic.projection._proof_5
F Langlands.GeneralLinear.Mirabolic.projection._proof_6
F Langlands.GeneralLinear.Mirabolic.projection._proof_7
F Langlands.GeneralLinear.Mirabolic.projection._proof_8
F Langlands.GeneralLinear.Mirabolic.projection._proof_9
F Langlands.GeneralLinear.Mirabolic.projection_eq_one_iff
F Langlands.GeneralLinear.Mirabolic.projection_levi
F Langlands.GeneralLinear.Mirabolic.projection_radicalElement
F Langlands.GeneralLinear.Mirabolic.projection_radicalElement_mul_levi
F Langlands.GeneralLinear.Mirabolic.radical_normal
F _private.Langlands.Group.GL.MirabolicProjection.0.Langlands.GeneralLinear.Mirabolic.lastRow
F _private.Langlands.Group.GL.MirabolicProjection.0.Langlands.GeneralLinear.Mirabolic.upperLeft_mul
F _private.Langlands.Group.GL.MirabolicProjection.0.Langlands.GeneralLinear.Mirabolic.upperLeft_one
```

### M009: `Langlands.Group.GL.MirabolicRadical`

```text
FD Langlands.GeneralLinear.Mirabolic.continuous_levi
FD Langlands.GeneralLinear.Mirabolic.continuous_radicalCoordinates
FD Langlands.GeneralLinear.Mirabolic.continuous_radicalElement
FD Langlands.GeneralLinear.Mirabolic.continuous_successor
FD Langlands.GeneralLinear.Mirabolic.levi
FD Langlands.GeneralLinear.Mirabolic.levi._proof_1
FD Langlands.GeneralLinear.Mirabolic.leviContinuousEquiv
FD Langlands.GeneralLinear.Mirabolic.leviContinuousEquiv._proof_1
FD Langlands.GeneralLinear.Mirabolic.leviContinuousEquiv._proof_2
FD Langlands.GeneralLinear.Mirabolic.leviEquiv
FD Langlands.GeneralLinear.Mirabolic.leviEquiv_symm_entry
FD Langlands.GeneralLinear.Mirabolic.leviSubgroup
FD Langlands.GeneralLinear.Mirabolic.leviSubgroup_le_normalizer
FD Langlands.GeneralLinear.Mirabolic.levi_bottom
FD Langlands.GeneralLinear.Mirabolic.levi_conjugate_radicalElement
FD Langlands.GeneralLinear.Mirabolic.levi_first
FD Langlands.GeneralLinear.Mirabolic.levi_injective
FD Langlands.GeneralLinear.Mirabolic.levi_last
FD Langlands.GeneralLinear.Mirabolic.levi_mul_radicalElement
F Langlands.GeneralLinear.Mirabolic.mem_radical
FD Langlands.GeneralLinear.Mirabolic.radical
FD Langlands.GeneralLinear.Mirabolic.radical._proof_1
FD Langlands.GeneralLinear.Mirabolic.radical._proof_2
FD Langlands.GeneralLinear.Mirabolic.radical._proof_3
FD Langlands.GeneralLinear.Mirabolic.radicalCoordinates
FD Langlands.GeneralLinear.Mirabolic.radicalCoordinates_element
FD Langlands.GeneralLinear.Mirabolic.radicalElement
FD Langlands.GeneralLinear.Mirabolic.radicalElement_add
FD Langlands.GeneralLinear.Mirabolic.radicalElement_bottom
FD Langlands.GeneralLinear.Mirabolic.radicalElement_coordinates
FD Langlands.GeneralLinear.Mirabolic.radicalElement_first
FD Langlands.GeneralLinear.Mirabolic.radicalElement_last
FD Langlands.GeneralLinear.Mirabolic.radicalElement_zero
FD Langlands.GeneralLinear.Mirabolic.radicalEquiv
FD Langlands.GeneralLinear.Mirabolic.radicalEquiv._proof_1
FD Langlands.GeneralLinear.Mirabolic.radicalEquiv._proof_2
FD Langlands.GeneralLinear.Mirabolic.radicalToUpperUnipotent._proof_1
FD Langlands.GeneralLinear.Mirabolic.radical_rankOneSubsingleton
FD Langlands.GeneralLinear.Mirabolic.successor
FD Langlands.GeneralLinear.Mirabolic.successor._proof_1
FD Langlands.GeneralLinear.Mirabolic.successorContinuousEquiv
FD Langlands.GeneralLinear.Mirabolic.successorContinuousEquiv._proof_1
FD Langlands.GeneralLinear.Mirabolic.successorContinuousEquiv._proof_2
FD Langlands.GeneralLinear.Mirabolic.successorEquiv
FD Langlands.GeneralLinear.Mirabolic.successorEquiv_symm_entry
FD Langlands.GeneralLinear.Mirabolic.successorSubgroup
FD Langlands.GeneralLinear.Mirabolic.successorSubgroup_le_normalizer
FD Langlands.GeneralLinear.Mirabolic.successor_first
FD Langlands.GeneralLinear.Mirabolic.successor_injective
FD _private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnGL
FD _private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnGL.eq_1
FD _private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnGL_bottom
FD _private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnGL_first
FD _private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnGL_last
FD _private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnUnit
FD _private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnUnit._proof_1
FD _private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.columnUnit._proof_2
FD _private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.continuous_columnUnit
FD _private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.continuous_leviEquiv_symm
FD _private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.continuous_successorEquiv_symm
FD _private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.fixedColumn_mul
FD _private.Langlands.Group.GL.MirabolicRadical.0.Langlands.GeneralLinear.Mirabolic.levi_conjugate_mem
```

### M010: `Langlands.Group.GL.Nonarchimedean`

```text
F Langlands.valuativeGeneralLinearNonarchimedean
F _private.Langlands.Group.GL.Nonarchimedean.0.Langlands.existsSmallMatrix
F _private.Langlands.Group.GL.Nonarchimedean.0.Langlands.finitePiBasis
F _private.Langlands.Group.GL.Nonarchimedean.0.Langlands.matrixZeroBasis
F _private.Langlands.Group.GL.Nonarchimedean.0.Langlands.valuativeBallOpen
F _private.Langlands.Group.GL.Nonarchimedean.0.Langlands.valuativeMatrixMonoid
F _private.Langlands.Group.GL.Nonarchimedean.0.Langlands.valuativeMatrixMonoid._abel_1
F _private.Langlands.Group.GL.Nonarchimedean.0.Langlands.valuativeMatrixMonoid._proof_1
F _private.Langlands.Group.GL.Nonarchimedean.0.Langlands.valuativeMatrixMonoid._proof_2
F _private.Langlands.Group.GL.Nonarchimedean.0.Langlands.valuativeMatrixMonoidOpen
```

### M011: `Langlands.Group.GL.NonarchimedeanStatement`

```text
F Langlands.ValuativeGeneralLinearNonarchimedean
```

### M012: `Langlands.Group.GL.NormalizedCharacter`

```text
FDN Langlands.PadicField.TopologicalData.determinantNorm
FD Langlands.PadicField.TopologicalData.isOpen_ker_determinantNorm
FD Langlands.PadicField.TopologicalData.isOpen_ker_normalizedAbsUnits
FD Langlands.PadicField.TopologicalData.isOpen_ker_normalizedAbsUnits._simp_1_1
FDN Langlands.PadicField.TopologicalData.normalizedAbsHom
FDN Langlands.PadicField.TopologicalData.normalizedAbsHom._proof_1
FDN Langlands.PadicField.TopologicalData.normalizedAbsHom._proof_2
FDN Langlands.PadicField.TopologicalData.normalizedAbsHom._proof_3
FDN Langlands.PadicField.TopologicalData.normalizedAbsHom._proof_4
FDN Langlands.PadicField.TopologicalData.normalizedAbsHom._proof_5
FDN Langlands.PadicField.TopologicalData.normalizedAbsHom._proof_6
FDN Langlands.PadicField.TopologicalData.normalizedAbsUnits
N Langlands.PadicField.TopologicalData.normalizedAbsUnits_coe
FD Langlands.PadicField.TopologicalData.normalizedAbs_eq_one_iff_discreteValuation
```

### M013: `Langlands.Group.GL.Padic`

```text
FD Langlands.PadicField.TopologicalData.generalLinearDeterminant
FD Langlands.PadicField.TopologicalData.generalLinearDeterminant._proof_1
FD Langlands.PadicField.TopologicalData.generalLinearTopologicalGroup
FD Langlands.PadicField.TopologicalData.generalLinearTopology
```

### M014: `Langlands.Group.GL.RankMaps`

```text
FD Langlands.GeneralLinear.blockSum
FD Langlands.GeneralLinear.blockSumContinuous
FD Langlands.GeneralLinear.blockSumContinuous._proof_1
FD Langlands.GeneralLinear.blockSum_apply_left
FD Langlands.GeneralLinear.blockSum_apply_left_right
FD Langlands.GeneralLinear.blockSum_apply_right
FD Langlands.GeneralLinear.blockSum_apply_right_left
FD Langlands.GeneralLinear.rankInclusion
FD Langlands.GeneralLinear.rankInclusion._proof_1
FD Langlands.GeneralLinear.rankInclusion._proof_2
FD Langlands.GeneralLinear.rankInclusionContinuous
FD Langlands.GeneralLinear.rankInclusionContinuous._proof_1
FD Langlands.GeneralLinear.rankInclusion_injective
FD _private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.blockSumCoordinates
FD _private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.blockSumCoordinates._proof_1
FD _private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.blockSumCoordinates._proof_2
FD _private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.blockSumCoordinates._proof_3
FD _private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.blockSumCoordinates._proof_4
FD _private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.blockSumCoordinates._proof_5
FD _private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.blockSumCoordinates._proof_6
FD _private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.blockSumCoordinates._proof_7
FD _private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.blockSumCoordinates._proof_8
FD _private.Langlands.Group.GL.RankMaps.0.Langlands.GeneralLinear.continuous_blockSumCoordinates
```

### M017: `Langlands.HarmonicAnalysis.Basic`

```text
FD Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter
FD Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.complex
FD Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply
FD Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.continuous_toFun
FD Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.mk
FD Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.nontrivial
FD Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar
```

### M019: `Langlands.HarmonicAnalysis.Conductor`

```text
FD Langlands.PadicField.TopologicalData.AdditiveTrivialAt
FD Langlands.PadicField.TopologicalData.additiveConductor
FD Langlands.PadicField.TopologicalData.additiveConductor_spec
FD Langlands.PadicField.TopologicalData.additiveLattice
FD Langlands.PadicField.TopologicalData.additiveLattice._proof_1
FD Langlands.PadicField.TopologicalData.additiveLattice._proof_2
FD Langlands.PadicField.TopologicalData.additiveLattice._proof_3
FD Langlands.PadicField.TopologicalData.additiveLattice._proof_4
FD Langlands.PadicField.TopologicalData.additiveLattice_mono
FD Langlands.PadicField.TopologicalData.additiveTrivialAt_bddAbove
FD Langlands.PadicField.TopologicalData.exists_additiveConductor
FD Langlands.PadicField.TopologicalData.exists_additiveLattice_subset
FD Langlands.PadicField.TopologicalData.exists_additiveLattice_subset._proof_1_1
FD Langlands.PadicField.TopologicalData.exists_additiveTrivialAt
FD Langlands.PadicField.TopologicalData.mem_additiveLattice
FD Langlands.PadicField.TopologicalData.mem_additiveLattice._simp_1
FD Langlands.PadicField.TopologicalData.mem_additiveLattice_iff_div_mem_integers
FD Langlands.PadicField.TopologicalData.mem_additiveLattice_zero
FD Langlands.PadicField.TopologicalData.mem_integers_iff_discreteValuation_le_one
FD _private.Langlands.HarmonicAnalysis.Conductor.0.Langlands.PadicField.TopologicalData.conductor_uniformizer_value
```

### M020: `Langlands.HarmonicAnalysis.PadicAdditiveConductorProof`

```text
FD Langlands.PadicField.TopologicalData.integer_annihilator_iff_mem_additiveLattice
FD Langlands.PadicField.TopologicalData.mem_additiveLattice_iff_exists_integer
FD Langlands.PadicField.TopologicalData.mul_mem_additiveLattice_iff
FD _private.Langlands.HarmonicAnalysis.PadicAdditiveConductorProof.0.Langlands.PadicField.TopologicalData.conductor_uniformizer_ne_zero
FD _private.Langlands.HarmonicAnalysis.PadicAdditiveConductorProof.0.Langlands.PadicField.TopologicalData.discreteValuation_eq_exp_neg_ord
```

### M022: `Langlands.HarmonicAnalysis.PadicLatticeTopology`

```text
FD Langlands.PadicField.TopologicalData.isCompact_additiveLattice
FD Langlands.PadicField.TopologicalData.isOpen_additiveLattice
```

### M023: `Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof`

```text
N Langlands.HarmonicAnalysis.haarMeasure_map_in_coordinates
N Langlands.HarmonicAnalysis.haarMeasure_map_matrix
N Langlands.HarmonicAnalysis.haarMeasure_map_rectangular
N Langlands.HarmonicAnalysis.padicRectangularHaarScaling
N Langlands.HarmonicAnalysis.productMeasure_map_diagonal
N Langlands.HarmonicAnalysis.productMeasure_map_matrix
N Langlands.HarmonicAnalysis.productMeasure_preserving_transvection
N Langlands.HarmonicAnalysis.productMeasure_preserving_transvection._simp_1_1
N Langlands.HarmonicAnalysis.productMeasure_preserving_transvection._simp_1_2
N Langlands.HarmonicAnalysis.rectangularCoordinates
N Langlands.HarmonicAnalysis.rectangularCoordinates._proof_1
N Langlands.HarmonicAnalysis.rectangularCoordinates._proof_2
N Langlands.HarmonicAnalysis.rectangularCoordinates._proof_3
N Langlands.HarmonicAnalysis.rectangularCoordinates_mul
```

### M024: `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof`

```text
N Langlands.HarmonicAnalysis.padicScalarHaarScaling
N Langlands.PadicField.TopologicalData.haarMeasure_regular
FDN Langlands.PadicField.TopologicalData.isCompact_integers
FDN Langlands.PadicField.TopologicalData.isOpen_integers
N Langlands.PadicField.TopologicalData.pseudoMetrizableSpace
N Langlands.PadicField.TopologicalData.secondCountableTopology
N Langlands.PadicField.TopologicalData.sigmaCompactSpace
N _private.Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof.0.Langlands.PadicField.TopologicalData.distribHaarChar_eq_normalizedAbsUnits
N _private.Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof.0.Langlands.PadicField.TopologicalData.residueCardinality_mul_measure_maximalIdeal
N _private.Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof.0.Langlands.PadicField.TopologicalData.smul_integers_eq
N _private.Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof.0.Langlands.PadicField.TopologicalData.uniformizer_ne_zero
N _private.Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof.0.Langlands.PadicField.TopologicalData.uniformizer_smul_integers
```

### M025: `Langlands.HarmonicAnalysis.RowSchwartzAction`

```text
F Langlands.HarmonicAnalysis.rowHomeomorph
F Langlands.HarmonicAnalysis.rowHomeomorph._proof_1
F Langlands.HarmonicAnalysis.rowHomeomorph._proof_2
F Langlands.HarmonicAnalysis.rowHomeomorph._proof_3
F Langlands.HarmonicAnalysis.rowHomeomorph._proof_4
F Langlands.HarmonicAnalysis.rowHomeomorph_apply
```

### M032: `Langlands.LocalField.Definitions`

```text
FDN Langlands.PadicField
FDN Langlands.PadicField.Carrier
FDN Langlands.PadicField.TopologicalData
FDN Langlands.PadicField.TopologicalData.localField
FDN Langlands.PadicField.TopologicalData.mk
N Langlands.PadicField.TopologicalData.moduleTopology
FDN Langlands.PadicField.TopologicalData.topology
FDN Langlands.PadicField.TopologicalData.valuativeRel
FDN Langlands.PadicField.algebra
N Langlands.PadicField.canonicalNormedAlgebra
N Langlands.PadicField.canonicalNormedField
N Langlands.PadicField.canonicalNormedField._proof_1
N Langlands.PadicField.canonicalTopology
FDN Langlands.PadicField.field
N Langlands.PadicField.finiteDimensional
FDN Langlands.PadicField.mk
```

### M033: `Langlands.LocalField.Normalization.Definitions`

```text
FDN Langlands.PadicField.TopologicalData.Integers
FDN Langlands.PadicField.TopologicalData.ResidueField
FDN Langlands.PadicField.TopologicalData.ResidueField._proof_1
FDN Langlands.PadicField.TopologicalData.discreteValuation
FDN Langlands.PadicField.TopologicalData.discreteValuation._proof_1
FDN Langlands.PadicField.TopologicalData.discreteValuation._proof_2
FDN Langlands.PadicField.TopologicalData.normalizedAbs
FDN Langlands.PadicField.TopologicalData.ord
FDN Langlands.PadicField.TopologicalData.residueCardinality
FDN Langlands.PadicField.TopologicalData.uniformizer
FDN Langlands.PadicField.TopologicalData.uniformizer._proof_1
```

### M034: `Langlands.LocalField.Normalization.Proof`

```text
FDN Langlands.PadicField.TopologicalData.discreteValuation_uniformizer
FDN Langlands.PadicField.TopologicalData.finite_residueField
FDN Langlands.PadicField.TopologicalData.finite_residueField._proof_1_1
FDN Langlands.PadicField.TopologicalData.normalizedAbs_le_iff_of_ne_zero
N Langlands.PadicField.TopologicalData.normalizedAbs_le_one_iff_mem_integers
FDN Langlands.PadicField.TopologicalData.normalizedAbs_mul
FDN Langlands.PadicField.TopologicalData.normalizedAbs_nonneg
FDN Langlands.PadicField.TopologicalData.normalizedAbs_of_ne_zero
FDN Langlands.PadicField.TopologicalData.normalizedAbs_one
FDN Langlands.PadicField.TopologicalData.normalizedAbs_pos
FDN Langlands.PadicField.TopologicalData.normalizedAbs_zero
FD Langlands.PadicField.TopologicalData.ord_inv
FDN Langlands.PadicField.TopologicalData.ord_mul
FDN Langlands.PadicField.TopologicalData.ord_one
FDN Langlands.PadicField.TopologicalData.ord_uniformizer
N Langlands.PadicField.TopologicalData.ord_zero
FDN Langlands.PadicField.TopologicalData.ord_zpow
FDN Langlands.PadicField.TopologicalData.residueCardinality_gt_one
N Langlands.PadicField.TopologicalData.topology_eq_canonicalModule
N Langlands.PadicField.TopologicalData.topology_eq_canonicalNormTopology
```

### M036: `Langlands.LocalField.Topology`

```text
FN Langlands.PadicField.TopologicalData.fieldT2
```

### M037: `Langlands.Representation.Category.Abelian`

```text
F Langlands.SmoothRep.epi_iff_surjective
F Langlands.SmoothRep.mono_iff_injective
F Langlands.SmoothRep.smoothRepProperty_containsZero
F Langlands.SmoothRep.smoothRepProperty_isClosedUnderQuotients
F Langlands.SmoothRep.smoothRepProperty_isClosedUnderSubobjects
F Langlands.SmoothRep.toRep_preservesEpimorphisms
F Langlands.SmoothRep.toRep_preservesMonomorphisms
```

### M038: `Langlands.Representation.Category.Basic`

```text
FD Langlands.SmoothRep
FD Langlands.SmoothRep.hom
FD Langlands.SmoothRep.instAddCommGroupVObjRepSmoothRepProperty
FD Langlands.SmoothRep.instModuleVObjRepSmoothRepProperty
FD Langlands.SmoothRep.isSmooth
FD Langlands.SmoothRep.of
FD Langlands.SmoothRep.ofHom
FD Langlands.SmoothRep.representation
F Langlands.SmoothRep.toRep
FD Langlands.smoothRepProperty
```

### M039: `Langlands.Representation.Category.Subquotients`

```text
F Langlands.SmoothRep.mkQ
F Langlands.SmoothRep.mkQ_surjective
F Langlands.SmoothRep.quotient
F Langlands.SmoothRep.quotient._proof_1
F Langlands.SmoothRep.stable
F Langlands.SmoothRep.subrepresentation
F Langlands.SmoothRep.subrepresentation._proof_1
F Langlands.SmoothRep.subtype
```

### M040: `Langlands.Representation.Category.Twist`

```text
FD Langlands.SmoothRep.twist
FD Langlands.SmoothRep.twist._proof_1
FD Langlands.SmoothRep.twistFunctor
FD Langlands.SmoothRep.twistFunctor._proof_1
FD Langlands.SmoothRep.twistFunctor._proof_2
```

### M041: `Langlands.Representation.Classification.StrongIndecomposability`

```text
F Langlands.Classification.IsStronglyIndecomposable
```

### M042: `Langlands.Representation.Classification.StrongIndecomposabilityLatticeTransferProof`

```text
F Langlands.Classification.IsStronglyIndecomposable.eq_1
F Langlands.Classification.strongIndecomposabilityLatticeTransfer
F Langlands.Classification.stronglyIndecomposable_iff_essential_interval
F Langlands.Classification.stronglyIndecomposable_iff_of_orderIso
F _private.Langlands.Representation.Classification.StrongIndecomposabilityLatticeTransferProof.0.Langlands.Classification.nonbottom_inf_essential_interval
F _private.Langlands.Representation.Classification.StrongIndecomposabilityLatticeTransferProof.0.Langlands.Classification.nonbottom_inf_transport
```

### M043: `Langlands.Representation.Classification.StrongIndecomposabilityLatticeTransferStatement`

```text
F Langlands.Classification.StrongIndecomposabilityLatticeTransferStatement
```

### M044: `Langlands.Representation.Compact.Definitions`

```text
FD Langlands.Compact.averageMap
FD Langlands.Compact.averageMap._proof_1
FD Langlands.Compact.averageMap._proof_2
FD Langlands.Compact.finite_orbit_of_smooth
FD Langlands.Compact.finite_orbit_of_smooth._proof_1_1
```

### M045: `Langlands.Representation.Compact.FiniteMean`

```text
FD Langlands.Compact.finiteMean
FD Langlands.Compact.finiteMean_comp
FD Langlands.Compact.finite_orbit_prod
FD Langlands.Compact.orbit
FD Langlands.Compact.orbitAction
FD Langlands.Compact.orbitAction._proof_1
FD Langlands.Compact.orbitAction._proof_2
FD Langlands.Compact.orbitAction._proof_3
FD Langlands.Compact.orbitMap
FD Langlands.Compact.orbitMap._proof_1
FD Langlands.Compact.orbitMap._proof_2
FD Langlands.Compact.orbitMap._proof_3
FD Langlands.Compact.orbitMean
FD Langlands.Compact.orbitMean_add
FD Langlands.Compact.orbitMean_add._proof_1_1
FD Langlands.Compact.orbitMean_add._proof_1_2
FD Langlands.Compact.orbitMean_add._proof_1_3
FD Langlands.Compact.orbitMean_eq_finiteMean
FD Langlands.Compact.orbitMean_map
FD Langlands.Compact.orbitMean_smul
FD Langlands.Compact.orbitMean_smul._proof_1_1
FD Langlands.Compact.orbitNonempty
FD Langlands.Compact.orbitPretransitive
FD Langlands.Compact.representationAction
FD Langlands.Compact.representationAction._proof_1
FD Langlands.Compact.representationAction._proof_2
FD _private.Langlands.Representation.Compact.FiniteMean.0.Langlands.Compact.fiberEquiv
FD _private.Langlands.Representation.Compact.FiniteMean.0.Langlands.Compact.fiberEquiv._proof_1
FD _private.Langlands.Representation.Compact.FiniteMean.0.Langlands.Compact.fiberEquiv._proof_2
FD _private.Langlands.Representation.Compact.FiniteMean.0.Langlands.Compact.fiberEquiv._proof_3
FD _private.Langlands.Representation.Compact.FiniteMean.0.Langlands.Compact.fiberEquiv._proof_4
FD _private.Langlands.Representation.Compact.FiniteMean.0.Langlands.Compact.fiberEquiv._proof_5
FD _private.Langlands.Representation.Compact.FiniteMean.0.Langlands.Compact.fiberEquiv._proof_6
```

### M046: `Langlands.Representation.Compact.OrbitMeanTranslation`

```text
FD Langlands.Compact.orbitMean_apply
```

### M050: `Langlands.Representation.Derivative.Homogeneity`

```text
FD Langlands.Derivative.HasNonzeroDerivative
F Langlands.Derivative.IsHomogeneous
FD Langlands.Derivative.hasNonzeroDerivative_iff
FD Langlands.Derivative.hasNonzeroDerivative_iff.match_1_1
F Langlands.Derivative.isHomogeneous_iff
F Langlands.Derivative.le_level_of_hasNonzeroDerivative
FD Langlands.Derivative.level
FD Langlands.Derivative.level_eq_zero_iff
F Langlands.Derivative.level_eq_zero_of_subsingleton
FD Langlands.Derivative.mirabolicDerivativeOfOrder
F Langlands.Derivative.mirabolicDerivativeOfOrder_obj_subsingleton
F Langlands.Derivative.mirabolicDerivativeOfOrder_one
F Langlands.Derivative.mirabolicDerivative_obj_subsingleton
FD Langlands.Derivative.mirabolicRankCast
F Langlands.Derivative.mirabolicRankCast_obj_subsingleton
FD Langlands.Derivative.mirabolic_rank_eq_of_order
FD Langlands.Derivative.mirabolic_rank_eq_of_order._proof_1_1
F Langlands.Derivative.phiMinusIterate_obj_subsingleton
F _private.Langlands.Representation.Derivative.Homogeneity.0.Langlands.Derivative.subsingleton_of_surjective
```

### M051: `Langlands.Representation.Derivative.Iteration`

```text
FD Langlands.Derivative.mirabolicDerivative
F Langlands.Derivative.mirabolicDerivative_zero
FD Langlands.Derivative.phiMinusIterate
FD Langlands.Derivative.phiMinusIterate._f
FD Langlands.Derivative.phiMinusIterate.match_1
```

### M052: `Langlands.Representation.Derivative.LevelCalculus`

```text
F Langlands.Derivative.LevelCalculus.codRestrict
F Langlands.Derivative.LevelCalculus.codRestrict._proof_1
F Langlands.Derivative.LevelCalculus.codRestrict._proof_2
F Langlands.Derivative.LevelCalculus.codRestrict_injective
F Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_iff_of_iso
F Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_iff_of_iso.match_1_1
F Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_level
F Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff
F Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff._proof_1_1
F Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff._proof_1_2
F Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff._proof_1_3
F Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff._proof_1_4
F Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff._proof_1_5
F Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff_cast
F Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff_cast._proof_1_1
F Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff_cast._proof_1_2
F Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff_cast._proof_1_3
F Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff_cast._proof_1_4
F Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff_cast._proof_1_5
F Langlands.Derivative.LevelCalculus.hasNonzeroDerivative_succ_iff_cast._proof_1_6
F Langlands.Derivative.LevelCalculus.hom_inv_apply
F Langlands.Derivative.LevelCalculus.isIso_of_bijective
F Langlands.Derivative.LevelCalculus.isoRange
F Langlands.Derivative.LevelCalculus.isoRange._proof_1
F Langlands.Derivative.LevelCalculus.isoRange._proof_2
F Langlands.Derivative.LevelCalculus.iso_hom_injective
F Langlands.Derivative.LevelCalculus.level_eq_level_phiMinus_succ
F Langlands.Derivative.LevelCalculus.level_le_level_phiMinus_succ
F Langlands.Derivative.LevelCalculus.level_le_level_phiMinus_succ._proof_1_1
F Langlands.Derivative.LevelCalculus.level_le_level_phiMinus_succ._proof_1_2
F Langlands.Derivative.LevelCalculus.level_le_level_phiMinus_succ._proof_1_3
F Langlands.Derivative.LevelCalculus.level_le_level_phiMinus_succ._proof_1_4
F Langlands.Derivative.LevelCalculus.level_le_level_phiMinus_succ._proof_1_5
F Langlands.Derivative.LevelCalculus.level_le_of_imp
F Langlands.Derivative.LevelCalculus.level_le_one_of_subsingleton_phiMinus
F Langlands.Derivative.LevelCalculus.level_pos
F Langlands.Derivative.LevelCalculus.mirabolicDerivative_succ_cast_obj
F Langlands.Derivative.LevelCalculus.nontrivial_iff_of_iso
F Langlands.Derivative.LevelCalculus.nontrivial_mirabolicDerivative_cast_congr
F Langlands.Derivative.LevelCalculus.nontrivial_of_hasNonzeroDerivative
F Langlands.Derivative.LevelCalculus.nontrivial_of_injective
F Langlands.Derivative.LevelCalculus.nontrivial_of_level_ne_zero
F Langlands.Derivative.LevelCalculus.nontrivial_phiMinus_iff
F Langlands.Derivative.LevelCalculus.nontrivial_phiMinus_iff._proof_1_1
F Langlands.Derivative.LevelCalculus.nontrivial_phiMinus_iff._proof_1_2
F Langlands.Derivative.LevelCalculus.subrepresentation_nontrivial
F Langlands.Derivative.LevelCalculus.top_ne_bot
```

### M053: `Langlands.Representation.Derivative.MinusVanishing`

```text
FD Langlands.Derivative.Mirabolic.characterAverage_congr
FD Langlands.Derivative.Mirabolic.characterAverage_eq_zero_of_le
FD Langlands.Derivative.Mirabolic.coordinateCharacter
FD Langlands.Derivative.Mirabolic.coordinateCharacter._proof_1
FD Langlands.Derivative.Mirabolic.coordinateCharacter_apply
FD Langlands.Derivative.Mirabolic.coordinateCharacter_eq_of_sub_mem
FD Langlands.Derivative.Mirabolic.coordinateCharacter_eq_of_sub_mem._abel_1_1
FD Langlands.Derivative.Mirabolic.coordinateCharacter_eq_one
FD Langlands.Derivative.Mirabolic.coordinateCharacter_zero
FD Langlands.Derivative.Mirabolic.eq_zero_of_forall_characterAverage_eq_zero
FD Langlands.Derivative.Mirabolic.eq_zero_of_forall_characterAverage_eq_zero._proof_1_1
FD Langlands.Derivative.Mirabolic.eq_zero_of_forall_characterAverage_eq_zero._simp_1_2
FD Langlands.Derivative.Mirabolic.eq_zero_of_forall_characterAverage_eq_zero._simp_1_3
FD Langlands.Derivative.Mirabolic.exists_forall_characterAverage_eq_zero
FD Langlands.Derivative.Mirabolic.exists_lastRow_eq_of_ne_zero
FD Langlands.Derivative.Mirabolic.exists_mem_latticeBox
FD Langlands.Derivative.Mirabolic.isCompact_radicalBox
FD Langlands.Derivative.Mirabolic.isOpen_ker_coordinateCharacter
FD Langlands.Derivative.Mirabolic.levi_inv_mem_relations
FD Langlands.Derivative.Mirabolic.levi_inv_mem_relations._simp_1_1
FD Langlands.Derivative.Mirabolic.levi_inv_mem_relations._simp_1_2
FD Langlands.Derivative.Mirabolic.mem_radicalBox
FD Langlands.Derivative.Mirabolic.radicalBox
FD Langlands.Derivative.Mirabolic.radicalBox._proof_1
FD Langlands.Derivative.Mirabolic.radicalBox._proof_2
FD Langlands.Derivative.Mirabolic.radicalBox._proof_3
FD Langlands.Derivative.Mirabolic.radicalBox_mono
FD Langlands.Derivative.Mirabolic.subsingleton_of_psiMinus_phiMinus
FD Langlands.Derivative.Mirabolic.subsingleton_of_psiMinus_phiMinus._simp_1_1
```

### M054: `Langlands.Representation.Derivative.MirabolicCharacter`

```text
FD Langlands.Derivative.Mirabolic.lastCoordinate
FD Langlands.Derivative.Mirabolic.lastCoordinate._proof_1
FD Langlands.Derivative.Mirabolic.lastCoordinate._proof_2
FD Langlands.Derivative.Mirabolic.lastCoordinate._proof_3
FD Langlands.Derivative.Mirabolic.lastCoordinate._proof_4
FD Langlands.Derivative.Mirabolic.mulVec_last
FD Langlands.Derivative.Mirabolic.theta
F Langlands.Derivative.Mirabolic.thetaContinuous
F Langlands.Derivative.Mirabolic.thetaContinuous._proof_1
FD Langlands.Derivative.Mirabolic.theta_isInvariant
F Langlands.Derivative.Mirabolic.theta_isOpen_ker
FD Langlands.Derivative.Mirabolic.theta_radicalElement
FD Langlands.PadicField.TopologicalData.mirabolicTheta
F Langlands.PadicField.TopologicalData.mirabolicTheta_isOpen_ker
```

### M055: `Langlands.Representation.Derivative.MirabolicDerivativeDetectionProof`

```text
F Langlands.Derivative.mirabolicDerivativeDetection
```

### M056: `Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement`

```text
FD Langlands.Derivative.MirabolicDerivativeDetection
```

### M057: `Langlands.Representation.Derivative.MirabolicDerivativeVanishing`

```text
FD Langlands.Derivative.Mirabolic.derivativeDetection
FD Langlands.Derivative.Mirabolic.radical_acts_trivially_zero
FD Langlands.Derivative.Mirabolic.relations_one_eq_bot
FD Langlands.Derivative.Mirabolic.subsingleton_of_forall_mirabolicDerivative
FD Langlands.Derivative.Mirabolic.subsingleton_of_forall_mirabolicDerivativeOfOrder
FD Langlands.Derivative.Mirabolic.subsingleton_of_forall_mirabolicDerivativeOfOrder._proof_1_1
FD Langlands.Derivative.Mirabolic.subsingleton_of_forall_mirabolicDerivativeOfOrder._proof_1_2
FD Langlands.Derivative.Mirabolic.subsingleton_of_forall_mirabolicDerivativeOfOrder._proof_1_3
FD Langlands.Derivative.Mirabolic.subsingleton_of_psiMinus_zero
FD Langlands.Derivative.Mirabolic.subsingleton_rankCast_mirabolicDerivative_congr
```

### M058: `Langlands.Representation.Derivative.MirabolicHighestDerivativeDescent`

```text
F Langlands.Derivative.Mirabolic.eq_zero_of_forall_mem_relations
F Langlands.Derivative.Mirabolic.eq_zero_of_forall_mem_relations._simp_1_1
F Langlands.Derivative.Mirabolic.radical_acts_trivially_of_phiMinus
```

### M059: `Langlands.Representation.Derivative.MirabolicHighestLayerLift`

```text
F Langlands.Derivative.Mirabolic.HighestLayer.exists_levi_translates_mem
F Langlands.Derivative.Mirabolic.HighestLayer.exists_levi_translates_mem._proof_1_2
F Langlands.Derivative.Mirabolic.HighestLayer.exists_levi_translates_mem._simp_1_1
F Langlands.Derivative.Mirabolic.HighestLayer.exists_mem_liftStep
F Langlands.Derivative.Mirabolic.HighestLayer.exists_radical_difference
F Langlands.Derivative.Mirabolic.HighestLayer.hasNonzeroDerivative_of_subrepresentation
F Langlands.Derivative.Mirabolic.HighestLayer.hasNonzeroDerivative_of_subrepresentation._proof_1_1
F Langlands.Derivative.Mirabolic.HighestLayer.hasNonzeroDerivative_of_subrepresentation._proof_1_2
F Langlands.Derivative.Mirabolic.HighestLayer.hasNonzeroDerivative_of_subrepresentation._proof_1_3
F Langlands.Derivative.Mirabolic.HighestLayer.hasNonzeroDerivative_of_subrepresentation._proof_1_4
F Langlands.Derivative.Mirabolic.HighestLayer.hasNonzeroDerivative_one_of_subrepresentation
F Langlands.Derivative.Mirabolic.HighestLayer.imageStep
F Langlands.Derivative.Mirabolic.HighestLayer.imageStep._proof_1
F Langlands.Derivative.Mirabolic.HighestLayer.imageStep._proof_2
F Langlands.Derivative.Mirabolic.HighestLayer.imageStep._proof_3
F Langlands.Derivative.Mirabolic.HighestLayer.imageStep._proof_4
F Langlands.Derivative.Mirabolic.HighestLayer.imageStep_bot
F Langlands.Derivative.Mirabolic.HighestLayer.imageStep_liftStep
F Langlands.Derivative.Mirabolic.HighestLayer.imageStep_mono
F Langlands.Derivative.Mirabolic.HighestLayer.inf_imageStep_ne_bot_iff
F Langlands.Derivative.Mirabolic.HighestLayer.isOpen_ker_one
F Langlands.Derivative.Mirabolic.HighestLayer.le_liftStep_imageStep
F Langlands.Derivative.Mirabolic.HighestLayer.level_subrepresentation_le
F Langlands.Derivative.Mirabolic.HighestLayer.liftStep
F Langlands.Derivative.Mirabolic.HighestLayer.liftStep._proof_1
F Langlands.Derivative.Mirabolic.HighestLayer.liftStep._proof_2
F Langlands.Derivative.Mirabolic.HighestLayer.liftStep._proof_3
F Langlands.Derivative.Mirabolic.HighestLayer.liftStep._proof_4
F Langlands.Derivative.Mirabolic.HighestLayer.liftStep._proof_5
F Langlands.Derivative.Mirabolic.HighestLayer.liftStep_imageStep
F Langlands.Derivative.Mirabolic.HighestLayer.liftStep_mono
N Langlands.Derivative.Mirabolic.HighestLayer.map_inv_mul_haar
N Langlands.Derivative.Mirabolic.HighestLayer.map_inv_mul_haar_iff
N Langlands.Derivative.Mirabolic.HighestLayer.map_inv_mul_haar_iff._proof_1_1
F Langlands.Derivative.Mirabolic.HighestLayer.mem_liftStep
F Langlands.Derivative.Mirabolic.HighestLayer.mem_relations_subrepresentation
F Langlands.Derivative.Mirabolic.HighestLayer.ne_bot_iff_exists
F Langlands.Derivative.Mirabolic.HighestLayer.nontrivial_iff_of_bijective
F Langlands.Derivative.Mirabolic.HighestLayer.nontrivial_subrepresentation_iff
N Langlands.Derivative.Mirabolic.HighestLayer.phiMinusCharacter_eq_modulus
F Langlands.Derivative.Mirabolic.HighestLayer.phiMinusSubIso
F Langlands.Derivative.Mirabolic.HighestLayer.phiMinusSubIso._proof_1
F Langlands.Derivative.Mirabolic.HighestLayer.phiMinus_map_subtype_injective
F Langlands.Derivative.Mirabolic.HighestLayer.psiImage
F Langlands.Derivative.Mirabolic.HighestLayer.psiImage._proof_1
F Langlands.Derivative.Mirabolic.HighestLayer.psiImage._proof_2
F Langlands.Derivative.Mirabolic.HighestLayer.psiImage._proof_3
F Langlands.Derivative.Mirabolic.HighestLayer.psiImage._proof_4
F Langlands.Derivative.Mirabolic.HighestLayer.psiImage._proof_5
F Langlands.Derivative.Mirabolic.HighestLayer.psiIso
F Langlands.Derivative.Mirabolic.HighestLayer.psiIso._proof_1
F Langlands.Derivative.Mirabolic.HighestLayer.psiIso._proof_2
F Langlands.Derivative.Mirabolic.HighestLayer.psiIso._proof_3
N Langlands.Derivative.Mirabolic.HighestLayer.psiMinusCharacter_eq_modulus
F Langlands.Derivative.Mirabolic.HighestLayer.psiMinusQuotient_injective
F Langlands.Derivative.Mirabolic.HighestLayer.psiMinus_map_subtype_injective
F Langlands.Derivative.Mirabolic.HighestLayer.psiPreimage
F Langlands.Derivative.Mirabolic.HighestLayer.psiPreimage._proof_1
F Langlands.Derivative.Mirabolic.HighestLayer.psiPreimage._proof_2
F Langlands.Derivative.Mirabolic.HighestLayer.psiPreimage._proof_3
F Langlands.Derivative.Mirabolic.HighestLayer.psiPreimage._proof_4
F Langlands.Derivative.Mirabolic.HighestLayer.radical_trivial_of_level_le_one
F Langlands.Derivative.Mirabolic.HighestLayer.radical_trivial_of_level_le_one._proof_1_1
F Langlands.Derivative.Mirabolic.HighestLayer.radical_trivial_subrepresentation
F Langlands.Derivative.Mirabolic.HighestLayer.range_phiMinus_map_subtype
F Langlands.Derivative.Mirabolic.HighestLayer.stepIso
F Langlands.Derivative.Mirabolic.HighestLayer.stepIso._proof_1
F Langlands.Derivative.Mirabolic.HighestLayer.stepIso._proof_2
F Langlands.Derivative.Mirabolic.HighestLayer.stepIso._proof_3
F Langlands.Derivative.Mirabolic.HighestLayer.stepIso._proof_4
F Langlands.Derivative.Mirabolic.HighestLayer.stepIso._proof_5
F Langlands.Derivative.Mirabolic.HighestLayer.stepIso._proof_6
F Langlands.Derivative.Mirabolic.HighestLayer.stepIso._proof_7
F Langlands.Derivative.Mirabolic.HighestLayer.successor_mem
```

### M060: `Langlands.Representation.Derivative.MirabolicHighestLayerPlus`

```text
F Langlands.Derivative.Mirabolic.HighestLayer.exists_compact_rows
F Langlands.Derivative.Mirabolic.HighestLayer.exists_cutoff
F Langlands.Derivative.Mirabolic.HighestLayer.exists_latticeBox_fixing
F Langlands.Derivative.Mirabolic.HighestLayer.exists_latticeBox_fixing._simp_1_1
F Langlands.Derivative.Mirabolic.HighestLayer.exists_openSubgroup_fixing
F Langlands.Derivative.Mirabolic.HighestLayer.exists_orbitFun_eq_near
F Langlands.Derivative.Mirabolic.HighestLayer.exists_orbitFun_eq_zero_of_mem_relations
F Langlands.Derivative.Mirabolic.HighestLayer.exists_phiPlusPost_eq_of_mem
F Langlands.Derivative.Mirabolic.HighestLayer.exists_plusStep
F Langlands.Derivative.Mirabolic.HighestLayer.exists_plus_mul_levi
F Langlands.Derivative.Mirabolic.HighestLayer.exists_relation_orbitFun_eq
F Langlands.Derivative.Mirabolic.HighestLayer.exists_relation_orbitFun_eq._abel_1_1
F Langlands.Derivative.Mirabolic.HighestLayer.isCompact_quotientSupport_of_projectionRow
F Langlands.Derivative.Mirabolic.HighestLayer.isCompact_quotientSupport_of_projectionRow._simp_1_1
F Langlands.Derivative.Mirabolic.HighestLayer.isCompact_quotientSupport_of_projectionRow._simp_1_2
F Langlands.Derivative.Mirabolic.HighestLayer.isCompact_quotientSupport_of_projectionRow._simp_1_3
F Langlands.Derivative.Mirabolic.HighestLayer.liftStep_bot
F Langlands.Derivative.Mirabolic.HighestLayer.mem_liftStep_top
F Langlands.Derivative.Mirabolic.HighestLayer.mem_range_plusStepMap
F Langlands.Derivative.Mirabolic.HighestLayer.mulVec_last_eq_dotProduct
F Langlands.Derivative.Mirabolic.HighestLayer.mul_radicalElement
F Langlands.Derivative.Mirabolic.HighestLayer.orbitFun
F Langlands.Derivative.Mirabolic.HighestLayer.orbitFun_add
F Langlands.Derivative.Mirabolic.HighestLayer.orbitFun_apply
F Langlands.Derivative.Mirabolic.HighestLayer.orbitFun_covariant
F Langlands.Derivative.Mirabolic.HighestLayer.orbitFun_isCompact
F Langlands.Derivative.Mirabolic.HighestLayer.orbitFun_mul
F Langlands.Derivative.Mirabolic.HighestLayer.orbitFun_plus_mul
F Langlands.Derivative.Mirabolic.HighestLayer.orbitFun_radicalElement
F Langlands.Derivative.Mirabolic.HighestLayer.orbitFun_smul
F Langlands.Derivative.Mirabolic.HighestLayer.orbitFun_sub
F Langlands.Derivative.Mirabolic.HighestLayer.orbitFun_sum
F Langlands.Derivative.Mirabolic.HighestLayer.orbitFun_zero
F Langlands.Derivative.Mirabolic.HighestLayer.phiMinus_orbitFun
F Langlands.Derivative.Mirabolic.HighestLayer.phiPlusCharacter_smul_phiMinusCharacter_smul
F Langlands.Derivative.Mirabolic.HighestLayer.plusStepMap
F Langlands.Derivative.Mirabolic.HighestLayer.plusStepMap_apply
F Langlands.Derivative.Mirabolic.HighestLayer.plusStepMap_injective
F Langlands.Derivative.Mirabolic.HighestLayer.projectionRow
F Langlands.Derivative.Mirabolic.HighestLayer.projectionRow._proof_1
F Langlands.Derivative.Mirabolic.HighestLayer.projectionRow.eq_1
F Langlands.Derivative.Mirabolic.HighestLayer.projectionRow_mem_of_orbitFun_ne_zero
F Langlands.Derivative.Mirabolic.HighestLayer.projectionRow_ne_zero
F Langlands.Derivative.Mirabolic.HighestLayer.projectionRow_plus_mul
F Langlands.Derivative.Mirabolic.HighestLayer.relationsSubtype
F Langlands.Derivative.Mirabolic.HighestLayer.relationsSubtype._proof_1
F Langlands.Derivative.Mirabolic.HighestLayer.sum_character_out
F Langlands.Derivative.Mirabolic.HighestLayer.theta
F Langlands.Derivative.Mirabolic.HighestLayer.theta._proof_1
F Langlands.Derivative.Mirabolic.HighestLayer.theta._proof_2
F Langlands.Derivative.Mirabolic.HighestLayer.theta._proof_3
F Langlands.Derivative.Mirabolic.HighestLayer.theta._proof_4
F Langlands.Derivative.Mirabolic.HighestLayer.theta._proof_5
F Langlands.Derivative.Mirabolic.HighestLayer.theta._proof_6
F Langlands.Derivative.Mirabolic.HighestLayer.theta._proof_7
F Langlands.Derivative.Mirabolic.HighestLayer.thetaFun
F Langlands.Derivative.Mirabolic.HighestLayer.thetaFun._proof_1
F Langlands.Derivative.Mirabolic.HighestLayer.thetaFun._proof_2
F Langlands.Derivative.Mirabolic.HighestLayer.thetaInv
F Langlands.Derivative.Mirabolic.HighestLayer.thetaInv._proof_1
F Langlands.Derivative.Mirabolic.HighestLayer.thetaInv_theta
F Langlands.Derivative.Mirabolic.HighestLayer.theta_eval
F Langlands.Derivative.Mirabolic.HighestLayer.theta_injective
F Langlands.Derivative.Mirabolic.HighestLayer.theta_surjective
F Langlands.Derivative.Mirabolic.HighestLayer.theta_thetaInv
```

### M061: `Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps`

```text
F Langlands.Derivative.Mirabolic.HighestLayer.mem_range_phiPlusPost
F Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPost
F Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPost._proof_1
F Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPost._proof_2
F Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPost._proof_3
F Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPost._proof_4
F Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPost_injective
F Langlands.Derivative.Mirabolic.HighestLayer.psiMinusQuotient_psiPlusBaseEmbedding
F Langlands.Derivative.Mirabolic.HighestLayer.psiPlusBaseEmbedding
F Langlands.Derivative.Mirabolic.HighestLayer.psiPlusBaseEmbedding._proof_1
F Langlands.Derivative.Mirabolic.HighestLayer.psiPlusBaseEmbedding_injective
F Langlands.Derivative.Mirabolic.HighestLayer.psiPlusBaseEmbedding_quotient
F Langlands.Derivative.Mirabolic.HighestLayer.psiPlusBaseEmbedding_range
F _private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPostValue
F _private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPostValue._proof_1
F _private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPostValue._proof_2
F _private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPostValue._proof_3
F _private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPostValue._proof_4
F _private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPostValue._proof_5
F _private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPostValue._proof_6
F _private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.phiPlusPostValue._proof_7
F _private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.psiPlusBaseLinear
F _private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.psiPlusBaseLinear._proof_1
F _private.Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps.0.Langlands.Derivative.Mirabolic.HighestLayer.psiPlusBaseLinear._proof_2
```

### M062: `Langlands.Representation.Derivative.MirabolicHighestLayerProof`

```text
F Langlands.Derivative.Mirabolic.HighestLayer.IsPlusLayerImage
F Langlands.Derivative.Mirabolic.HighestLayer.IsPlusLayerImage._proof_1
F Langlands.Derivative.Mirabolic.HighestLayer.IsPlusLayerImage._proof_2
F Langlands.Derivative.Mirabolic.HighestLayer.derivative_cast
F Langlands.Derivative.Mirabolic.HighestLayer.derivative_obj_succ
F Langlands.Derivative.Mirabolic.HighestLayer.exists_layer
F Langlands.Derivative.Mirabolic.HighestLayer.exists_layer._proof_1_1
F Langlands.Derivative.Mirabolic.HighestLayer.exists_layer._proof_1_2
F Langlands.Derivative.Mirabolic.HighestLayer.exists_layer._proof_1_3
F Langlands.Derivative.Mirabolic.HighestLayer.exists_layer._proof_1_4
F Langlands.Derivative.Mirabolic.HighestLayer.exists_layer._proof_1_5
F Langlands.Derivative.Mirabolic.HighestLayer.exists_layer._proof_1_6
F Langlands.Derivative.Mirabolic.HighestLayer.isPlusLayerImage_liftStep
F Langlands.Derivative.Mirabolic.HighestLayer.isPlusLayerImage_succ
F Langlands.Derivative.Mirabolic.HighestLayer.isPlusLayerImage_top
F Langlands.Derivative.Mirabolic.HighestLayer.isPlusLayerImage_zero
F Langlands.Derivative.Mirabolic.HighestLayer.plusLayerSucc
F Langlands.Derivative.Mirabolic.HighestLayer.plusLayerSucc_succ
F Langlands.Derivative.Mirabolic.HighestLayer.plusLayerSucc_zero
F Langlands.Derivative.mirabolicHighestLayer
F Langlands.Derivative.mirabolicHighestLayer._proof_1_1
F Langlands.Derivative.mirabolicHighestLayer._proof_1_2
F Langlands.Derivative.mirabolicHighestLayer_plusModel
F Langlands.Derivative.mirabolicHighestLayer_plusModel._proof_1_1
F Langlands.Derivative.mirabolicHighestLayer_plusModel._proof_1_2
F Langlands.Derivative.mirabolicHighestLayer_plusModel._proof_1_3
F Langlands.Derivative.mirabolicHighestLayer_plusModel._proof_1_4
```

### M063: `Langlands.Representation.Derivative.MirabolicHighestLayerStatement`

```text
F Langlands.Derivative.MirabolicHighestLayerStatement
```

### M064: `Langlands.Representation.Derivative.MirabolicLatticeBox`

```text
FD Langlands.Derivative.Mirabolic.character_dotProduct_eq_one
FD Langlands.Derivative.Mirabolic.character_mul_eq_one
FD Langlands.Derivative.Mirabolic.coe_latticeBox
FD Langlands.Derivative.Mirabolic.coe_latticeBox._simp_1_1
F Langlands.Derivative.Mirabolic.eq_one_of_smul_eq_self
FD Langlands.Derivative.Mirabolic.exists_latticeBox_subset
FD Langlands.Derivative.Mirabolic.finite_latticeBox_quotient
FD Langlands.Derivative.Mirabolic.isCompact_latticeBox
FD Langlands.Derivative.Mirabolic.isOpen_latticeBox
FD Langlands.Derivative.Mirabolic.latticeBox
FD Langlands.Derivative.Mirabolic.latticeBox_mono
FD Langlands.Derivative.Mirabolic.mem_latticeBox
FD Langlands.Derivative.Mirabolic.mem_latticeBox._simp_1_2
FD Langlands.Derivative.Mirabolic.mem_latticeBox_of_forall_character_eq_one
FD Langlands.Derivative.Mirabolic.sum_out_eq_zero
```

### M065: `Langlands.Representation.Derivative.MirabolicMinus`

```text
FD Langlands.Derivative.Mirabolic.continuousPullback
FD Langlands.Derivative.Mirabolic.continuousPullback._proof_1
FD Langlands.Derivative.Mirabolic.continuousPullbackFunctor
FD Langlands.Derivative.Mirabolic.continuousPullbackFunctor._proof_1
FD Langlands.Derivative.Mirabolic.continuousPullbackFunctor._proof_2
FD Langlands.Derivative.Mirabolic.continuousPullbackMap
FD Langlands.Derivative.Mirabolic.continuousPullbackMap._proof_1
FD Langlands.Derivative.Mirabolic.continuousPullbackMap._proof_2
FD Langlands.Derivative.Mirabolic.isOpen_ker_phiMinusCharacter
FD Langlands.Derivative.Mirabolic.isOpen_ker_psiMinusCharacter
F Langlands.Derivative.Mirabolic.ker_phiMinusQuotient
F Langlands.Derivative.Mirabolic.ker_psiMinusQuotient
FD Langlands.Derivative.Mirabolic.phiMinus
FDN Langlands.Derivative.Mirabolic.phiMinusCharacter
F Langlands.Derivative.Mirabolic.phiMinusQuotient
F Langlands.Derivative.Mirabolic.phiMinusQuotient_radical
F Langlands.Derivative.Mirabolic.phiMinusQuotient_surjective
FD Langlands.Derivative.Mirabolic.phiMinusUnnormalized
FD Langlands.Derivative.Mirabolic.phiMinusUnnormalized._proof_1
FD Langlands.Derivative.Mirabolic.phiMinusUnnormalized._proof_2
FD Langlands.Derivative.Mirabolic.phiMinusUnnormalized._proof_3
FD Langlands.Derivative.Mirabolic.phiMinusUnnormalized._proof_4
FD Langlands.Derivative.Mirabolic.phiMinusUnnormalized._proof_5
F Langlands.Derivative.Mirabolic.phiMinus_action
F Langlands.Derivative.Mirabolic.phiMinus_map_quotient
FD Langlands.Derivative.Mirabolic.psiMinus
FDN Langlands.Derivative.Mirabolic.psiMinusCharacter
FDN Langlands.Derivative.Mirabolic.psiMinusCharacter._proof_1
F Langlands.Derivative.Mirabolic.psiMinusQuotient
F Langlands.Derivative.Mirabolic.psiMinusQuotient_surjective
FD Langlands.Derivative.Mirabolic.psiMinusUnnormalized
FD Langlands.Derivative.Mirabolic.psiMinusUnnormalized._proof_1
FD Langlands.Derivative.Mirabolic.psiMinusUnnormalized._proof_2
FD Langlands.Derivative.Mirabolic.psiMinusUnnormalized._proof_3
FD Langlands.Derivative.Mirabolic.psiMinusUnnormalized._proof_4
FD Langlands.Derivative.Mirabolic.psiMinusUnnormalized._proof_5
F Langlands.Derivative.Mirabolic.psiMinus_action
F Langlands.Derivative.Mirabolic.psiMinus_map_quotient
```

### M070: `Langlands.Representation.Derivative.MirabolicPhiMinusNondegeneratePairing`

```text
F Langlands.Derivative.Mirabolic.radicalRelations_stable
F Langlands.Derivative.Mirabolic.radicalRelations_stable._simp_1_1
```

### M071: `Langlands.Representation.Derivative.MirabolicPlus`

```text
F Langlands.Derivative.Mirabolic.continuous_thetaPlus
F Langlands.Derivative.Mirabolic.isOpen_ker_thetaPlus
F Langlands.Derivative.Mirabolic.phiPlusEval
F Langlands.Derivative.Mirabolic.phiPlusEval_covariant
F Langlands.Derivative.Mirabolic.phiPlusEval_exists_openSubgroup
F Langlands.Derivative.Mirabolic.phiPlusEval_injective
F Langlands.Derivative.Mirabolic.phiPlusEval_isCompact_quotientSupport
F Langlands.Derivative.Mirabolic.phiPlusMk
F Langlands.Derivative.Mirabolic.phiPlusUnnormalized
F Langlands.Derivative.Mirabolic.phiPlusUnnormalized._proof_1
F Langlands.Derivative.Mirabolic.plusLastCoordinate
F Langlands.Derivative.Mirabolic.plusLastCoordinate._proof_1
F Langlands.Derivative.Mirabolic.plusLastCoordinate._proof_2
F Langlands.Derivative.Mirabolic.plusLastCoordinate._proof_3
F Langlands.Derivative.Mirabolic.plusLastCoordinate._proof_4
F Langlands.Derivative.Mirabolic.plusTwistFunctor
F Langlands.Derivative.Mirabolic.plusTwistFunctor._proof_1
F Langlands.Derivative.Mirabolic.plusTwistFunctor._proof_2
F Langlands.Derivative.Mirabolic.plusTwistFunctor._proof_3
F Langlands.Derivative.Mirabolic.plusTwistRepresentation
F Langlands.Derivative.Mirabolic.plusTwistRepresentation._proof_1
F Langlands.Derivative.Mirabolic.psiPlusUnnormalized
F Langlands.Derivative.Mirabolic.psiPlusUnnormalized._proof_1
F Langlands.Derivative.Mirabolic.psiPlusUnnormalized._proof_2
F Langlands.Derivative.Mirabolic.thetaPlus
F Langlands.Derivative.Mirabolic.thetaPlusContinuous
F Langlands.Derivative.Mirabolic.thetaPlusContinuous._proof_1
F Langlands.Derivative.Mirabolic.thetaPlus_apply
F Langlands.Derivative.Mirabolic.thetaPlus_isOpen_ker
```

### M072: `Langlands.Representation.Derivative.MirabolicPlusNormalization`

```text
F Langlands.Derivative.Mirabolic.isOpen_ker_phiPlusCharacter
F Langlands.Derivative.Mirabolic.isOpen_ker_psiPlusCharacter
F Langlands.Derivative.Mirabolic.phiMinusCharacter.eq_1
F Langlands.Derivative.Mirabolic.phiPlus
F Langlands.Derivative.Mirabolic.phiPlusCharacter
F Langlands.Derivative.Mirabolic.phiPlusCharacter_eq_inv
F Langlands.Derivative.Mirabolic.phiPlusCharacter_mul_phiMinusCharacter
F Langlands.Derivative.Mirabolic.phiPlusHaarHalf._proof_1
F Langlands.Derivative.Mirabolic.phiPlusHaarHalf._proof_6
F Langlands.Derivative.Mirabolic.phiPlusNormalizedEval
F Langlands.Derivative.Mirabolic.phiPlusNormalizedEval_covariant
F Langlands.Derivative.Mirabolic.phiPlusNormalizedEval_exists_openSubgroup
F Langlands.Derivative.Mirabolic.phiPlusNormalizedEval_injective
F Langlands.Derivative.Mirabolic.phiPlusNormalizedEval_isCompact_quotientSupport
F Langlands.Derivative.Mirabolic.phiPlusNormalizedMk
F Langlands.Derivative.Mirabolic.psiMinusCharacter.eq_1
F Langlands.Derivative.Mirabolic.psiPlus
F Langlands.Derivative.Mirabolic.psiPlusCharacter
F Langlands.Derivative.Mirabolic.psiPlusCharacter._proof_1
F Langlands.Derivative.Mirabolic.psiPlusCharacter_eq_inv
F Langlands.Derivative.Mirabolic.psiPlusCharacter_mul_psiMinusCharacter
F Langlands.Derivative.Mirabolic.psiPlusHaarHalf._proof_6
```

### M073: `Langlands.Representation.Derivative.MirabolicStrongIndecomposabilityProof`

```text
F Langlands.Derivative.mirabolicStrongIndecomposabilityReduction
```

### M074: `Langlands.Representation.Derivative.MirabolicStrongIndecomposabilityStatement`

```text
F Langlands.Derivative.MirabolicStrongIndecomposabilityReduction
```

### M082: `Langlands.Representation.Induction.Definitions`

```text
F Langlands.Induction.CompactFunctions
F Langlands.Induction.EquivariantFunctions
F Langlands.Induction.EquivariantFunctions._proof_1
F Langlands.Induction.LeftQuotient
F Langlands.Induction.SmoothFunctions
F Langlands.Induction.SmoothRep
F Langlands.Induction.compactFunctionOf
F Langlands.Induction.compactFunctions
F Langlands.Induction.compactFunctions._proof_1
F Langlands.Induction.compactFunctions._proof_2
F Langlands.Induction.compactFunctions._proof_3
F Langlands.Induction.compactFunctions._proof_4
F Langlands.Induction.compactFunctions._proof_5
F Langlands.Induction.compactFunctions._proof_6
F Langlands.Induction.compactFunctions._simp_1
F Langlands.Induction.compactFunctions._simp_2
F Langlands.Induction.compactFunctionsAddCommGroup
F Langlands.Induction.compactInduced
F Langlands.Induction.compactInducedMap
F Langlands.Induction.compactInducedMap._proof_1
F Langlands.Induction.compactInducedMap._proof_2
F Langlands.Induction.compactInduced_smooth
F Langlands.Induction.compactInductionFunctor
F Langlands.Induction.compactInductionFunctor._proof_1
F Langlands.Induction.compactInductionFunctor._proof_2
F Langlands.Induction.compactInductionFunctor._proof_3
F Langlands.Induction.compactSubrepresentation
F Langlands.Induction.compactSubrepresentation._proof_1
F Langlands.Induction.equivariantAction
F Langlands.Induction.eval
F Langlands.Induction.quotientMap
F Langlands.Induction.quotientRight
F Langlands.Induction.quotientRight._proof_1
F Langlands.Induction.quotientSupport
F Langlands.Induction.smoothFunctionOf
F Langlands.Induction.smoothFunctionOf._proof_1
F Langlands.Induction.smoothFunctionsAddCommGroup
F Langlands.Induction.smoothInduced
F Langlands.Induction.smoothInducedMap
F Langlands.Induction.smoothInduced_smooth
F _private.Langlands.Representation.Induction.Definitions.0.Langlands.Induction.compact_map_mem
F _private.Langlands.Representation.Induction.Definitions.0.Langlands.Induction.continuous_quotientRight
F _private.Langlands.Representation.Induction.Definitions.0.Langlands.Induction.eval_locallyConstant
F _private.Langlands.Representation.Induction.Definitions.0.Langlands.Induction.preimage_quotientSupport
F _private.Langlands.Representation.Induction.Definitions.0.Langlands.Induction.quotientSupport_closed
```

### M083: `Langlands.Representation.Jacquet.CharacterAveraging`

```text
F Langlands.Jacquet.Localization.apply_characterAverage
F Langlands.Jacquet.Localization.apply_eq_zero_of_mem_relations
F Langlands.Jacquet.Localization.apply_orbitMean
FD Langlands.Jacquet.Localization.characterAverage
FD Langlands.Jacquet.Localization.characterAverage_eq_orbitMean
FD Langlands.Jacquet.Localization.characterAverage_eq_quotient_sum
FD Langlands.Jacquet.Localization.characterAverage_relation
FD Langlands.Jacquet.Localization.eventually_characterAverage_eq_zero
FD Langlands.Jacquet.Localization.finite_orbit_twistedRestriction
FD Langlands.Jacquet.Localization.isSmooth_twistedRestriction
FD Langlands.Jacquet.Localization.isSmooth_twistedRestriction._simp_1_1
FD Langlands.Jacquet.Localization.isSmooth_twistedRestriction._simp_1_2
FD Langlands.Jacquet.Localization.isSmooth_twistedRestriction._simp_1_3
FD Langlands.Jacquet.Localization.orbitMean_eq_quotient_sum
FD Langlands.Jacquet.Localization.orbitMean_eq_smul_sum
FD Langlands.Jacquet.Localization.sub_orbitMean_mem
FD Langlands.Jacquet.Localization.twistedRestriction
FD Langlands.Jacquet.Localization.twistedRestriction._proof_1
FD Langlands.Jacquet.Localization.twistedRestriction_apply
```

### M084: `Langlands.Representation.Jacquet.Coinvariants`

```text
F Langlands.Jacquet.relations
F Langlands.Jacquet.relations._proof_1
```

### M085: `Langlands.Representation.Jacquet.Localization`

```text
FD Langlands.Jacquet.Localization.Coinvariants
FD Langlands.Jacquet.Localization.IsInvariant
FD Langlands.Jacquet.Localization.action
FD Langlands.Jacquet.Localization.conjugate
FD Langlands.Jacquet.Localization.conjugate._proof_1
FD Langlands.Jacquet.Localization.hom_ext
FD Langlands.Jacquet.Localization.isInvariant_one
FD Langlands.Jacquet.Localization.isSmooth_action
F Langlands.Jacquet.Localization.ker_mk
FD Langlands.Jacquet.Localization.lift
FD Langlands.Jacquet.Localization.lift._proof_1
FD Langlands.Jacquet.Localization.map
FD Langlands.Jacquet.Localization.map._proof_1
FD Langlands.Jacquet.Localization.mapLinear
FD Langlands.Jacquet.Localization.mapLinear._proof_1
FD Langlands.Jacquet.Localization.map_comp
FD Langlands.Jacquet.Localization.map_id
FD Langlands.Jacquet.Localization.mk
FD Langlands.Jacquet.Localization.mk_apply_subgroup
FD Langlands.Jacquet.Localization.mk_eq_iff
F Langlands.Jacquet.Localization.mk_eq_zero
FD Langlands.Jacquet.Localization.mk_surjective
FD Langlands.Jacquet.Localization.quotientMap
FD Langlands.Jacquet.Localization.quotientMap._proof_1
FD Langlands.Jacquet.Localization.quotientMap._proof_2
FD Langlands.Jacquet.Localization.relations
FD Langlands.Jacquet.Localization.relations._proof_1
F Langlands.Jacquet.Localization.relations.eq_1
FD Langlands.Jacquet.Localization.relations_le_ker_iff
FD Langlands.Jacquet.Localization.relations_le_ker_iff._simp_1_1
FD Langlands.Jacquet.Localization.relations_le_ker_iff._simp_1_2
F Langlands.Jacquet.Localization.relations_one
FD Langlands.Jacquet.Localization.relations_stable
FD Langlands.Jacquet.Localization.smoothFunctor
FD Langlands.Jacquet.Localization.smoothFunctor._proof_1
FD Langlands.Jacquet.Localization.smoothFunctor._proof_2
FD Langlands.Jacquet.Localization.smoothObject
FD Langlands.Jacquet.Localization.smoothObject._proof_1
FD Langlands.Jacquet.Localization.sub_mem_relations
```

### M092: `Langlands.Representation.RankinSelberg.EqualRankFrobeniusProof`

```text
F Langlands.RankinSelberg.EqualRankFrobenius.exists_lastRow_eq
F Langlands.RankinSelberg.EqualRankFrobenius.isOpenMap_lastRow
F Langlands.RankinSelberg.EqualRankFrobenius.isOpen_orbitSet
F Langlands.RankinSelberg.EqualRankFrobenius.lastRow_lift
F Langlands.RankinSelberg.EqualRankFrobenius.lastRow_mem_orbitSet
F Langlands.RankinSelberg.EqualRankFrobenius.lastRow_mirabolic_mul
F Langlands.RankinSelberg.EqualRankFrobenius.lift
F Langlands.RankinSelberg.EqualRankFrobenius.mem_orbitSet
F Langlands.RankinSelberg.EqualRankFrobenius.mul_inv_mem_mirabolic_of_lastRow_eq
F Langlands.RankinSelberg.EqualRankFrobenius.orbitSet
F Langlands.RankinSelberg.EqualRankFrobenius.orbitSet.eq_1
```

### M097: `Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof`

```text
F Langlands.RankinSelberg.continuous_lastRow
F Langlands.RankinSelberg.isEmbedding_generalLinear_val
F Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val
F Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val._simp_1_1
F Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val._simp_1_2
F Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val._simp_1_3
F Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val._simp_1_4
F Langlands.RankinSelberg.lastRow_image_mem_nhds
F Langlands.RankinSelberg.lastRow_mem_image_iff
F Langlands.RankinSelberg.lastRow_ne_zero
F Langlands.RankinSelberg.mem_mirabolic_iff_lastRow
F Langlands.RankinSelberg.mem_mirabolic_iff_lastRow._simp_1_2
```

### M101: `Langlands.Representation.RankinSelberg.QuotientIntegrals`

```text
F Langlands.RankinSelberg.lastRow
F Langlands.RankinSelberg.lastRow_mul_eq_vecMul
```

### M105: `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof`

```text
FD Langlands.PadicField.TopologicalData.mem_additiveLattice_of_forall_mul_eq_one
```

### M109: `Langlands.Representation.Smooth.Definitions`

```text
FD Langlands.IsSmooth
FD Langlands.IsSmoothVector
FD Langlands.fixedVectors
```

### M110: `Langlands.Representation.Smooth.SmoothPart.BasicProof`

```text
F Langlands.isSmoothVector_zero
```

### M112: `Langlands.Representation.Smooth.SmoothPart.Definitions`

```text
F Langlands.smoothInclusion
F Langlands.smoothInclusion._proof_1
F Langlands.smoothInclusion._proof_2
F Langlands.smoothLift
F Langlands.smoothLift._proof_1
F Langlands.smoothLift._proof_2
F Langlands.smoothMap
F Langlands.smoothMap._proof_1
F Langlands.smoothPart
F Langlands.smoothSubrepresentation
F Langlands.smoothSubrepresentation._proof_1
F Langlands.smoothVectors
F Langlands.smoothVectors._proof_1
F Langlands.smoothVectors._proof_2
F Langlands.smoothVectors._proof_3
```

### M113: `Langlands.Representation.Smooth.Transfer.PullbackProof`

```text
FD Langlands.isSmoothVector_comp
FD Langlands.isSmooth_comp
```

### M115: `Langlands.Representation.Smooth.Transfer.SubquotientProof`

```text
FD Langlands.isSmoothVector_map
F Langlands.isSmoothVector_of_injective
F Langlands.isSmooth_of_injective
FD Langlands.isSmooth_of_surjective
```

### M122: `Langlands.Representation.Twist.ContinuousCharacterProof`

```text
F Langlands.complex_eq_one_of_forall_norm_pow_sub_one_lt
F Langlands.isOpen_ker_of_continuous_complex_character
```

### M124: `Langlands.Representation.Twist.Definitions`

```text
FD Langlands.twist
FD Langlands.twist._proof_1
FD Langlands.twist._proof_2
FD Langlands.twist._proof_3
FD Langlands.twistIntertwining
FD Langlands.twistIntertwining._proof_1
FD Langlands.twistIntertwining._proof_2
```

### M125: `Langlands.Representation.Twist.RealPower`

```text
FD Langlands.isOpen_ker_realPowerCharacter
FD Langlands.ker_le_realPowerCharacter_ker
FDN Langlands.positiveUnitsToComplex
FDN Langlands.realPowerCharacter
F Langlands.realPowerCharacter_neg
```

### M126: `Langlands.Representation.Twist.SmoothProof`

```text
FD Langlands.isSmoothVector_twist_iff
FD Langlands.isSmooth_twist_iff
```

### M140: `Langlands.Topology.Nonarchimedean.Subgroup`

```text
F Langlands.subgroupNonarchimedean
```
