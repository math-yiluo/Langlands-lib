# Actual finite inertia restrictions and Weil representation presentations

Worker 104 authors this derived construction unit. All declarations are in
`Langlands.Ramification.Padic`, including the two presentation namespaces.
The field universe `u` and the representation-carrier universe `v` are
independent. The prime `p` and `F : PadicField.{u} p` are unrestricted.

## Sources and scope

Jean-Pierre Serre, *Local Fields* (Greenberg translation, 1979), Chapter IV,
section 1, printed pages 61–62 (PDF pages 68–69), defines the actual
ramification groups by their action on the integer ring modulo powers of its
maximal ideal. The zeroth group is the residue-action kernel, namely inertia.
Section 3, printed pages 73–75 (PDF pages 80–82), describes upper numbering,
its quotient compatibility and the inverse limit over finite Galois
subextensions. These passages were read directly in the registered original:
`serre-1979-local-fields`,
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Pierre Deligne and Guy Henniart, *Sur la variation, par torsion, des constantes
locales d'équations fonctionnelles de fonctions L* (1981), section 0.5,
printed page 92 (PDF page 4), uses continuous finite-dimensional complex
representations and states that inertia acts through a finite group. This
page was read directly in the registered original:
`deligne-henniart-1981-variation`,
`/home/taskhub/central-library/Deligne-Henniart--Sur la variation, par torsion, des constantes locales d'equations fonctionnelles de fonctions L--1981.pdf`,
SHA256 `54fe3348af12263a8d3774a0353fff352cb041728f446fb0cccc4b0f97803a3e`.
No source-specific errata file was present in the workspace's published notes.

The restriction maps and presentation records below are internal constructions
from these actual field and representation objects. They are not quotations
of a presentation definition in the sources. This unit constructs maps and
proves their well-definedness and elementary composition, kernel and descent
properties. It does not prove inertia-restriction surjectivity, existence of
presentations for continuous representations, independence or integrality of
conductor sums, or comparisons of ramification breaks or indices. In
particular, Serre's upper-numbering quotient theorem is not assumed here.
No local constants or Deligne–Henniart stability result is constructed or used.

## Actual fields, integer rings and restriction

For `L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)`,
the published `absoluteFiniteExtension F L` has exactly the carrier `L` and
its inherited algebra embeddings. Its topology is
`(absoluteFiniteExtension F L).canonicalTopologicalData`.
`finiteBaseEmbedding F L` is the existing scalar-tower embedding from `F`
over `Padic p`. No replacement field or valuation certificate is input data.
The subtype's universe agrees with Mathlib's chosen algebraic closure;
representation carriers remain in the independent universe `v`. The published
`finiteGaloisPadicField` helper retains its independent ambient universe.

`finiteClosureIntegerMap F L` embeds this finite canonical integer ring into
`F.closureIntegers F.canonicalTopologicalData` by the actual inclusion into the
algebraic closure. Its construction uses the published
`Weil.Local.extensionIntegers_isIntegral`: a finite integer is integral over
the base integer ring, so `LocalGalois.closureIntegers_integral` places its
image in the closure integer ring. The coercion formula
`finiteClosureIntegerMap_coe` is definitional. The instance
`finiteClosureIntegerMap_isLocalHom` proves localness: the closure integer
ring is integral over the base integer ring, hence over the embedded finite
integer ring, and the embedding is injective. Mathlib's theorem that an
injective integral ring map reflects units applies. Thus the induced residue
map exists and, as a field homomorphism, is injective.

`absoluteFiniteRestriction_mem_inertia` proves that an actual absolute inertia
element restricts into `Ramification.Padic.inertia` for the finite extension.
After lifting a residue class to an integer, apply the injective residue map
just constructed. The equality upstairs is exactly the absolute inertia
kernel condition; the actions commute because `AlgEquiv.restrictNormal`
commutes with the actual field inclusion. No map-membership certificate is
supplied by a caller.

`absoluteInertiaRestriction F L` is the resulting continuous homomorphism.
Its underlying map is the published `absoluteFiniteRestriction`, namely
`AlgEquiv.restrictNormalHom`, restricted on source and target. Continuity is
inherited from that map by composition with the source subtype and restriction
to the target subtype. `absoluteInertiaRestriction_coe` identifies the
underlying finite Galois element; `absoluteInertiaRestriction_apply` states
that evaluating at `x : L` and including in the closure gives the original
absolute automorphism evaluated at the same `x`.

`weilInertiaProjection F` restricts the actual `localProjection F` to
`localInertia F` and absolute inertia. It reuses the forward continuous
homomorphism of the published `Weil.Local.localInertiaEquiv F` from
`Weil.Local.AssemblyProof`; the underlying map is still the actual projection.
`weilInertiaProjection_coe` is its exact projection formula.
`weilInertiaRestriction F L` composes this with
`absoluteInertiaRestriction F L`; it is a continuous homomorphism on the
actual subgroup topologies. Its `_coe` and `_apply` lemmas state the exact
underlying restriction and elementwise evaluation formulas. In particular,
this is a specified arithmetic map, not an arbitrary quotient homomorphism.

## Nested finite fields

For an actual inclusion `h : L ≤ M`, `finiteGaloisRestriction F h` is
`AlgEquiv.restrictNormalHom` for the algebra structure induced by
`IntermediateField.inclusion h`. The finite Galois groups have their existing
discrete Krull topologies, so this map is continuous.
`finiteGaloisRestriction_apply` gives its evaluation after inclusion into the
same algebraic closure.

`finiteGaloisRestriction_mem_inertia` again uses residue injectivity, now for
the published `extensionResidueMap` of the actual finite-field inclusion.
It proves membership without an arithmetic hypothesis. This constructs
`finiteInertiaRestriction F h`, whose `_coe` lemma identifies the underlying
finite Galois restriction. `finiteInertiaRestriction_absolute` and
`finiteInertiaRestriction_weil` prove the composition square with the
absolute and Weil restriction maps, respectively. Both are equalities of
actual finite inertia elements. Their proof compares evaluations on each
field element and uses the restriction evaluation formulas.

`weilInertiaRestriction_ker_le` follows from that square: the kernel for the
larger field is contained in the kernel for the smaller field.

## Presentations, descent and common refinements

For `A : FiniteRepresentation.{0,u,v} ℂ (localWeilGroup F)`,
`localInertiaRepresentation F A` is the actual action restricted to
`localInertia F`, on the original finite-dimensional carrier `A`.

`FiniteInertiaPresentation F A` has exactly two fields: an actual finite
Galois subextension `extension`, and `kernel_le`, asserting that the kernel
of `weilInertiaRestriction F extension` is contained in the kernel of that
restricted representation. This data makes sense for any genuine algebraic
finite-dimensional complex representation. Continuity is not needed to
construct or use a given presentation; it belongs to the separate existence
statement for the continuous objects of Deligne–Henniart section 0.5.
Neither universal existence nor surjectivity nor any conductor law is a
field of this record.

For a presentation `P`, `P.representation hsurj` reuses the published
`descendInertiaRepresentation` with this specific restriction map and
`P.kernel_le`. The hypothesis `hsurj` explicitly asserts surjectivity of
`weilInertiaRestriction F P.extension`. The theorem `P.representation_apply`
identifies its value on the image of any Weil inertia element with the original
action. `P.artinConductor hsurj` and `P.swanConductor hsurj` directly reuse
`artinConductorOfQuotient` and `swanConductorOfQuotient` on the same data.
These are expressions at this chosen presentation, without an independence
claim.

`P.refine M h` constructs a presentation at a containing actual finite field
using the proved kernel containment. `P.pullback hsurj M h` is the genuine
representation obtained by precomposing `P.representation hsurj` with
`finiteInertiaRestriction F h`. Its evaluation lemma follows from the
composition square. `P.representation_refine` identifies it with descent at
`M` when surjectivity at `M` is also supplied, by lifting each finite inertia
element to Weil inertia and using the evaluation formulas.

`FiniteInertiaCommonRefinement F A P Q` consists only of an actual finite
Galois field and its two actual inclusions of the fields of `P` and `Q`.
`FiniteInertiaCommonRefinement.compositum F A P Q` constructs such data using
Mathlib's finite Galois compositum `P.extension ⊔ Q.extension`.
The functions `R.leftRepresentation` and `R.rightRepresentation` are the
actual pullbacks of the two descended actions. Their evaluation lemmas give
the original action on every image of Weil inertia. `R.representations_eq`
proves equality of these pullbacks if surjectivity at the common field is
supplied separately. No equality is stored as common-refinement data, and
this equality of actions does not assert equality of conductor sums.

## Remaining statement obligations

The precise missing surjectivity assertion is, for every prime, every actual
`F`, and every actual finite Galois subextension `L`,
`Function.Surjective (weilInertiaRestriction F L)`.
The corresponding assertion for `absoluteInertiaRestriction F L` is also
not proved here. The precise presentation-existence assertion is, with
independent field and carrier universes, for every `A` as above,
`A.IsContinuous → Nonempty (FiniteInertiaPresentation F A)`.
It must not be replaced by an assertion assuming presentations already exist
for all representations. Conductor independence, integrality, and
ramification-break comparisons remain separate arithmetic obligations.

## Published dependencies

The module imports `Ramification.Herbrand.Absolute` (Worker 68's actual field
packaging and restriction), `Ramification.Descent` (Worker 20's descent and
conductor interfaces), `Weil.Local.AssemblyProof` (the published local inertia
equivalence), `Weil.Local.ExtensionWeil` (Worker 53's assembly,
integer/residue maps and integrality, using Worker 9's absolute Galois layer),
and `Weil.Representation.Predicates` (Worker 17's actual finite-dimensional
representations and separate continuity predicate). All are reused by their
published Lean names; no unpublished draft is imported or copied. The pinned
environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
