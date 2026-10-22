# Actual absolute and abelianized upper ramification

Worker 68 authors this construction. All declarations below are in
`Langlands.Ramification.Padic`. The module imports the published
`Herbrand.Finite` and `ClassFieldTheory.Local.Galois` (formerly at
`LocalClassField.Galois`) modules unchanged. It uses Mathlib's actual
algebraic closure, finite Galois intermediate fields, automorphism groups,
restriction maps, and Krull topologies.

## Source and scope

The original is Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay
Greenberg, GTM 67, Springer (1979), Chapter IV, Section 3. The real lower
indexing and inverse Herbrand function are on printed p.73 (PDF p.80);
upper numbering and its endpoint are on printed p.74 (PDF p.81); the infinite
Galois construction is Remark 1 on printed p.75 (PDF p.82). These three pages
were read as text and independently inspected as page images. The registered
source is `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
No source-specific errata file was present in the Library notes.

Serre describes the infinite upper group by the inverse limit of the finite
Galois upper groups. Inside the actual absolute Galois group, this construction
is implemented as the intersection of all finite restriction preimages. An
absolute automorphism already has compatible finite restrictions; no new
compatibility certificate is a parameter. The construction and elementary
lemmas here require no arithmetic theorem about images under restriction.
The equality of the image with a prescribed finite upper group remains a
separate theorem obligation.

The parameter `p` is any prime, and `F : PadicField.{u} p` is any finite
extension of the actual `Padic p`. The index is an unrestricted real number.
Serre's original domain starts at -1. The finite module uses the lower group
at `ceil(u)` and upper group at `psi(v)`, where psi is the actual inverse of
its constructed Herbrand order isomorphism. Thus the convention is left
continuous: the group at a break retains the value from the left. Serre's
infinite left-continuity formula is `G^v = ⋂ (w < v), G^w`. The proof of that
formula is not part of this construction unit; it is not assumed here. The
published finite extension below -1 gives the full group, and the same
extension is proved here for the absolute filtration. No claim of absolute
eventual triviality is made.

## Concrete fields and restriction

`finiteGaloisPadicField F L` packages any actual finite Galois intermediate
field `L` in an ambient field `Ω : Type v`. The base universe `u` and ambient
universe `v` are independent. Its carrier is definitionally the existing
subtype `L`, with its inherited field and p-adic algebra instances.
Finite dimensionality is proved by the tower from `Padic p` through
`F.Carrier` to `L`. The ambient p-adic algebra and the specified base embedding
are required to form an actual scalar tower. This is a transparent algebraic
packaging helper, not a replacement field structure or an arithmetic input
record. It also permits independent-universe consumers.

`absoluteFiniteExtension F L` specializes that helper to
`L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)`.
The identical universe of this particular subtype and the chosen algebraic
closure is inherited from Mathlib, not imposed on the general helper.
Every such finite field has the published `canonicalTopologicalData`.
Its canonical upper group is the published integer-ring construction on
that realization. No silent identification with a different supplied
valuation or residue ring is used.

`absoluteFiniteRestriction F L` is the actual
`AlgEquiv.restrictNormalHom`, packaged as a continuous group homomorphism.
Continuity is Mathlib's `InfiniteGalois.restrictNormalHom_continuous`.
The target is `Gal(L/F.Carrier)` with its existing, discrete Krull topology.

## Absolute intersection and its elementary proofs

`absoluteUpperRamificationGroup F v` is the infimum over **all** the finite
Galois intermediate fields of the comaps of
`canonicalUpperRamificationGroup (absoluteFiniteExtension F L) F.Carrier v`
along `absoluteFiniteRestriction F L`. In particular, the indexing family
is not restricted to abelian extensions and is not supplied by the caller.
This declaration implements Serre IV.3, Remark 1, p.75, inside the actual
absolute Galois group.

`mem_absoluteUpperRamificationGroup_iff` is the exact universal membership
formula, proved by subgroup infimum and comap membership. The formula
`mem_absoluteUpperRamificationGroup_iff_lower` expands each finite condition
to the published integer lower group at `ceil(herbrandPsi ... v)`; it follows
by definitional equality, with canonical topological data at each field.
These are finite evaluation conditions on one absolute element.

`absoluteUpperRamificationGroup_le_comap` is the infimum bound at any finite
field. `absoluteUpperRamificationGroup_map_restriction_le` rewrites that
bound by the map/comap adjunction. It asserts image **containment**, not image
equality. These proofs use no surjectivity on ramification groups.

`absoluteUpperRamificationGroup_normal` pulls back the finite normality
instances and applies normality of an arbitrary subgroup intersection.
`absoluteUpperRamificationGroup_isClosed` rewrites the carrier as a set
intersection. Each term is closed because every subset of the finite
discrete target is closed and the restriction map is continuous.
`absoluteUpperRamificationGroup_antitone` applies finite decreasing behavior
to every restriction of an element. The theorem
`absoluteUpperRamificationGroup_neg_one` uses the finite -1 endpoint and
infimum/comap simplification. The theorem
`absoluteUpperRamificationGroup_of_le_neg_one` then uses decreasing behavior
to retain the full group at every smaller real index.

These construction proofs are elementary consequences of the source
construction and the published finite interfaces. Their Lean route is
explicitly intersection, continuity, and subgroup lattice reasoning, rather
than an invocation of the arithmetic quotient theorem on Serre p.74.

## Abelianized image

`localAbelianUpperRamificationGroup F v` is the subgroup image of the actual
absolute upper group under the published continuous
`Langlands.LocalClassField.localAbelianGaloisProjection F`. The ambient group
is the existing quotient by the **closed** commutator subgroup,
`Field.absoluteGaloisGroupAbelianization F.Carrier`. This image definition is
a derived project interface: it applies the existing quotient projection to
the source-defined subgroup, rather than being a further assertion in the
cited passage. No reciprocity map or principal-unit subgroup is involved.

`mem_localAbelianUpperRamificationGroup_iff` is the exact existence of an
absolute upper-group element with prescribed quotient image, by subgroup
map membership. Its `_iff_finite` variant expands membership of that same
witness into all finite Galois conditions. The one witness must satisfy all
conditions simultaneously. `localAbelianUpperRamificationGroup_antitone`
follows from monotonicity of subgroup image and the absolute decreasing
property. These are elementary derived lemmas, not an identification with
an intersection over finite abelian quotients.

Arithmetic finite-image equality, inertia at zero, wild inertia and right
limits, a proof of left continuity, and comparison with finite abelian
quotients are separate obligations. None is a hypothesis of a definition or
construction lemma here. The new unit was compiled with no errors or warnings;
independent semantic review and publication are separate from development
checking.
