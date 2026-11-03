# Natural opposite-Jacquet duality on the actual rational-point group

Author: Worker 196. Worker 490 contributed the orientation needed by the
downstream induction/Jacquet term comparison.

`Langlands.Aubert.General.RationalPointFamily.RationalNaturalJacquetDualityStatement`
is a proposition definition awaiting proof. It requires a coherent family of
opposite-Jacquet duality isomorphisms on admissible smooth objects. It proves
neither those isomorphisms nor rational-point Aubert commutation.

## Actual subgroups, topology and normalization

The field `k : Type u` ranges over all nonarchimedean local fields, including
positive characteristic. The group scheme `G` is connected reductive, without
a splitness or quasisplitness restriction. The actual maximal split torus map
`i`, generic cocharacter `ν` and arbitrary finite subset `I` of
`SimpleRoot i ν` specify the published standard parabolic, Levi and unipotent
subgroup. The label type and the finite subset may be empty.

The rational-point group carries the canonical `pointTopology`. Local
compactness, nonarchimedeanness and Hausdorffness refer to that topology.
Closedness of the standard unipotent subgroup is displayed explicitly.
`StandardCocharacterStatement`, together with the displayed geometric
hypotheses, supplies the standard semidirect decomposition through
`isSemidirectDecomposition_of_standardCocharacterStatement`.

The variable `ζ` is any actual cocharacter satisfying
`IsStandardCocharacter i ν (rootSet i ν I) ζ`. Its inverse is precomposition
with inversion on the multiplicative group. `oppositeParabolic i ζ` and
`oppositeUnipotent i ζ` are the identity-test values of its dynamic parabolic
and contraction subgroup functors. The construction
`opposite_isSemidirectDecomposition` derives the opposite decomposition with
the literal standard subgroup `levi i ν I`, using equality of centralizers on
every test scheme. Thus both Jacquet functors land in the same actual Levi
category. No equivalence between different Levi models is inserted.

`isClosed_oppositeUnipotent_localField` derives closedness of the actual
opposite contraction subgroup in `pointTopology`. It uses the published
closed represented-subgroup topology and dynamic affine representability;
the local-field interface supplies Hausdorffness of the coefficient field.
The statement assumes neither this closedness nor an opposite decomposition.
It asks for a family for each standard-cocharacter witness separately and
contains no comparison between different choices of `ζ`.

Write `rP` and `rO` for `General.jacquetFunctor` on these standard and opposite
decompositions. Each takes actual unipotent coinvariants with the descended
Levi action and twists by `HaarModulus.closedInverseHalfCharacter` for its own
closed radical. Hence the action is
`m · [v] = δ(m)^(-1/2) [m v]`, where `δ` is the positive Haar scaling character
of forward conjugation on that radical. The half power is the positive real
square root embedded in complex units. The statement uses both actual
normalizations; it supplies no compatibility identity between their moduli
as a premise.

An input `A` is a bundled smooth complex representation of the ambient
rational-point group with `A.IsAdmissible`: its fixed spaces for every open
subgroup are finite-dimensional. No finite-length or finite-dimensional
whole-carrier condition is substituted. All representation carriers have
universe `max (u + 1) v` with independent parameters `u` and `v`. There is no
topology on those carriers.

## Coherent contravariant naturality

For each fixed set of field, group, torus, root and cocharacter data, one
family is chosen simultaneously on all admissible ambient objects:

`E_A : rP(A∨) ≅ (rO(A))∨`.

Here the dual is the published `SmoothRep.contragredient`, the smooth part of
the complex-linear algebraic dual with inverse-transpose action. For every
actual morphism `f : A ⟶ B` between admissible objects, the required equation
of bundled morphisms is

`rP(f∨) ≫ E_A.hom = E_B.hom ≫ (rO(f))∨`.

Both sides map `rP(B∨)` to `(rO(A))∨`. The Jacquet maps are the published maps
on actual coinvariant classes, `[v] ↦ [f v]`, and
`contragredientHom` pulls smooth functionals back along the given map.
Objectwise isomorphisms with no naturality argument do not prove this target.

## Original source and derived formulation

The registered original source is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, revision April 29, 2019,
source `casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The retained original is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
The original text and rendered pages 4–5 and 7–8 were read, including the
overbars distinguishing the opposite radical. No separate errata file for
this source was found in the inspected public notes or source folder.

Page 4 defines the negative-half normalized Jacquet action. Section 4 on
page 5 fixes opposite parabolics with common Levi and discusses adapted
compact opens and contraction. Page 7, Proposition III.5.5, constructs
canonical stable-image lifts; III.5.6 gives admissibility of Jacquet modules;
III.5.7 gives compatibility of canonical lifts with averaging when compact
opens shrink. The source explicitly restricts the stable-image argument to
field coefficients after warning that an earlier arbitrary-Noetherian
argument was incorrect. Here the coefficient field is `ℂ`.

III.6.2 on page 7 pairs `V_N` with `(V∨)_{Nbar}`.
III.6.3 on page 8 identifies `(V∨)_{Nbar}` with the contragredient
of `V_N` as representations of the common Levi. Applying that result with
the opposite parabolic as the initial parabolic gives exactly the orientation
`rP(A∨) ≅ (rO(A))∨` used here.

The rational-point/topology packaging and coherent naturality square are
derived formulations, not additional verbatim source theorems. Their
provenance is the canonical-lift construction: an actual intertwiner
commutes with averaging and contracting Hecke operators, so it preserves the
uniquely characterized canonical stable-image lifts. Evaluation satisfies
`(f∨(ell))(v) = ell(f(v))`. Independence of the adapted compact open then
gives the displayed square for the canonical pairing. This explains the
intended assertion; no Lean proof of these compatibility facts or of the
duality map is supplied in this statement module.

## Proof and consumer obligations

A proof must construct the actual canonical pairing or another comparison,
establish nondegeneracy and smooth surjectivity, compare the actual opposite
Haar normalizations, and prove the coherent naturality equation. The target
does not assume stable-pairing data, a duality equivalence, a compact-limit
condition or those normalization identities. The conditional module
`Langlands.Representation.Jacquet.StablePairingProof` may provide a route once
its inputs have actual proofs; it is not already this specialization.
The existing general-linear natural Jacquet-duality statement has analogous
orientation but does not prove this general reductive target.

Using the admissible-input family on every finite-length ambient object
still requires the separately owned ambient finite-length admissibility
proof. This proposition adds no premise to
`RationalContragredientCommutationStatement`. It proves no finite-length
preservation, same-parabolic induction duality, associated-Levi transport,
independence of a parabolic in a Grothendieck class, root-opposition
realization or final exact-Grothendieck-group commutation. In particular,
the opposite subgroup construction alone supplies none of those
representation-theoretic comparisons.
