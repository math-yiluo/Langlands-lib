# One geometric witness for the special compact and simultaneous basis

`Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement`
is a proposition target. It puts the special compact properties, standard-Levi
inheritance, ambient and Levi Iwasawa products, ambient and Levi Cartan comparison
and simultaneous Renard basis under one existential apartment datum `D` and one
point `x`. It also constructs an actual represented torus centralizer and its
character comparison, shared by all Cartan clauses. It supplies no proof.

This is derived packaging of the shared special-compact predicates of
Worker 1249, the geometric adapters of Worker 1229, the actual-parabolic
product predicates of Worker 1265, the actual Cartan predicates of Workers 454
and 1266, and the simultaneous basis predicates of Workers 15 and 1218.
Worker 118 supplied the common-witness requirement and the retained
corrected-building boundary.

## Quantifiers and the geometric subgroup

The target quantifies over every nonarchimedean local field `F` in an arbitrary
universe, an actual connected reductive group scheme `G`, a chosen maximal
split torus `i : S.toGrp ⟶ G`, and a generic cocharacter `ν` of `S`. The
instances required for the apartment and rational-point constructions come
from `hG.isAffineHom` and `hi.isSplitSubtorus.mono`. There is no restriction on
characteristic, residue characteristic, rank, splitness, quasi-splitness or
tameness.

The fixed `i` and `ν` determine the simple relative roots and all standard
parabolics, including the minimal one with empty index. Only then does the
target require `D : KPApartmentData i (localFieldOrder F)` and
`x : D.Apartment`. The conclusion also chooses a group scheme `Z`, a closed
inclusion `j : Z ⟶ G` representing `torusCentralizer i` on every test scheme,
and a factorization `s : S.toGrp ⟶ Z` with `s ≫ j = i`. It constructs
`h : Function.Bijective (restrictionEvaluation s)`, rather than assuming this
character comparison for a supplied centralizer. The ambient Cartan clause uses
exactly these `Z`, `j`, `s` and `h`; the Levi clauses factor this same `j`
through each standard Levi and retain `Z`, `s` and `h`. Every compact and basis
conjunct uses the same `D` and `x`. In particular,

```
K0 = D.specialCompactSubgroup x
   = D.compactStabilizer (D.apartmentMap x)
   = G(F)^1 ∩ Stab(D.apartmentMap x).
```

The first equality names the subgroup; the second unfolds the shared adapter.
The last is the imported character-kernel stabilizer formula. This is the
literal subgroup of the sibling special-compact task. Its definition does
not assert compactness. The present target requires compactness, openness
and maximality as conclusions at this particular witness.

`D.IsSpecialApartmentVertex x` is the conjunction of geometric specialness
and vertexhood for `D.affineRoots`. It contains no compact-subgroup or basis
condition. The smaller subgroups in the basis are distinct from a chamber
Iwahori; the subgroup `K0` is distinct from the full reduced fixer and is
not identified with the parahoric.

## Conjuncts at the common witness

| Conjunct | Exact requirement |
| --- | --- |
| `SpecialCompactProperties F i ν K0` | `K0` is algebraically bounded, open and maximal among bounded subgroups; compact, open and maximal among compact subgroups; has representatives of the actual relative Weyl group; and satisfies `K0 ∩ P_J = (K0 ∩ M_J)(K0 ∩ N_J)` for every standard `J`. |
| `SpecialLeviInheritance F hi ν D x` | Each actual represented standard Levi has an apartment point obtained by restriction of `x`, special and a vertex, whose compact stabilizer has those special compact properties and equals the preimage of this same `K0`. |
| `Iwasawa.ParabolicPointProductFamily i ν K0` | Both literal products cover `G(F)` for every actual algebraic, dynamic and standard parabolic, including all rational conjugates, with this same `K0`. |
| `RenardCartan.SpecialCompactRenardComparison D x ν j s h` | Every `K0` double coset has an actual dominant centralizer representative; two such representatives have the same double coset exactly when their quotient lies in `Z(F)^1`; and the existing actual centralizer lattice conclusions hold for this `i`, `ν`, `s` and `h`. |
| Levi `Iwasawa.ParabolicPointProductFamily` | For every standard `J`, both product orders cover the actual `M_J(F)` for all its algebraic, dynamic and standard parabolics and their rational conjugates, using `Standard.leviTorusHom i ν J`, the same `ν` and exactly `D.specialCompactLeviSubgroup ν J x`. |
| `RenardCartan.SpecialCompactStandardLeviCompatibility D x ν s h j` | For every standard `J`, this same `Z` represents the torus centralizer in `M_J` through a closed `jM` with `jM ≫ leviHom = j` and `s ≫ jM = iM`. Levi positive roots are ambient positive roots, and Cartan coverage, classification and lattice conclusions hold for the literal preimage compact. |
| `SimultaneousStandardBasisAt i ν K0` | One compact-open normal identity-neighborhood basis works simultaneously for all actual standard parabolics, with all four Renard basis clauses. |

The compact and bounded forms are imposed separately. The target does not
use their comparison as an assumption. The ambient and Levi Iwasawa conjuncts
reuse the published family predicate; they define no new product notion.

The Cartan conjunct reuses the sibling predicate for this literal geometric
subgroup. Its two geometric requirements are coverage and classification of the
actual induced relation, with quotient orientation `z' * z⁻¹ ∈ Z(F)^1`.
Together they give a bijection from the dominant chamber in the actual valuation
image to the double cosets of this same `K0`. They do not identify that image
with the full cocharacter lattice or replace `K0` by a parahoric.

The imported lattice conclusions retain actual common-uniformizer representatives,
finite full transversals, dominant valuation sections and finite positive product
covers. A cover may repeat valuation classes. The stronger rectangular section
and nonrepeating product conclusions are conditional on the existing
chamber-compatible-transversal property. This reuses the corrected sibling
interface for Renard V.3.23 and V.5.1(4); it does not infer that stronger condition
for an arbitrary finite transversal. The reason for including this ambient
Cartan clause in the basis target is Renard V.5.2's use of the `K0` fixed in V.5.1.

The four basis clauses map to the source ledger as follows.

| Renard row | Imported requirement |
| --- | --- |
| S20, V.5.2(i) and the introductory basis assertion | One existential family `B`, before every standard `J`, is a full identity-neighborhood basis of compact open subgroups contained in and normal under this `K0`. |
| S21, V.5.2(ii) | For every `J` and every `K ∈ B`, actual multiplication from `(K ∩ Nbar_J) × (K ∩ M_J) × (K ∩ N_J)` to `K` is bijective. `C_A` normalizes the Levi intersection; its weak positive chamber contracts the forward radical intersection, and inverse elements contract the opposite intersection. |
| S22, V.5.2(iii) | Every strict-chamber element gives the two exhaustive expanding unions, with forward powers `m⁻ⁿ (K ∩ N_J) mⁿ` and opposite powers `mⁿ (K ∩ Nbar_J) m⁻ⁿ`. Each compact subset has a positive epsilon threshold before every element of the epsilon chamber, giving the one-step expanding containment. |
| S23, V.5.2(iv) | Contracting forward powers and inverse opposite powers give identity-neighborhood bases. Each compact open subgroup has a positive epsilon threshold giving uniform one-step contracting containment. |

The same compatible actual split component `A → S` is chosen for a fixed `J`
before every `K ∈ B`. Its `C_A` is the common-uniformizer cocharacter image.
Its weak, strict and epsilon chambers are defined by the restricted actual
characters in `standardParabolicComponentCharacters`. The epsilon chamber
uses norm strictly below epsilon without an additional norm-at-most-one
restriction. The topology in the compact and basis predicates is the named
canonical `rationalPointTopology F G.X`, with induced subgroup topologies.

## Standard-Levi compatibility

The basis inherited in `standardLeviPoints i ν J` is exactly the family of
preimages `K.comap (standardLeviPoints i ν J).subtype` for `K ∈ B`. Its
ambient compact subgroup is the same preimage of `K0`. No new family or
compact subgroup is chosen independently in that carrier.

For the represented Levi `M_J = Standard.leviScheme i ν J`, the inherited
geometric compact in `SpecialLeviInheritance` is exactly
`D.specialCompactLeviSubgroup ν J x`. This is the preimage under
`rationalPoints.map (Standard.leviHom i ν J)`. The shared adapter
`D.specialCompactLeviSubgroup_map` identifies its image with
`K0 ⊓ standardLeviPoints i ν J`. Thus both clauses specify the literal
intersection with the same `K0`. The algebraic equivalence
`Standard.leviPointsEquiv i ν J` connects these two carriers; the required
topological comparison and transport of the inherited basis remain proof
obligations. The target adds no unrelated choice of a Levi compact.

The Levi Iwasawa clause uses this preimage directly. Its affine-group
instance comes from the closed standard Levi inclusion. In conjunction with
`SpecialLeviInheritance`, it supplies property (1) of Renard V.5.1 for the
same subgroup that the inherited apartment point defines. The inherited
torus and `ν` determine its minimal parabolic.

For property (4), `SpecialCompactStandardLeviCompatibility` constructs, for
each `J`, a closed centralizer inclusion `jM` into the actual represented
Levi. The identities `jM ≫ Standard.leviHom i ν J = j` and
`s ≫ jM = Standard.leviTorusHom i ν J` align these centralizers with the
ambient witnesses. The common group `Z`, character comparison `s,h`,
uniformizer subgroup `C0 S s`, valuation image lattice and norm kernel
`Z(F)^1` remain identical. Each Levi chamber uses its own actual positive
roots, required to be ambient positive roots. The Cartan classification
has the same orientation `z' * z⁻¹ ∈ Z(F)^1` and concerns double cosets of
exactly `D.specialCompactLeviSubgroup ν J x`.

The imported conditional equivalences then identify the norm quotient,
the chamber in the actual valuation image, and any actual dominant
valuation section with those double cosets. The Levi lattice conclusion
has the same finite-cover and chamber-compatible-transversal boundary as
the ambient one. No simultaneous rectangular transversal for all Levis is
required. These clauses supply no inherited apartment; that remains the
separate `SpecialLeviInheritance` conjunct. Together the clauses require
all four compact-package properties for the literal intersection, as in
Renard V.5.1(5).

## Sources and provenance

The source tuples are:

- Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026
  edition, `renard-2026-representations-groupes-reductifs-padiques`,
  SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:
  V.5.1–V.5.2, printed122–123/PDF128–129. V.5.2 fixes the same minimal
  parabolic, torus and compact as V.5.1 before selecting its one basis.
  The section and chamber conventions are V.2.5, V.3.14 and V.3.21–V.3.23.
  V.3.23, printed117/PDF123, distinguishes the dominant intersection of a
  finite-transversal section from the additional rectangular choice.
- Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`,
  SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
  Definition 1.3.39, printed29/PDF60; Theorem 4.2.15(1),
  printed173–174/PDF204–205; §6.7, printed233–234/PDF264–265.
  Theorem 5.2.1, printed186–188/PDF217–219, motivates the separate parahoric
  comparison; it is not used to identify that subgroup with the present `K0`.
- Kaletha–Prasad, *Corrections and additions*, 1 November 2024,
  `kaletha-prasad-2024-corrections`,
  SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`:
  the corrected building axioms on PDF27–29 and the additional Chapter 7
  AS 5 prerequisite on PDF33 remain part of the construction obligations.

The packaging is derived: it conjoins existing actual-group conclusion
predicates at one geometric witness. Separate existential targets for the
basis and compact properties would not imply this conjunction. This
declaration explicitly requires the common witnesses rather than making
that inference.

## Retained obligations and published dependencies

This target remains existential in `D` and `x`. It asserts no structural
result for arbitrary weak `KPApartmentData`. That data type does not contain
all corrected building axioms. The proposed same-data validity interface is
also partial; it is not used as a sufficient hypothesis here. General
corrected-building existence and any structural basis target on genuinely
sufficient valid supplied data remain separate obligations.

The target includes ambient and Levi Iwasawa and Cartan conclusions at the
same witnesses. It is a strengthening of the existing basis-existence
projection. It does not assert corrected validity or discharge the sibling
construction and proof obligations.

Proofs still must construct the corrected geometric witnesses and their
special vertices, establish all compact and maximality properties, build
one simultaneous filtration basis, construct the compatible split
components and uniformizer sections, construct the represented centralizer,
prove the restriction-evaluation comparison, compare canonical topologies and
actual opposite radicals, and prove every decomposition, lattice comparison,
ambient and Levi Cartan coverage and classification, root containment,
centralizer factorization, contraction, exhaustion and cofinality clause.
The generic compact-containment statement
and `SimultaneousBasisJacquetAdapterStatement` are reused for their own
roles; neither proves this existence target.

The geometric `SpecialCompact` and `SpecialCompactLevi` adapters, the general
`SimultaneousBasisStatement` projection, `SpecialCompact.Properties`,
`RenardSpecialCompactComparison`, its `SpecialCompactDominantQuotient`
dependency, and `RenardSameCompactLeviComparison` are published. This target
imports their Lean names and does not resubmit their definitions. Development
checks using private copies establish only syntax and interface compatibility.
The submission was also freshly compiled and inspected against the published
imports in the refreshed workspace; this verifies elaboration and the
proposition-valued target, without proving the target.
