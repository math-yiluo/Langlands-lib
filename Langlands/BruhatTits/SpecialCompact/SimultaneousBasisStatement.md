# General existence of the simultaneous standard basis

`Langlands.BruhatTits.SpecialCompact.SimultaneousStandardBasisExistenceStatement`
is a proposition target, not a theorem. It requires, for every connected
reductive group over every nonarchimedean local field, apartment data `D` and a
geometric special vertex `x` such that the actual compact stabilizer

```
D.compactStabilizer (D.apartmentMap x)
```

has the published `SimultaneousStandardBasisAt` property. The maximal split
torus `i` and generic cocharacter `ν` are fixed before these witnesses. The
same `i`, `ν`, `D` and `x` occur throughout the conclusion; in particular,
no compact subgroup is selected separately for a standard parabolic.

The provenance of the existence target is derived packaging of Renard,
*Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
V.5.1–V.5.2 (printed122–123/PDF128–129), with the geometric compact-stabilizer
convention of Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Definition 1.3.39 (printed29/PDF60) and Theorem 4.2.15
(printed173–174/PDF204–205). The mandatory 1 November 2024 corrections,
especially the correction to AS 5 (PDF33), apply to the retained building
construction. This target neither constructs nor assumes that corrected
construction as a typeclass.

## The geometric subgroup and the fixed standard system

The imported `KPApartmentData` and `KPBuilding` modules define the actual
valued-root apartment, its quotient `ReducedBuilding`, the map `apartmentMap`
and the action of `G(F)`. The subgroup in the conclusion is exactly
`G(F)^1 ∩ Stab(D.apartmentMap x)`: its first factor is the published
`Plancherel.rationalCommonNormKernel G`, and its second factor is the full
stabilizer for that action. This is the literal term used by the sibling
special-compact interface. No replacement subgroup, chosen apartment origin,
parahoric or chamber Iwahori is introduced.

Both point conditions refer to `D.affineRoots`. `IsSpecialPoint` says that
every affine-root hyperplane is parallel to one through `x`;
`IsVertex` says that the facet of `x` is the singleton `{x}`. They are
geometric conditions, with none of the basis or contraction conclusions
included as fields.

The hypotheses use the existing `IsConnectedReductive`,
`IsMaximalSplitTorus` and `IsGenericCocharacter`. The first supplies the
affine structure morphism; the second supplies the monomorphism needed for
the actual apartment data. The positive system and standard subgroups
remain those defined by `i` and `ν`, including the minimal standard
parabolic with empty simple-root index. There is no additional choice of
a minimal parabolic. No restriction on characteristic, residue
characteristic, rank, splitness, quasi-splitness or tameness of `G` is
imposed.

## Renard S20–S23 and standard-Levi compatibility

All four rows below are required by the single
`SimultaneousStandardBasisAt i ν` conjunct. Their definitions and source
conventions are in the imported paired file `StandardBasisProperty.md`.

| Source row | Requirement at this same geometric subgroup |
| --- | --- |
| S20, V.5.2(i) and the introductory assertion | One family `B` is a full identity-neighborhood basis of compact open subgroups, contained in and normal under this `K0`. This existential family precedes every standard index `J`. |
| S21, V.5.2(ii) | For every standard `J` and every `K ∈ B`, multiplication from the literal opposite-radical, Levi and radical intersections to `K` is bijective, in that order. The same component section normalizes the Levi intersection and contracts the radical intersections in the two source directions. |
| S22, V.5.2(iii) | Every strictly contracting element gives both exhaustive expanding unions. For each compact subset of either radical there is a positive epsilon threshold, chosen before every element of the corresponding epsilon chamber, giving the specified one-step expanding containment. |
| S23, V.5.2(iv) | For each strictly contracting element, the contracting powers give identity-neighborhood bases in both radicals. For every compact open subgroup of either radical, a positive epsilon threshold gives uniform one-step contracting containment. |

For each `J`, the inherited Levi basis is exactly
`{K.comap (standardLeviPoints i ν J).subtype | K ∈ B}`, with ambient
compact subgroup obtained by the same comap of this `K0`. The compatible
split component is an actual central maximal split torus of a represented
connected reductive Levi, with its inclusion factoring through the same
`S` and `i`. It is chosen after `J` and before every `K ∈ B`. Its
`C_A` and chambers are the published common-uniformizer images and
restricted actual-character inequalities; they are not freely supplied
subsets. The canonical topology and all induced subgroup topologies are
fixed inside `SimultaneousStandardBasisAt`.

## Scope and retained obligations

Construction of `D` and `x` is in the conclusion. In particular, this is
not an implication with a preexisting apartment or completed building
as a premise. Conversely, the target asserts nothing for every arbitrary
`KPApartmentData`: that published data structure contains only its stated
valued-root and split-torus compatibility laws, not all corrected KP
building axioms or topological consequences.

This focused target records the basis-existence projection at the shared
geometric formula for `K0`. It does not add separate compactness,
openness, maximal-compactness, Iwasawa, Weyl-representative, Cartan or
standard-Levi adaptedness conjuncts for `K0`. Those are sibling structural
obligations. In particular, two independently proved existential
statements do not imply that their witnesses agree. A final joint
compact-package statement must supply one `D,x` for all sibling
conclusions, or derive them uniformly from one genuinely sufficient
corrected validity predicate and its general existence theorem. That
same-witness composition and any corresponding supplied-data basis
target remain outstanding; no validity predicate is invented here.

The proof obligations also retain corrected valued-root/building
existence in full generality, existence of a special vertex, the
simultaneous small-filtration construction, the canonical topology
comparisons, actual standard-Levi and opposite-radical comparisons, the
compatible split-component construction and section theorem, and all
contraction and cofinality proofs. The exact inherited Levi compact
must still be identified with the sibling's adapted Levi compact at
the common witness.

This unit does not duplicate the generic compact-containment target or
the S22-to-Jacquet consumer. The existing
`SimultaneousBasisJacquetAdapterStatement` keeps the conditional passage
to the actual Jacquet input separate; its proof, including strict-chamber
nonemptiness, remains required. No deduction obtained by forgetting
openness establishes the present simultaneous basis target.
