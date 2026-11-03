# Simultaneous basis property on actual standard subgroups

This internal definition unit connects the compact-basis and contraction
predicates to the existing actual algebraic standard subgroups. Its principal
declaration is
`Langlands.BruhatTits.SpecialCompact.SimultaneousStandardBasisAt`.
It defines the required property of a supplied subgroup `K0`; it states no
universal theorem about arbitrary subgroups. The later structural statement
must apply it to the same geometric special compact stabilizer as the sibling
compact-package tasks.

The source conventions are David Renard, *Représentations des groupes réductifs
p-adiques*, 9 July 2026 edition, V.2.5 (printed107/PDF113), V.3.14
(printed113/PDF119), V.3.21–V.3.23 (printed116–117/PDF122–123), and
V.5.1–V.5.2 (printed122–123/PDF128–129), registered as
`renard-2026-representations-groupes-reductifs-padiques`. This module's
existential and conjunction packaging is internal; it supplies no proof of
these structural results.

## Actual groups and algebraic compatibility

Fix a field `F`, an actual group scheme `G` with affine structure morphism, a
commutative group scheme `S`, an algebraic homomorphism `i : S.toGrp ⟶ G`,
and a cocharacter `ν`. The existing `standardLeviPoints i ν J` and
`standardUnipotentPoints i ν J` are literal subgroups of `rationalPoints G`.
`standardOppositeUnipotentPoints i ν J` uses that same standard-unipotent
construction with `-ν` and the image of `J` under character negation. It
therefore reverses both the positive system and its simple-root index. The
interpretation as the opposite radical of the same Levi requires the usual
standard-parabolic comparison for a maximal split `i`, generic `ν`, and
`J ⊆ simpleRelativeRoots i ν`; no such comparison is proved here.

`IsCompatibleStandardSplitComponent i ν J A q` requires an actual split
subtorus `q : A.toGrp ⟶ S.toGrp` and the existence of an actual connected
reductive group scheme `M`, closed inclusion `j : M ⟶ G`, and split-component
inclusion `a : A.toGrp ⟶ M`. The inclusion `j` must represent the existing
`standardLevi i ν J` on every test scheme, not only on field-valued points.
The split component uses the published `IsSplitComponent`, meaning a maximal
central split torus. The equality `a ≫ j = q ≫ i` makes its ambient embedding
literally compatible with the fixed `S` and `i`. These are algebraic
requirements, with no compact subgroup, decomposition, contraction, or basis
conclusion hidden in them.

The property quantifies existence of these data for every standard index; it
does not merely assume that a family exists or allow its absence to make all
parabolic clauses vacuous. Constructing compatible represented Levis and
their split components remains a proof obligation, to be supplied by the
owning algebraic construction.

## Characters, sections and chambers

`componentCharacterRestriction q` is the existing `characterRestrict q`,
transported through the published identity equivalences between rational
characters and character lattices of commutative group schemes. Thus it
restricts actual algebraic characters. The set
`standardParabolicComponentCharacters i ν J q` is the image of
`simpleRelativeRoots i ν \ J` under this restriction. This is Renard's
`Delta(P_J)` from V.3.14; Renard explicitly cautions that it need not be a
simple system of a root system.

`standardComponentCA i q` maps `CocharacterUniformizer.CA F A` into
`rationalPoints G` through the actual morphism `q ≫ i`. The weak, strict
and epsilon variants map the corresponding `CocharacterUniformizer` sets
by the same morphism, using exactly the restricted character set just
defined. They therefore use the existing rational-character normalized
norm and the single chosen order-one field uniformizer, common to all
split components. The inequalities are respectively at most one, strictly
less than one, and strictly less than `ε`. The epsilon definition has no
additional weak-chamber condition. Empty character sets are retained,
including the full-Levi and rank-zero cases. No alternative valuation or
section is introduced, and `C_A` is not replaced by all of `A(F)`.

## Source map and simultaneous quantifiers

All the following declarations are in
`Langlands.BruhatTits.SpecialCompact`.

| Renard row | Encoding in `SimultaneousStandardBasisAt` |
| --- | --- |
| S20, V.5.2(i) and the introductory basis assertion | One existential `B` precedes every standard index `J`. `CompactOpenNormalBasis K0 B` includes containment in and normality under the same `K0`, compact and open ambient carriers, and the full identity-neighborhood `HasBasis` law. |
| S21, V.5.2(ii), ordered product | Every `K ∈ B` satisfies `HasIwahoriIntersectionDecomposition` for the actual `M_J(F)`, `N_J(F)` and opposite radical. Its map is actual multiplication from `(K ∩ Nbar_J) × (K ∩ M_J) × (K ∩ N_J)` to `K`; bijectivity includes the product equality and intrinsic uniqueness. |
| S21, V.5.2(ii), normalization and contraction | `StandardParabolicBasisMember` applies `ContractionAndCofinality` to these same literal intersections and the actual section/chambers. It normalizes the Levi factor, contracts the forward radical with `m`, and contracts the opposite factor with `m⁻¹`. |
| S22, V.5.2(iii) | The imported predicate gives both strict-element exhaustive unions and the positive epsilon threshold before every element of its epsilon chamber, for every compact subset of either radical. |
| S23, V.5.2(iv) | The same predicate gives both contracting-power identity-neighborhood bases and uniform cofinality for every compact open subgroup of either radical. |

The component `A` and its inclusion `q` are chosen after the standard index
and before every member of `B`. The quantifiers are therefore one `B`, then
every `J`, then compatible algebraic component data, then every `K ∈ B`.
There is no separate small-subgroup choice for a parabolic. Every topology
in the two principal properties is explicitly the canonical
`rationalPointTopology F G.X`; all Levi and radical topologies are its
induced subgroup topologies.

For each `J`, `InheritedCompactOpenNormalBasis` uses exactly the image
family `{K.comap M_J.subtype | K ∈ B}` and the ambient compact
`K0.comap M_J.subtype`. It does not choose an unrelated family inside the
Levi. Identifying the latter compact with the sibling's adapted special
compact in the standard Levi remains the shared standard-Levi comparison
obligation. This smaller normal basis is distinct from a chamber Iwahori.

## Retained construction and theorem obligations

This definition unit does not establish the existence or any property of
the geometric `K0`, actual KP apartment/building data, special points,
parahorics, or compact stabilizers. It does not assume a completed-building
typeclass or an arbitrary good-position certificate. The supplied-data
target on explicitly valid KP data must substitute the shared
`SpecialVertex.K0` once that actual interface is available. A separate
general existence target must retain construction of valid actual data
and a special point for every connected reductive group over every
nonarchimedean local field, of either characteristic. Those final targets,
and their proofs, remain outstanding here.

The current property is characteristic unrestricted and imposes no
splitness, quasi-splitness, tameness, large-residue-characteristic, or
positive-rank hypothesis on `G`. Its intended structural statements add
actual connected reductivity, maximal splitness of `i`, and genericity of
`ν`; these hypotheses do not occur as substitutes for the conclusions.
The section theorem, represented-Levi and opposite-radical comparisons,
canonical topology comparisons, and simultaneous KP filtration
construction still require proofs.

The existing
`Langlands.BruhatTits.DynamicUnipotentCompactOpenContainmentStatement`
and its S22-to-Jacquet consumer retain their separate roles. This module
reuses the focused contraction predicate, does not restate either generic
target, and makes no inference that forgetting openness proves the
actual simultaneous normal basis.
