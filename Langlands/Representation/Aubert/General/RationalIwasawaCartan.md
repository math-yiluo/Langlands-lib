# Iwasawa and Cartan decompositions of the actual standard family

Implementation and documentation: Worker 785 (task
`7d46c4f8-9da1-4872-9784-df53d7c630cf`, Jacquet–Cartan data on general
reductive rational points). This module supplies the Iwasawa field and the
Cartan fields of the planned standard parabolic system on `G(F)`. The other
pieces are the standard-family facts of
[StandardFamilyStructure](StandardFamilyStructure.md) and Worker 1380's assembly,
lattice model and wall contraction, which are drafted separately. The datum
itself, wall contraction and the final target are not treated here.

The geometric results are **conditional**. They take as explicit hypotheses
some of the conjuncts of the conclusion of the published, unproved Prop target
`Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement`
(`Langlands/BruhatTits/SpecialCompact/JointBasisStatement.lean`): the special
compact properties of `K₀ = D.specialCompactSubgroup x`, the actual parabolic
product family for `K₀`, and `SpecialCompactStandardLeviCompatibility`. Nothing
here proves those conjuncts. The general coset-cover facts and the countability
lemmas need no such hypothesis.

## Compact coset covers

Namespace `Langlands.Induction`. `G` is a group with a topology.

* `HasCompactCosetCover P` (definition), for `P : Subgroup G`: there is a
  compact set `K ⊆ G` such that every `g : G` is `p * k` with `p ∈ P` and
  `k ∈ K`. That is, `G = P K` with `K` compact. This is word for word the shape
  of the `iwasawa` field of the planned standard parabolic system for
  `P = P_∅`. It is Lean packaging, not a numbered source definition.
* `compactSpace_of_hasCompactCosetCover`: a compact coset cover makes the
  published `LeftQuotient P = P \ G` (from
  [Group/LeftQuotient](../../../Group/LeftQuotient.md)) a compact space. Proof:
  the projection maps `K` onto `P \ G`, because `g = p k` puts `g` and `k` in
  one right coset `P g`. The image of a compact set under the continuous
  projection is compact.
* `hasCompactCosetCover_of_compactSpace`, for a topological group that is
  weakly locally compact: if `P \ G` is compact then `G = P K` for a compact
  `K`. Proof: take a compact neighbourhood `V` of `1`. The projection is an
  open map, so the images of the translates `i · interior V` form an open cover
  of `P \ G`. A finite subcover over `t` gives the compact set
  `K = ⋃_{i ∈ t} i V`. For `g`, the coset of `g` meets some `i · interior V`
  at `i k`, so `g (i k)⁻¹ ∈ P` and `g = (g (i k)⁻¹) (i k)`.
* `hasCompactCosetCover_iff_compactSpace`: the two directions together, for a
  weakly locally compact topological group.

These two directions are the standard equivalence between `G = P K` with `K`
compact and compactness of `P \ G`. Renard, *Représentations des groupes
réductifs p-adiques* (2026 version), Théorème V.5.1 (1) (printed p. 122,
PDF p. 128) gives `G = K₀ P_∅ = P_∅ K₀`, and the Corollary on printed p. 123
(PDF p. 129) deduces that `G/P` is compact. The Lean lemmas only prove the
abstract equivalence. They are not used for the decompositions below.

## Setting for the rational points

Namespace `Langlands.Aubert.General.RationalPointFamily`. The topology on
`RationalPoint k G.X` is the published `rationalPointTopology k G.X`, with
`IsAffine G.X.left` obtained from `[IsAffineHom G.X.hom]`. Both are bound by
`haveI`/`letI` inside the statements, as in the published
`SpecialCompactProperties`. The standard family
`parabolic/levi i ν I` for `I : Finset (SimpleRoot i ν)` is the published one
of [RationalPointFamily](RationalPointFamily.md).

* `rationalPoints_map_comp_apply f g y`: the published
  `rationalPoints.map` is functorial,
  `map (f ≫ g) y = map g (map f y)`. Proof: `rationalPoints.map_apply`, Mathlib's
  `Grp.comp_hom_hom` and associativity. (Closing this goal by `rfl` for the
  standard Levi inclusion runs into a kernel deterministic timeout, so the
  lemma is stated for arbitrary morphisms.)

## Iwasawa decomposition `G = P_∅ K₀`

`k` is a field with a topology, `T` a commutative group scheme and `G` a group
scheme over `Spec k`, `i : T.toGrp ⟶ G`, `ν : cocharacterLattice T`.

* `hasCompactCosetCover_parabolic_empty_of_products i ν hK hP`: if `K` is a
  compact subgroup of `G(k)` and
  `hP : Langlands.BruhatTits.Iwasawa.StandardParabolicProducts i ν K`, then
  `HasCompactCosetCover (parabolic i ν ∅)`. Proof: the first product equality
  of `hP` at the empty root set says `G(k) = P_∅ K` as sets. Write
  `g = p c` with `p ∈ standardParabolicPoints i ν ∅` and `c ∈ K`. The published
  `parabolic` at `∅` unfolds, by `rootSet_empty`, to those standard parabolic
  points.
* `hasCompactCosetCover_parabolic_empty_of_specialCompactProperties i ν hK hP`,
  with `[ValuativeRel k]`: the same conclusion from
  `hK : SpecialCompactProperties k i ν K` and
  `hP : Langlands.BruhatTits.Iwasawa.ParabolicPointProductFamily i ν K`.
  Compactness of `K` is the first conjunct of `IsCompactOpenMaximal` inside
  `hK`, and `StandardParabolicProducts` is the third conjunct of `hP`. These
  are conjuncts of the conclusion of `JointSpecialCompactBasisExistenceStatement`
  for `K = D.specialCompactSubgroup x`. This is the Lean form of Renard,
  Théorème V.5.1 (1), `G = P_∅ K₀`, with `K₀` compact.

## Cartan decomposition of the standard Levi subgroups

`F` is a nonarchimedean local field (`[Field F] [ValuativeRel F]
[TopologicalSpace F] [IsNonarchimedeanLocalField F]`). `S` is a commutative
group scheme and `G`, `Z` are group schemes over `Spec F`.
`i : S.toGrp ⟶ G` has `[Mono i.hom.hom.left]` and `G` has
`[IsAffineHom G.X.hom]`. `D : KPApartmentData i (localFieldOrder F)`,
`x : D.Apartment`, `ν : cocharacterLattice S`, `j : Z ⟶ G`, `s : S.toGrp ⟶ Z`
and `h : Function.Bijective (restrictionEvaluation s)`. In the intended use,
`Z` is the centralizer of the maximal split torus, represented by `j`, and
`(D, x, Z, j, s, h)` are the witnesses of `JointSpecialCompactBasisExistenceStatement`.
A local instance supplies `IsAffineHom` for every standard Levi scheme
`Standard.leviScheme i ν J` from the published
`Standard.isClosedSubgroup_leviHom`.

For `I : Finset (SimpleRoot i ν)` write `M_I = levi i ν I`,
`K_I = K₀ ⊓ M_I` with `K₀ = D.specialCompactSubgroup x`, and

`Λ_I = rationalPoints.map j '' tildeC0Plus s F0 (dominantCentralizer (Standard.leviTorusHom i ν (rootSet i ν I)) ν s h)`.

Here `tildeC0Plus s F0 dom = (C0 S s * F0) ∩ dom` is the published dominant
part of Renard's representative set `C₀ F₀` (V.3.23), with `C0 S s` the image of
the uniformizer section of the cocharacter lattice. `dominantCentralizer` is
the published dominant chamber of `Z(F)` for the positive roots of the torus in
`M_I`. `F0` is a finite lattice transversal (`IsFiniteLatticeTransversal s F0`).

* `isCompact_inf_levi ν hK I`: if `K` is compact then `K ⊓ M_I` is compact.
  Proof: `M_I` is closed by the published
  `isClosed_levi_of_isNonarchimedeanLocalField`
  ([StandardFamilyStructure](StandardFamilyStructure.md)), and a compact set
  meets a closed set in a compact set.
* `countable_cocharacterLattice hT`: the cocharacter lattice of a split torus
  is countable. Proof: an isomorphism of `T` with a published split torus
  `splitTorus … I` (with `I` finite) identifies the lattice, through
  `cocharacterLattice.congr` and `splitTorus.cocharacterLatticeEquiv`, with
  `I → ℤ`, which is countable because `I` is finite.
* `countable_tildeC0Plus hS hF0 dom` and `countable_image_tildeC0Plus`: for a
  split torus `S` and finite `F0`, `tildeC0Plus s F0 dom` and its image under
  `rationalPoints.map j` are countable. Proof: `C0 S s` is the range of a map
  from the countable lattice, and `C0 S s * F0` is the image of a product of a
  countable and a finite set.
* `map_mem_levi hcompat I a` and `image_tildeC0Plus_subset_levi`: from
  `hcompat : SpecialCompactStandardLeviCompatibility D x ν s h j`, the image
  `rationalPoints.map j a` of every point of `Z(F)` lies in `M_I`. Hence
  `Λ_I ⊆ M_I`. Proof: the compatibility at `rootSet i ν I` gives
  `jM : Z ⟶ Standard.leviScheme i ν (rootSet i ν I)` with
  `jM ≫ Standard.leviHom i ν _ = j`. So `map j a` is the image of a point of the
  Levi scheme, which lies in `M_I` by the published `Standard.leviPointsEquiv`.
* `exists_isFiniteLatticeTransversal hcompat`: a finite lattice transversal
  `F0` exists. It is the transversal in the fourth conjunct of the
  `DominantCentralizerLatticeConclusions` that `hcompat` provides at the empty
  root set.
* `exists_cartan_levi hcompat hF0 I`: **Cartan decomposition of `M_I`.** For a
  finite lattice transversal `F0`, every `m ∈ M_I` is `k₁ * t * k₂` with
  `k₁, k₂ ∈ K_I` and `t ∈ Λ_I`. Proof: let `J = rootSet i ν I` and take
  `jM` and the comparison `hc : SameCompactLeviCartanComparison D x ν J jM s h`
  from `hcompat`. The fifth conjunct of its lattice conclusions makes
  `tildeC0Plus s F0 Z_dom` a dominant valuation section. The published
  `sameCompactLeviSectionMap_bijective`
  (`Representation/Plancherel/RenardSameCompactLeviComparison`) then says that
  `a ↦ K^M jM(a) K^M` is a bijection from that section onto the double cosets
  `K^M \ M_J(F) / K^M`, where `K^M = D.specialCompactLeviSubgroup ν J x` is the
  preimage of `K₀` in the Levi scheme. Lift `m` to the Levi scheme by
  `Standard.leviPointsEquiv`, use surjectivity to get `a` and `k₁, k₂ ∈ K^M`
  (`DoubleCoset.eq`), and push everything back to `G(F)` with
  `rationalPoints_map_comp_apply`. The images of `k₁, k₂` lie in `K₀` (by
  definition of the preimage) and in `M_I`.

Only the covering half of Renard's Cartan decomposition is stated here:
disjointness of the double cosets is not part of the conclusion. This is the
Lean form of Renard, Théorème V.5.1 (4) applied to the Levi `M_I` through V.5.1
(5), which says `K₀ ∩ M` satisfies (1)–(4) for `M` (printed p. 122, PDF p. 128).
The middle set is the image of `C̃⁺_∅ = (C₀ F₀) ∩ Z_dom` in the notation of
V.3.23. Together with `isCompact_inf_levi` (with `hK` the compactness in
`SpecialCompactProperties`), `inf_le_right`, `countable_image_tildeC0Plus` and
`image_tildeC0Plus_subset_levi`, this gives the Cartan fields of the planned
standard parabolic system with `cartanCompact I = K₀ ⊓ M_I` and
`cartanSet I = Λ_I`.

## Provenance

Internal supporting module. The coset-cover definition and lemmas are Lean
packaging of a standard topological-group fact. The decompositions only combine
published Library results, imported by Lean name, under explicit hypotheses
that are conjuncts of the conclusion of
`JointSpecialCompactBasisExistenceStatement`. The source statements they
formalize are Renard, Théorème V.5.1 (1), (4) and (5).

The forward compactness implication reuses
`compactSpace_leftQuotient_of_compact_representatives` from
`Group.LeftQuotientInversion` after unpacking `HasCompactCosetCover`.
