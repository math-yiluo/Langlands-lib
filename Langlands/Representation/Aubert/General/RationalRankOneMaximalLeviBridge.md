# Rational rank-one self-association from Renard VII.1.3

Author: Worker 3916 (formerly Worker 63). Module
`Langlands.Representation.Aubert.General.RationalRankOneMaximalLeviBridge`.

This supporting unit proves that the published Renard VII.1.3 statement
`RepresentedParabolic.MaximalLeviSupercuspidalReducibilityStatement` implies the
published target `RationalPointFamily.RationalRankOneSelfAssociationStatement`.
It introduces one `Prop`-valued definition, the implication
`RationalRankOneSelfAssociationFromMaximalLeviStatement.{u, v}`, and proves it in
the same module. The unit proves neither VII.1.3 nor the target. The target
follows as soon as VII.1.3 is proved at universes `u, max (u + 1) v`.

The other structural inputs of the proof are published theorems. They include
`parabolicDynamic` (Milne 25.1) and `smoothMaximalSplitTorusConjugacy`
(Borel–Tits, CGP C.2.3). They are not premises.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026 (registered source
`renard-2026-representations-groupes-reductifs-padiques`), VII.1.3, Théorème
(printed p.224 / PDF p.230). For a maximal standard Levi `M` with
`W(M,∗) = {1, w}` and `M′ = w·M`, the theorem says: if `i_P^G(ρ)` is reducible
for an irreducible supercuspidal `ρ` of `M`, then `M = M′` and
`ρ^w = ρψ` for an unramified character `ψ` with values in `ℝ*₊`.

The target's conclusion `associatedSubset actual J = J`, for
`J = univ.erase α`, is the statement `M′ = M` for `M = M_J`. The published
`MaximalLeviSupercuspidalReducibilityStatement` formalizes VII.1.3 for arbitrary
actual maximal parabolics. Its conclusion supplies `g ∉ M(F)` and `φ : M ≅ M`
with `φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom`, so `g` normalizes `M`. It
also supplies the twist `ψ`. This unit uses only `g` and `φ`.

## The statement

```
def RationalRankOneSelfAssociationFromMaximalLeviStatement : Prop :=
  RepresentedParabolic.MaximalLeviSupercuspidalReducibilityStatement.{u, max (u + 1) v} →
    RationalRankOneSelfAssociationStatement.{u, v}
```

Both sides are the published propositions, unchanged. The target instantiates
`rankOneSelfAssociation.{u, u, max (u + 1) v}`. Its representations `σ` of the
literal Levi subgroup are finite-length objects with carriers in
`Type (max u (max (u + 1) v))`, which is `Type (max (u + 1) v)`. VII.1.3 is
therefore used with Levi carriers in that universe. A proof of VII.1.3 at all
universes discharges the premise.

Provenance: internal. The implication is not a numbered statement of the
literature. It records that the self-association half of Renard VII.1.3
discharges the published rank-one target. The theorem
`rationalRankOneSelfAssociation_of_maximalLeviSupercuspidalReducibility` proves
it.

## Proof

The proof goes through the published normalizer form
`RationalRankOneNormalizingWeylStatement`
(`RationalRankOneNormalizingWeyl.md`). Its conclusion asks, for a maximal
standard `J`, for a point of `Group.RelativeWeyl.normalizer (torusPoints i)` that
normalizes `levi i ν J` and does not lie in it. The published
`rationalRankOneSelfAssociation_of_normalizingWeyl` turns this into the target.

### Torus correction (`RepresentedParabolic` namespace)

- The existing `pointImage_iso_comp` from
  [ArbitraryParabolicLeviReparametrization](../../Exponents/ArbitraryParabolicLeviReparametrization.md)
  says that precomposing with an isomorphism does not change a point image.
  This module imports and reuses that declaration.
- `exists_torusNormalizer_of_leviNormalizer`: let `j : M ⟶ G` be a closed
  connected reductive subgroup, `iM` a maximal split torus of `M`, and
  `g : G(F)` with `φ.hom ≫ j = j ≫ (G.innerIso g).hom` and `g ∉ M(F)`.
  `smoothMaximalSplitTorusConjugacy`, applied inside `M` to `iM` and
  `iM ≫ φ.hom`, gives `m ∈ M(F)` conjugating one into the other. With `m'` the
  image of `m` in `G(F)`, the point `n = g⁻¹ m'` normalizes the torus image,
  normalizes `M(F)`, and lies outside `M(F)`. The proof uses
  `mem_pointImage_comp_innerIso`, `innerIso_hom_comp` and group identities.

### Induction presentations

`normalizedInduction_isIrreducible_congr`: equal parabolic, Levi and radical
subgroups, with an equivariant linear equivalence of the inducing
representations, give equivalent irreducibility of normalized inductions. The
proof substitutes the equalities and transports along `SmoothRep.mkIso`.

### Maximality of the standard maximal parabolic

- `isIso_of_closedSubgroup_range_eq_top` and `isIso_of_comp_eq_of_range_eq`: a
  closed subgroup with full range is an isomorphism, and a factor between
  closed subgroups with the same range is an isomorphism. Both use
  `IsRepresentedBy.isoOfIsRepresentedBy`.
- `standardParabolic_simpleRelativeRoots_eq_top`: the standard parabolic of all
  simple roots is the whole group. The zero cocharacter is standard for it,
  and its dynamic parabolic is everything.
- `standardParabolic_isMaximal`: let `J = univ.erase α`, and let `q : Q ⟶ G` be
  an actual parabolic with `j ≫ q = Standard.parabolicHom i ν (rootSet i ν J)`.
  Then `j` or `q` is an isomorphism. By `parabolicDynamic`, the range of `q` is
  `Dynamic.parabolic χ`. The minimal standard parabolic
  (`standardParabolic_empty_eq_dynamic_of_generic`) lies below it. So
  `exists_standardParabolic_eq_of_parabolic_le_of_structural_statements` gives
  `K` with range `standardParabolic K`. Its inputs are
  `smoothMaximalSplitTorusConjugacy`, `dynamicConnected`,
  `relativeRootSignInclusions` and `relativeRootNegation`. The root
  comparison `standardParabolic_order_of_root_comparison` gives
  `rootSet J ⊆ K`. If `α ∈ K`, then `K` is every simple root and `q` is an
  isomorphism. Otherwise `K = rootSet J` and `j` is an isomorphism.

### Standard Levi specialization

`exists_torusNormalizer_of_standardLeviNormalizer` applies the torus correction
to the actual standard Levi scheme. It uses `standardLeviScheme_isConnectedReductive`
and the maximal split torus `standardLeviTorusFactor`. The point image of
`Standard.leviHom` is `levi i ν J`, and that of the torus factor followed by
`Standard.leviHom` is `torusPoints i`. Membership in the normalizer of
`torusPoints i` comes from `Subgroup.mem_normalizer_iff`.

### Representation-theoretic inputs to VII.1.3

These lemmas live in a section with the canonical point topology on `G(F)`.

- `isSupercuspidal_pullback_of_isCorollaryLeviCuspidal`: inside-Levi standard
  cuspidality `IsCorollaryLeviCuspidal` of `σ` (zero standard Jacquet modules
  inside `levi i ν J`) gives `IsLeviCuspidal`. The published
  `rationalLeviCuspidalityTransport` turns this into `IsCuspidal` for the Levi
  scheme's own standard family. The published `isSupercuspidal_of_isCuspidal`
  (with `parabolicDynamic` and `smoothMaximalSplitTorusConjugacy`) then gives
  `IsSupercuspidal`. This is vanishing of the Jacquet modules of the pullback
  of `σ` along `leviRationalPointHomeomorph` for every actual proper parabolic
  of the Levi scheme, which is the cuspidality premise of VII.1.3. The Levi
  scheme's standard data come from `standardLeviStandardFamilies` and
  `HasRelativeRootSystem.of_standardLeviTorusFactor`.
- `leviInduction_isIrreducible_iff_standard`: the published
  `leviInductionFunctor` of the standard triple is irreducible on the pulled
  back representation exactly when the normalized induction from the literal
  standard family is irreducible on `σ`. The triple carries its parabolic,
  Levi, radical and multiplication data explicitly, with the Levi topology
  `leviPointTopology`. The proof rewrites by `leviInductionFunctor_obj` and
  identifies the point images of the parabolic, Levi and unipotent schemes. It
  then applies `normalizedInduction_isIrreducible_congr` with the identity
  linear map. Equivariance follows from `leviRationalPointHomeomorph_apply_coe`
  and `leviPointsEquiv_apply_coe`.
- `exists_torusNormalizer_of_maximalLeviSupercuspidalReducibility`: the VII.1.3
  application. `standard_representatives_geometric_of_standardCocharacter`
  supplies the actual parabolic, Levi, radical and multiplication data.
  Properness comes from `standardParabolic_ne_top_of_ne_univ` and maximality
  from `standardParabolic_isMaximal`. The pulled back representation is
  irreducible (`CuspidalSupport.isIrreducible_comp_of_surjective`),
  supercuspidal and reducibly induced, by the two lemmas above. VII.1.3 returns
  `g` and `φ`, and `exists_torusNormalizer_of_standardLeviNormalizer` corrects
  `g`.

### Assembly

`rationalRankOneNormalizingWeyl_of_maximalLeviSupercuspidalReducibility`
introduces the binders of `RationalRankOneNormalizingWeylStatement`, writes the
maximal standard `J` as `univ.erase α`, and applies the previous lemma. It
supplies the closedness `hM J` and `isSemidirectDecomposition_in_levi`.
`rationalRankOneSelfAssociation_of_maximalLeviSupercuspidalReducibility`
composes this with `rationalRankOneSelfAssociation_of_normalizingWeyl`.

The VII.1.3 application is a separate lemma for elaboration performance only.
Applied directly inside the assembly, the reducibility premise exceeded the
heartbeat limit.

## Scope

- No premise is added to the target. The implication's only hypothesis is
  VII.1.3.
- The positive unramified twist in the conclusion of VII.1.3 is not used.
- The module checks with zero diagnostics. The final theorem depends only on
  the axioms `propext`, `Classical.choice` and `Quot.sound`.
