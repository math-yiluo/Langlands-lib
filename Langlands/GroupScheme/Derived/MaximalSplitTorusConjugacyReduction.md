# Derived maximal split tori from conjugacy of maximal split tori

This module reduces the published `DerivedMaximalSplitTorusStatement`
(`Derived.MaximalSplitTorusStatement`) to rational conjugacy of maximal split
tori in the ambient group. Every conjugacy input is an explicit premise. The
module proves no conjugacy theorem and does not prove the derived statement
unconditionally.

Throughout, `Spec k` means `Spec (CommRingCat.of k)`, and morphisms of group
schemes are actual homomorphisms on all test schemes.

## Definition

For a homomorphism `d : D ⟶ G` of group schemes over `Spec k`,
`MaximalSplitToriContainSubgroupTori d` says: for every commutative group
scheme `S` and every maximal split torus `i : S.toGrp ⟶ G` there are a
commutative group scheme `S_D`, a maximal split torus `j : S_D.toGrp ⟶ D`
and a homomorphism of commutative group schemes `e : S_D ⟶ S` such that
`CommGroupScheme.groupHom e` is a closed subgroup and
`j ≫ d = CommGroupScheme.groupHom e ≫ i`.

This is the conclusion of `DerivedMaximalSplitTorusStatement` with the field,
the ambient group and `d` fixed. It imposes no reductivity, smoothness or
derived-subgroup condition by itself. `derivedMaximalSplitTorusStatement_iff`
records that the published statement is, by definition, this property for
every `d` with `IsDerivedSubgroup d` into a connected reductive `G` over a
field `k : Type u`.

## Theorems

- `SubgroupFunctor.IsRepresentedBy.maximalSplitToriContainSubgroupTori_of_conjugate`.
  Let `G` be a group scheme over `Spec k` whose structure morphism is affine
  and locally of finite type. Let `d : D ⟶ G` be a closed subgroup that
  represents a normal subgroup functor `F`. If
  `MaximalSplitToriAreConjugate G` holds
  (`Rational.MaximalSplitTorusConjugacyReduction`), then
  `MaximalSplitToriContainSubgroupTori d` holds. The lemma uses only
  normality of `F`, not that `F` is the derived subgroup.
- `IsDerivedSubgroup.maximalSplitToriContainSubgroupTori_of_conjugate` is the
  same conclusion for a homomorphism `d` with `IsDerivedSubgroup d`
  (`Derived.Basic`). Such a `d` is a closed subgroup representing
  `derivedSubgroup G` (`IsDerivedSubgroup.isRepresentedBy`), and that
  functor is normal (`derivedSubgroup_isNormal`).
- `derivedMaximalSplitTorus_of_conjugate`: if
  `MaximalSplitToriAreConjugate G` holds for every connected reductive group
  `G` over every field `k : Type u`, then
  `DerivedMaximalSplitTorusStatement.{u}` holds.
- `derivedMaximalSplitTorus_of_smoothMaximalSplitTorusConjugacy`: the
  Borel–Tits statement `SmoothMaximalSplitTorusConjugacyStatement.{u}`
  (`Rational.MaximalSplitTorusStatement`) implies
  `DerivedMaximalSplitTorusStatement.{u}`.
- `derivedMaximalSplitTorus_of_maximalSplitTorusConjugacy`: the reductive
  statement `MaximalSplitTorusConjugacyStatement.{u}`
  (`Rational.ConjugacyStatement`) implies
  `DerivedMaximalSplitTorusStatement.{u}`. Only its first conjunct, the
  conjugacy of maximal split tori, is used.

## Proof of the main lemma

Fix a maximal split torus `i : S.toGrp ⟶ G`.

1. `D` is affine and locally of finite type over `k`. The closed immersion
   `d` commutes with the structure morphisms, so `D`'s structure morphism is
   that of `G` composed with a closed immersion.
2. `exists_maximalSplitTorus` (`Rational.MinimalPseudoParabolicConjugacyAssembly`)
   gives a maximal split torus `j₀ : T.toGrp ⟶ D`.
3. `j₀ ≫ d` is a split subtorus of `G` by `IsSplitSubtorus.comp`
   (`Rational.MaximalSplitTorusSubgroup`). The extension theorem
   `exists_maximalSplitTorus_extension` (`Rational.MaximalSplitTorusExtension`)
   gives a maximal split torus `m : M.toGrp ⟶ G` and a homomorphism `f` with
   `f ≫ m = j₀ ≫ d`.
4. The conjugacy premise, applied to `m` and `i`, gives a rational point `g`
   of `G` and an isomorphism `c : M.toGrp ≅ S.toGrp` with
   `m ≫ (G.innerIso g).hom = c.hom ≫ i`.
5. Since `F` is normal and represented by `d`, conjugation by `g` restricts
   to an automorphism `φ := hr.conjugateIso hn g` of `D`, with
   `φ.hom ≫ d = d ≫ (G.innerIso g).hom` (`conjugateIso_hom_comp`,
   `Absolute.MaximalRankRadicalTorusIntersectionOfComplement`, built from
   `conjugateFactor` in `Rational.NormalRadicalConjugacy`).
6. Put `S_D := T`, `j := j₀ ≫ φ.hom` and let `e` be `f ≫ c.hom`, viewed as a
   morphism of commutative group schemes through `Additive.ofMul`. Then `j` is a maximal split torus
   of `D` by `IsMaximalSplitTorus.comp_iso` (`Rational.SplitRankTransport`).
   The chain of equalities
   `j₀ ≫ φ.hom ≫ d = j₀ ≫ d ≫ int(g) = f ≫ m ≫ int(g) = f ≫ c.hom ≫ i`
   gives `j ≫ d = CommGroupScheme.groupHom e ≫ i`.
7. `j ≫ d` is a closed subgroup of `G`, as a closed subgroup of `D` composed
   with the closed subgroup `d` (`IsClosedSubgroup.comp`). Since it equals
   `CommGroupScheme.groupHom e ≫ i`, and `i` is a closed subgroup,
   `IsClosedSubgroup.of_comp` (`Rational.LeviFactorization`) shows that
   `CommGroupScheme.groupHom e` is a closed subgroup.

The torus `S_D` is not constructed as the intersection `(S ∩ D)⁰_red`, and
`e` need not be surjective.

## Proofs of the corollaries

`derivedMaximalSplitTorus_of_conjugate` rewrites with
`derivedMaximalSplitTorusStatement_iff` and reads off the instances
`Smooth G.X.hom` and `IsAffineHom G.X.hom` from `IsConnectedReductive G`.
Smoothness gives local finite type. It then applies
`IsDerivedSubgroup.maximalSplitToriContainSubgroupTori_of_conjugate`. The smooth
corollary also reads off `ConnectedSpace G.X.left`, the remaining
hypothesis of `SmoothMaximalSplitTorusConjugacyStatement`. For the fixed `k`
and `G`, the conclusion of that statement is `MaximalSplitToriAreConjugate G`
by definition, after unfolding `SubgroupConjugate`. The reductive corollary
takes the first conjunct of `MaximalSplitTorusConjugacyStatement` for `G`,
which is `MaximalSplitToriAreConjugate G` by definition in the same way.

## Provenance

The definition and the reductions are internal. The definition fixes the
field, the ambient group and `d` in the published
`DerivedMaximalSplitTorusStatement`. The proof follows the conjugacy route
set out in the context of the proof task
`45bba50f-b29d-49c2-b923-64037208e2e1`. It differs from the source proof in
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Theorem C.2.15 (printed p.603 / PDF p.629). Step 1 of that proof (printed
p.604 / PDF p.630) applies Remark C.2.12(2) to a maximal `k`-torus
containing `S`, which needs maximal tori and root systems. The conjugacy
premise is the Borel–Tits theorem, Theorem C.2.3 of the same book (printed
p.593 / PDF p.619): all maximal `k`-split tori of a smooth connected affine
`k`-group are `G(k)`-conjugate. When this module was written, neither
`SmoothMaximalSplitTorusConjugacyStatement` nor
`MaximalSplitTorusConjugacyStatement` had a published proof in the Library
(proof tasks `7c6d89b9-d59a-44ce-aac6-95f9fafe7b82` and
`6cba93f0-40f3-481b-8d85-76977bc6e4ef`).
