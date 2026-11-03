# General semistandard parabolic intersection target

`DynamicSemistandardIntersectionStatement` is a proposition over every field
`k : Type u` and every connected reductive group scheme `G` over `Spec k`.
It fixes a maximal split torus `i : T → G` and two arbitrary cocharacters
`α, β` of `T`. Set `χ = α ≫ i`, `ψ = β ≫ i`, and write
`P = P(χ)`, `M = Z(χ)`, `N = U(χ)`, `Q = P(ψ)`, `L = Z(ψ)`,
`U = U(ψ)`. There is no inclusion or nesting hypothesis on these
parabolics or their Levis.

For any actual group scheme representing `M` by a closed homomorphism
`j`, the target asserts three conclusions.

- The actual pullback `Q.comap j` is a parabolic subgroup functor inside
  that representative, with Levi `L.comap j` and geometric unipotent
  radical `U.comap j`, in the precise sense of
  `SubgroupFunctor.IsParabolicWithLeviAndRadical`.
- On every test scheme, `M ∩ Q = (M ∩ L)(M ∩ U)` and
  `N ∩ Q = (N ∩ L)(N ∩ U)`, in the sense of
  `SubgroupFunctor.SemistandardIntersectionProducts`.
- The common torus lifts to a maximal split torus `iM` of the
  representative of `M`, with `iM ≫ j = i`, and its range is contained
  in `Q.comap j` on every test. Thus the intersection parabolic is
  semistandard relative to this lifted torus.

The first conclusion supplies actual representatives of the parabolic,
its connected reductive Levi and its smooth connected normal unipotent
radical. The radical is maximal after extension to an algebraic closure.
The conclusion also supplies normal complementary factors and the
ordered product on every test. These conditions are specified in the
imported definition pair `Rational.SemistandardIntersection`.
The equalities in the second conclusion are literal products of sets
of maps into `G`, rather than generated subgroups. All tests over the
field occur, including nonreduced schemes. The theorem
`SemistandardIntersectionProducts.identityTest` specializes the two
products to the identity test, giving the actual rational-point formulas.

The closed representative is arbitrary, as in the existing represented
dynamic-centralizer interfaces. Representability of the dynamic
centralizer and its reductivity remain separate structural obligations;
the target does not choose a privileged representative. No
correspondence, intersection decomposition or radical identification is
assumed in its hypotheses.

## Elementary torus comparison

`IsMaximalSplitTorus.exists_lift_to_centralizer_parabolic` proves only
the torus-lift conclusion, without assuming the structural target or
reductivity of `G`. The implemented proof uses that the image of a
commutative group centralizes each of its cocharacters. The existing
`IsMaximalSplitTorus.exists_lift` then factors `i` through the closed
centralizer representative and proves maximality there. The factorization
equality and `range_le_dynamicParabolic` place this lift in the other
parabolic on every test. This elementary comparison does not prove
parabolicity, the Levi/radical assertion or either product.

## Original sources and derived scope

Renard, 9 July 2026 edition, V.3.8 and V.3.10, printed pp.111–112
(PDF pp.117–118), fixes a common maximal split torus and chooses the
Levi containing it. V.3.10 treats two arbitrary semistandard parabolics
`P=MN`, `Q=LU`: `M ∩ Q` is a semistandard parabolic of `M`, with
Levi `M ∩ L` and radical `M ∩ U`, and
`N ∩ Q = (N ∩ L)(N ∩ U)`. The first product in this target is the
asserted Levi decomposition. Nesting is used in the separate VI.1.4
target, not in V.3.10.

Renard's governing passage concerns a nonarchimedean local field. The
arbitrary-field, represented-subgroup and all-test target here is
**derived**. Borel–Tits 1965 §0.3, printed pp.57–58
(PDF pp.4–5), permits the affine absolutely reduced scheme
interpretation. Sections 4.4(c) and 4.7, printed pp.86–88
(PDF pp.33–35), give the parabolic-in-Levi structure and rationality
of intersections and Levi factors. Milne 2017 §25.1 and §25.6–25.7,
printed pp.544–546 (PDF pp.560–562), supplies the cocharacter
framework and parabolic-intersection setting. Milne §6.45–6.46,
printed p.135 (PDF p.151), motivates the imported radical predicate.
These sources motivate this modern dynamic formulation; they do not
constitute a Lean proof or a literal all-test statement in Renard.

The registered official Milne errata has been read. The corrected
§25.6(b) concerns minimal parabolics, and the relative-root-system proof
warning supplies no root-classification assumption here. The target
uses centralizers of the chosen cocharacters, without asserting that
an arbitrary Levi is the centralizer of the whole maximal split torus.
The 2010 Renard correction requiring semistandard parabolics in VI.1.4
concerns the separate nested target; V.3.10 already states that setting.

The module defines the final structural assertion as a `Prop`. Its
proof is a separate obligation. The elementary torus-lift theorem
establishes only the comparison stated above.

Source IDs:
`renard-2026-representations-groupes-reductifs-padiques`,
`borel-tits-1965-groupes-reductifs`,
`milne-2017-algebraic-groups`, and
`milne-2017-algebraic-groups-errata-2026-11-02`.
