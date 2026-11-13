# Split tori without proper rational parabolics

Worker 184. This is the algebraic containment step used in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), §9.3.2, printed p.331
(PDF p.362), and the proof of Proposition 9.3.8, printed pp.334–335
(PDF pp.365–366). The Chapter 9 corrections (2024), PDF pp.39–41,
do not amend these passages. This module is an internal derivation from
published Library inputs.

For any field `k : Type u` and connected reductive group `G`, assume every
actual `k`-parabolic subgroup map `p : P → G` is an isomorphism. For every
split torus `S` and actual homomorphism `s : S.toGrp → G`, the proposition
`NoProperParabolicSplitTorusContainmentStatement.{u}` asserts:

* `s` is central on every test scheme, including after all refinements.
* For every actual maximal torus `t : T.toGrp → G`, there is a
  commutative-group-scheme homomorphism `f : S → T` with
  `groupHom f ≫ t = s`.
* If `s` is a closed subgroup map, so is this factor. If `s` is an ambient
  maximal split torus, its factor is maximal split in `T`.

No perfectness, characteristic, cardinality, or local-field assumption is
made. The map `s` need not be a monomorphism for the centrality or
factorization conclusion.

The proof of `IsSplitTorus.isCentral_of_noProperParabolic` chooses a
cocharacter of `S` with the same whole-torus centralizer, using the published
`IsSplitTorus.exists_cocharacter_centralizer` from
`Rational.GenericTorusCocharacter`. Its composite `χ` into `G` has a
closed dynamic parabolic representative
`Dynamic.Affine.parabolicHom χ`. The published
`isParabolicSubgroup_of_range_eq_dynamicParabolic` from
`Absolute.DynamicParabolicRecognition` proves this representative is an
actual rational parabolic. The explicit no-proper-parabolics assumption
therefore makes its original inclusion an isomorphism. Its range, and hence
`Dynamic.parabolic χ`, equals the full subgroup functor.

The published `IsConnectedReductive.isPseudoReductive` and
`pseudoReductiveCentralCocharacter` then imply
`Dynamic.centralizer χ = ⊤`. The selected cocharacter's centralizer
identity gives `torusCentralizer s = ⊤`, and the published
`isCentral_iff_torusCentralizer_eq_top` identifies this with centrality of
the original map `s`.

For containment, the proof reuses the existing
`IsCentral.exists_factor_of_isMaximalTorus` from
`Rational.FiniteFieldMaximalTorusTransporterReduction`. This supporting
theorem is over arbitrary fields despite its module name. It factors a
central torus homomorphism through any maximal torus of a smooth affine
group, using a torus image of the commuting product and maximality.
`Additive.ofMul` expresses the resulting map in the commutative
group-scheme category. The published `IsClosedSubgroup.of_comp` and
`IsMaximalSplitTorus.of_comp` pass the respective properties from the
ambient map to this factor. The maximal-split specialization
`IsMaximalSplitTorus.exists_commFactor_of_noProperParabolic` records
centrality and the actual factor, maximal split inside `T`.

The theorem `noProperParabolicSplitTorusContainment` proves the displayed
Prop-valued statement by these two constructions. The result retains the
no-proper-parabolics hypothesis. It constructs no Gamma-chamber, descended
integral model, reductive quotient, segment-model comparison, or residue
torus lift. Applying it to the quotient in §9.3.2 still requires that
quotient, connected reductivity, its no-proper-parabolics property, and the
relevant split-torus map. In particular, it does not prove
`UnramifiedFixedPointSplitTorusStatement`.
