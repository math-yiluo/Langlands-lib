# Scheme and point-image relative Weyl comparisons

This derived consumer module makes the remaining scheme-to-point comparison
explicit for the actual torus point image constructed in `RationalPointFamily`.
It states the comparison at general connected-reductive scope over a
nonarchimedean local field. It proves the elementary normalizer inclusion and
constructs a quotient equivalence conditional on both subgroup equalities.
The universal comparison statement itself is unproved.

All declarations are in
`Langlands.Aubert.General.RationalPointFamily`. For a field `k`, an actual
commutative group scheme `T`, a group scheme `G` over `Spec k` and
`i : T.toGrp ⟶ G`, `torusPoints i` is the literal image on identity-test
rational points. The two named propositions are:

- `HasPointNormalizerComparison i`: `GroupScheme.normalizerPoints i` equals
  the abstract subgroup normalizer of `torusPoints i`.
- `HasPointCentralizerComparison i`: `GroupScheme.centralizerPoints i`
  equals the full abstract centralizer of that same image.

These equalities are not definitions of the scheme normalizer or centralizer.
Their scheme sides test a group-scheme automorphism or identity on the entire
torus, whereas their image sides only test its rational points.
`normalizerPoints_le_pointNormalizer` is proved for every field and every `i`
in this scope, without connected reductivity, closed immersion or splitness.
Its proof evaluates a normalizing torus automorphism at a rational point and
uses closure under conjugation to get the subgroup-normalizer inclusion.
The centralizer inclusion is already proved in `RationalPointFamily`.
Neither inclusion proves its converse.

`RationalWeylComparisonStatement` universally quantifies `k : Type u` with
`Field`, `ValuativeRel`, `TopologicalSpace` and
`IsNonarchimedeanLocalField` instances, a group scheme `G`, an actual proof of
`GroupScheme.IsConnectedReductive G`, a commutative group scheme `T`, and
an actual `i` satisfying `GroupScheme.IsMaximalSplitTorus i`. Its conclusion
is the conjunction of the two displayed equalities. No characteristic-zero,
split-ambient-group, quasisplit, positive-rank, or generic-cocharacter
assumption is added. No substitute abstract reductive-group structure is used.
The local-field predicate supplies the genuine valued topology, local
compactness and nontrivial valuation; this statement does not assert the
comparisons over arbitrary finite fields.

Given both equalities as hypotheses, `normalizerEquiv` is the identity on
the underlying ambient points, with only the membership proof changed.
`normalizerEquiv_apply` records this formula. The proved
`normalizerEquiv_map_denominator` transports the entire scheme-centralizer
denominator to the full point-image centralizer denominator. It uses the
centralizer equality in both directions. `weylEquiv` then applies Mathlib's
quotient-group congruence to obtain
`GroupScheme.relativeWeylGroup i ≃* RationalPointFamily.Weyl i`.
`weylEquiv_mk` sends each normalizer class to the class of the same ambient
point. Thus the equivalence uses the actual numerator and denominator maps,
with no arbitrary relabeling of quotient elements.

`finite_weyl_of_scheme` transports an explicitly assumed
`Finite (GroupScheme.relativeWeylGroup i)` through this equivalence.
It supplies no finiteness instance without that premise and the two
comparisons. Actual simple-root finiteness, scheme-Weyl finiteness,
standard-Levi Weyl image comparison, Coxeter realization, root signs,
standard/dynamic equalities and endpoint assertions remain separate.
The module neither proves an Aubert identity nor adds a
representation-theoretic premise to an external structural package.

The source motivation is Renard, *Représentations des groupes réductifs
p-adiques*, version of 9 July 2026, V.4.1 and V.4.3, printed pp.118–119
/ PDF pp.124–125. V.4.1 uses `N_G(A_empty)/Z_G(A_empty)`, and V.4.3
uses the same full-centralizer denominator for the standard Levi inclusion.
The particular scheme-to-rational-image equalities here are explicit
implementation comparison targets, not separately numbered assertions in
Renard and not additional external hypotheses attributed to him. The
implemented proofs are evaluation of the normalizing-point identity,
transport along subgroup equality, quotient congruence and transport of
finiteness along a surjection.
