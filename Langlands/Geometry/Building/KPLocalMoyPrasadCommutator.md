# K-level Moy–Prasad commutators from actual torus estimates

This internal helper adapts the Library's `MoyPrasadCommutatorGenerators`
proof to `B : MaximalUnramified.BuildingData F H`, for
`K = UnramifiedClosure F`, and D1's actual torus filtration with
`hZ : IsTorus B.centralizer.Z`. The field `F` has arbitrary characteristic,
and all declarations are at arbitrary universe `u`.

The final theorem, `localMoyPrasadCommutator_of_torus_commutator_bounds`, has
type `LocalMoyPrasadCommutator B hZ` under the three explicit predicates of
`KPLocalMoyPrasadDoubleRootConjugation`: ordinary torus commutator
friendliness (S1 clause 1), root compatibility (S1 clause 2), and the
independent actual doubled-root estimate requested in Task 6543. These
hypotheses are not discharged in this module. This is not an unconditional
proof of clause 3 or of the full S2 statement.

## Implemented proof

- `exists_eval_eq_of_mem_relativeRoots` uses a generic cocharacter to find a
  real translation giving any prescribed value of a root. The membership
  lemmas `mem_filtration_vadd_of_mem` and `mem_filtration_of_mem_vadd` then
  read depths at translated apartment points using
  `KPApartmentData.filtration_mk_vadd`.
- `moyPrasad_eq_closure` rewrites D1's subgroup as the closure of its torus
  image and the union of its individual root filtrations. The theorem
  `filtrationBlock_vadd_subset_moyPrasad` places a root block at a translated
  point in the original-point subgroup whenever both translated-back root
  depths have the required bound.
- `commutator_mem_of_opposite_coordinates` is algebraic bookkeeping using
  `B.oppositeRootTripleProduct_injective`. Given an exchange
  `v₁ c u₁ = u v`, the last coordinates of two conjugation decompositions
  determine `u₁u⁻¹` and `v⁻¹v₁`. If both coordinates and `c` lie in a subgroup
  normalized by `v`, multiplication and conjugation place `⁅u,v⁆` there.
- `commutator_opposite_mem_moyPrasad` treats ordinary opposite roots at
  positive depths `r,s`. The actual middle coordinate has depth `r+s` by
  `exists_rankOne_depth_factorization`. Translate separately to points where
  each input has depth zero. The coordinate bounds from
  `IntegerRootConjugation`, read back at `x`, give the required positive and
  negative coordinates in `B.moyPrasad hZ x (r+s)`. The preceding bookkeeping
  theorem finishes under an explicit normalizer-membership hypothesis.
- `commutator_double_opposite_mem_moyPrasad` treats an ordinary root element
  at depth `r` and an opposite doubled-root element at depth `s`. At the
  point where the first input has depth zero, the doubled input has depth
  `s+2r`. The independent doubled-root predicate therefore places the
  middle coordinate at depth `s+2r`, hence at depth `r+s`. Mixed and ordinary
  conjugation coordinate bounds from `IntegerMixedConjugation` and
  `IntegerRootConjugation`, at appropriate translations, supply the other
  two coordinates. The same bookkeeping theorem finishes. The ordinary
  root valuation of the doubled element is used only at half its doubled
  depth, as required by the valuation axioms.
- `generator_commutator_mem_moyPrasad` combines four kinds of generators.
  Two torus-image elements commute since the centralizer is a torus.
  Torus/root pairs use root compatibility and its inverse. For two root
  elements, V3 treats nonopposite directions, and every positive integral
  combination has depth at least `r+s`. Negative proportional roots are
  ordinary opposite or doubled in one of the two directions, by the
  integer extended-affine-root system proved in
  the published `IntegerValuationExtendedAffineRoots` and `exists_order_eq_one F`. The
  preceding two opposite-root lemmas apply; inversion swaps the mixed
  orientation when necessary. Normalization of the target subgroup comes
  from the conditional clause 1 already proved in
  `KPLocalMoyPrasadDoubleRootConjugation`, together with antitonicity.
- `localMoyPrasadCommutator_of_torus_commutator_bounds` handles depth zero
  directly by that same conditional normality. For two positive depths it
  applies the published, field-independent
  `commutator_closure_le_of_le_normalizer` to the two sets of generators,
  inside `B.moyPrasad hZ x 0`, which normalizes the target of depth `r+s`.

## Provenance and limits

The source target is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Proposition 13.2.5(4), printed p.469 (PDF p.500). The implemented
proof uses the algebraic generator and translated rank-one route already
formalized in the Library for F-level supplied filtrations. It does not
instantiate `ParahoricBuildingData` over `K`, whose residue field is
infinite. The affine-root-system inputs are proved for integer-valuation
building data; no apartment axiom is added as a premise. The registered
2024 corrections, PDF p.33, qualify the chapter-7 apartment-axiom usage.

The independent sharper torus estimate is motivated by the quasi-split
SU3 computation in the proof of KP Proposition 7.1.1 (printed pp.239–240,
PDF pp.270–271). This module assumes it explicitly and does not derive it
from normality, Iwahori factorization, or torus intersection. Consequently
there is no dependency on the parent S2 conclusions in that estimate.
Acceptance of this conditional helper alone would not discharge the exact
unconditional S2 target.
