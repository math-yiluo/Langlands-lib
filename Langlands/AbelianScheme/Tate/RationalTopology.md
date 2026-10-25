# Topology and continuous monodromy on actual rational Tate modules

This construction equips the existing rational Tate carriers of an abelian scheme with the final topology of their actual integral Tate limits. It proves the open-lattice, Hausdorff and topological additive group properties for the full and prime-to-modulus systems. At a field-valued point it derives local compactness and a compact open integral image from the explicit geometric finiteness hypotheses, and proves joint continuity of the already published rational geometric monodromy.

## Construction and provenance

`rationalTopology A T P` is exactly `Langlands.Topology.Rationalization.finalTopology (Integral A T P)` on the existing carrier `Rational A T P = ℚ ⊗[ℤ] Integral A T P`. The integral group is the actual compatible family of torsion points at the test scheme `T`, with its published product-subspace topology. The selection predicate `P` is applied to positive torsion orders before rationalization. The open-set formula `isOpen_rationalTopology_iff` says that a set is open precisely when its preimage under every map `x ↦ q ⊗ x`, for `q : ℚ`, is open in the integral limit.

This is an internal specialization of the published generic construction in `Topology.Rationalization.Basic` and `Topology.Rationalization.Lattice`, using the actual Tate multiplication theorem in `Tate.MultiplicationTopologyProof` and the actual geometric actions in `Tate.IntegralMonodromy` and `Tate.RationalMonodromy`. These imported modules document their own source provenance. The new module is not a transcription of a literature theorem. It introduces no replacement carrier, supplied output topology, finite-rank hypothesis, or assumed comparison equivalence.

The topology is available for local installation with `letI := rationalTopology A T P`. Its instance attribute is local to this module; importing the module does not register a global topology on tensor products. The topological group, separation, local compactness and action continuity conclusions are likewise named results for local installation. All conclusions use this exact topology.

## Arbitrary selected systems and maps

For every `P`, `continuous_rationalChart` proves continuity of every rational chart, including zero. `continuous_rational_smul` proves continuity of multiplication by a fixed rational number. `continuous_toRational` specializes the chart at one to the existing integral-to-rational map. `continuous_rationalMap` applies the generic scalar-extension continuity theorem to the existing continuous integral map of an actual abelian-scheme homomorphism. `continuous_rationalRestrictAway` applies the same theorem to the existing full-to-away restriction.

These results need no finite-level finiteness or invertibility assumption. They assert continuity of the named maps, not joint scalar continuity for any topology on the rational numbers or on the finite adeles.

## Full and prime-to-modulus lattices

`isOpenEmbedding_full_toRational` and `isOpenEmbedding_away_toRational` identify the respective integral limits with open subspaces of their rationalizations. They apply the generic integral-chart theorem using the published `fullMultiplicationOpenEmbeddings` and `awayMultiplicationOpenEmbeddings` proofs for these actual limits. Thus positive multiplication being an open embedding is proved for the carriers being used, rather than supplied as a new hypothesis.

The same inputs give `rationalFull_topologicalAddGroup`, `rationalAway_topologicalAddGroup`, `rationalFull_t2Space`, and `rationalAway_t2Space`. Hausdorffness of the integral limit comes from its existing product of discrete torsion levels. These assertions hold for arbitrary test schemes, and the away assertions cover every natural modulus, including zero and one. There is no assertion that the corresponding lattice condition holds for an arbitrary selection predicate.

## Geometric compactness

Fix `s : Spec Ω ⟶ S` for a field `Ω`. The geometric hypotheses are `hfin`, finiteness of every finite étale cover's actual fibre at `s`, and `htor : TorsionFiniteEtaleStatement`. Full results require invertibility on `S` of every positive retained order. Away results require invertibility only for positive orders coprime to the given modulus.

`integralMonodromy_compactSpace` supplies compactness of each selected integral limit from the actual finite torsion kernels and the fibre-finiteness input. The module then applies the generic rationalization theorems to prove `rationalFull_compactOpen_integral` and `rationalAway_compactOpen_integral`, together with `rationalFull_locallyCompactSpace` and `rationalAway_locallyCompactSpace`. The compact open set is the range of the existing map `GroupScheme.Tate.toRational`.

The declarations explicitly retain both geometric hypotheses and the invertibility witnesses. They do not prove the torsion finite-étaleness theorem or infer its truth from an arbitrary structure field. Algebraic closedness, connectedness and local noetherianness are unnecessary for these formal conclusions once the displayed finiteness hypotheses are supplied; the usual geometric application can impose them separately.

## Joint continuity of the actual action

The private continuity lemma locally installs the published integral geometric action and its joint continuity instance. The generic `continuous_actionMap` then applies: its map is definitionally the rational scalar extension of `integralMonodromyHom`, exactly the existing `rationalMonodromy` map. No new geometric action is defined.

`continuous_rationalFullMonodromy` and `continuous_rationalAwayMonodromy` discharge the required open-multiplication condition using the published full and away proofs. They establish continuity on the product of the actual fundamental group, with its existing pointwise topology, and the actual rational Tate module, with `rationalTopology`. The final two `continuousSMul` theorems package these conclusions for the existing `rationalMonodromyAction`, preserving its identity, composition and additive laws.

This module does not assert a topological restricted-product identification, joint finite-adelic scalar continuity, continuity of maps induced by arbitrary rational homomorphisms, Weil-pairing properties, or a trivialization of the Tate twist. Those require separate constructions or arguments.
