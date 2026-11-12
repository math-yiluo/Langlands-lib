# Orbit grades of `r_I ∘ i_J` as actual normalized geometric terms

Module: `Langlands.Representation.Aubert.General.RationalGeometricOrbitTerm`,
namespace `Langlands.Aubert.General`. Author: Worker 4021.

This module works with the actual rational standard family. It takes the
published support filtration of `r_I ∘ i_J` (`jacquetSupportFiltration`,
module `ParabolicSupportFiltration`). It identifies the grade at an orbit
`P_J n⁻¹ P_I` with the published normalized geometric term
`geometricTermFunctor … I J n` (module `GeometricK0Target`). That term is the
source normalized Jacquet functor in `M_J`, followed by conjugation
`x ↦ σ(n⁻¹ x n)` and target normalized induction in `M_I`.

The identification is conditional on one equation: the two original epsilon
corrections must cancel, `geometricEpsilonOne … * geometricEpsilonTwo … = 1`.
This equation is an explicit hypothesis `hε` of the two final declarations. It
is not proved here.

## Generic helpers

- `twistFunctorIsoOfEqOne χ h` covers a smooth character `χ` whose underlying
  homomorphism is `1`. It is a natural isomorphism from `χ.twistFunctor` to the
  identity functor of `Rep R H`, with identity linear maps.
- `IsSemidirectDecomposition.eq_one_of_mem_levi_of_mem_unipotent` states that
  in an actual decomposition `P = M ⋉ U` the Levi and the radical meet
  trivially. Proof: the projection fixes `M` and kills `U`.
- `refinementParabolic_subgroupOf_levi` takes a subgroup `Pψ` whose underlying
  set is the product `(M_I ⊓ Q) · U_I`. It shows that `Pψ.subgroupOf M_I`
  equals `(M_I ⊓ Q).subgroupOf M_I`.

## Compactness of the target coset space

`compactSpace_leftQuotient_geometricTarget` proves
`CompactSpace (LeftQuotient ((M_I ∩ n P_J n⁻¹).subgroupOf M_I))`, for the
canonical `pointTopology` over a nonarchimedean local field. Its premises are
`StandardCocharacterStatement`, connected reductivity, the maximal split torus,
the generic cocharacter and `HasPointNormalizerComparison`. It also needs a
topological, weakly locally compact group structure on `G(k)`, closedness of
`P_I` and continuity of the `P_I` Levi projection.

The proof takes the cocharacter `ψ` from the published
`exists_geometric_common_levi_refinements`. Its rational parabolic is literally
`(M_I ∩ n P_J n⁻¹) · U_I` and is contained in `P_I`. The published
`BruhatTits.dynamicParabolicQuotientCompact` makes its coset space compact.
The published `compactSpace_leftQuotient_subgroupOf_levi` passes compactness to
the trace on `M_I`. The helper above identifies that trace with the literal
target intersection.

## Grade comparison

The section `Grade` fixes the canonical `pointTopology` on `G(k)`. Its
premises are:

- local compactness, the nonarchimedean group structure and Hausdorffness;
- `StandardCocharacterStatement`, connected reductivity, the maximal split
  torus, the generic cocharacter and `HasPointNormalizerComparison`;
- the original decompositions `dI`, `dJ`;
- closedness of every standard Levi and radical (`hM`, `hU`), and of `P_I`,
  `P_J`;
- continuity of both Levi projections;
- the limit-of-compact-subgroups property of `U_I` and `U_J`;
- the actual source and target intersection decompositions `hSource`,
  `hTarget` at the given torus-normalizer point `n`.

Second countability of `G(k)` is not a premise. It is derived internally from
the published `reductiveRationalPoint_secondCountable`.

- `geometricEpsilonCompactTermIso hε` relates the published
  `geometricTermEpsilonCompactFunctor`, i.e. compact induction from
  `K = (M_I ∩ n P_J n⁻¹).subgroupOf M_I` of the inducing coefficient twisted
  by the inflated product `ε₁ε₂`, to `geometricTermFunctor`. After
  `⋙ SmoothRep.toRep`, the two are naturally isomorphic. Under `hε`, the
  inflated character is trivial, so `twistFunctorIsoOfEqOne` removes the twist.
  The published `Induction.compactSmoothIso K`, with the compactness above,
  replaces compact by smooth induction. The published
  `geometricTermFunctor_eq_inducing` (`rfl`) recognizes the result as the
  normalized geometric term.
- `jacquetSupportGeometricTermIso hε s q hq` takes an ordered orbit cover
  `s : Geometric.OrderedDoubleCosets P_J P_I m` with
  `s.representative q = n`. It gives a natural isomorphism

  `(jacquetSupportFiltration dJ (hU J) dI (hU I) s).graded q ≅ geometricTermFunctor … I J n hSource hTarget ⋙ SmoothRep.toRep`.

  The isomorphism composes five published or previously staged pieces:
  1. `jacquetSupportOrbitIso`. It needs compactness of `P_J \ G(k)`, obtained
     from `compactSpace_leftQuotient_parabolic` with
     `dynamicParabolicQuotientCompact`, and `U_I.subgroupOf P_I` being a limit
     of compact subgroups, obtained from `isLimitOfCompactSubgroups_subgroupOf`.
  2. `orbitPieceCoinvariantsIso` (module `RationalGeometricOrbitSource`).
  3. The inverse of `geometricNormalizedCompactSourceRepIso`.
  4. The published `geometricNormalizedCompactActualNatIso`, whiskered by
     `SmoothRep.toRep`.
  5. `geometricEpsilonCompactTermIso`.

The convention is the general orbit convention: the term for `n` sits at the
orbit of `P_J n⁻¹` in `P_J \ G / P_I`.

Universes: the field universe `u` and the carrier universe `uV` are
independent. The filtration acts on `SmoothRep.{0,u,max u uV}` and the term is
`geometricTermFunctor.{u,u,uV}`.

## Provenance and dependencies

This is an internal derived assembly for the rational geometric lemma. BZ77 5.2
and Renard VI.5.1, printed p.171, identify the graded pieces with
`i^{M_I}_{M_I ∩ nP_Jn⁻¹} ∘ n ∘ r^{M_J}_{M_J ∩ n⁻¹P_In}`. The proof bodies use
only the declarations named above, together with categorical whiskering and
composition. They use no geometric-lemma expansion, adjointness, cuspidal
support, character independence or Langlands classification. The imported
module closure is larger.

The epsilon cancellation `hε` and the construction of an ordered orbit cover
indexed by minimal Weyl representatives are separate obligations. So is the
final exact-K0 expansion.
