# Proof of the transport of the factor clauses to Henniart's composite map

Lean module: `Langlands.Global.Factors.HenniartCompositeFactorProof`.

Authors: Worker 5130 and Worker 5731 (Task 5230).

## Statement proved

`Langlands.Global.PoleComparison.henniartCompositeFactor` proves
`Langlands.Global.PoleComparison.HenniartCompositeFactorStatement.{uF, uK, uW, uP, uE}`
(Library `Langlands/Global/Factors/HenniartCompositeMapStatement.lean`). The
setting is a Galois extension `E/F` of number fields, a class family `c`, a finite
place `v` and an isometry `T : weilImage F E c v ≃ₗ[ℤ] automorphicImage F E c v`.
Suppose `T` satisfies `RelativeIsometryFactors`: it has the determinant clause at
`F_v` for every geometric reciprocity candidate of `F_v`, and the pair L- and
epsilon-factor clauses at `F_v` for every nontrivial additive character of `F_v`.
Then for every prime `p` with `h : residuePrime v = p`, every p-adic field `K` and
every `ℚ_p`-algebra isomorphism `f : K ≅ F_v`, the composite
`henniartCompositeMap F E c v h K f T` has `FactorProperties` at `K`. That means
the determinant clause for every geometric reciprocity candidate of `K`, and the
pair-factor clause for every nontrivial additive character of `K`. These are the
factor clauses of Henniart (2000), 3.8, with the conventions of `K`. No hypothesis
is added.

## Mathematical idea

Henniart's composite at `K` (§3.7) pulls a class back from `K` to `F_v` on the Weil
side, applies `T`, and pulls back from `F_v` to `K` on the supercuspidal side. Each
clause at `K` comes from the same clause at `F_v`, once every convention of `K` is
moved to `F_v` along `f`: the reciprocity candidate, the additive character, the
self-dual measure and the local-constant system. The factors on both sides must
then be shown to match under the two pullbacks. The clauses at `F_v` quantify
over conventions of `F_v` and those at `K` over conventions of `K`, so each
transport is proved explicitly.

## Proof of the final theorem

`henniartCompositeFactor` introduces the data of the statement and splits
`RelativeIsometryFactors` into its two conjuncts.

* Determinant clause: `determinantCompatibility_henniartCompositeMap`
  (`HenniartCompositeFactorDeterminant`), applied to each geometric candidate `e`
  of `K`.
* Pair-factor clause: `pairFactorCompatibility_henniartCompositeMap`
  (`HenniartCompositeFactorPair`), applied to each additive character `ψ` of `K`.

## Supporting modules

Each module has its own Markdown with the lemma-by-lemma account.

By Worker 5130:

- `Langlands.Global.Factors.HenniartCompositeFactorWeil`: Weil determinants and
  arithmetic pair L-factors are unchanged by pullback along a degree-preserving
  isomorphism of local Weil groups. The two fields may lie over different primes.
- `Langlands.Global.Factors.HenniartCompositeFactorCentral`: central characters of
  supercuspidal classes along `fieldPullback`, for basis and virtual classes.
- `Langlands.Global.Factors.HenniartCompositeFactorDeterminant`: the determinant
  clause at `K`. The candidate is moved to `F_v` by the Library's
  `Global.exists_geometric_completionReciprocity`. The central character is then
  pulled back, and the Weil determinant is transported.
- `Langlands.LocalFactor.NonabelianSystemFieldTransportExtension`,
  `...Virtual`, `...Reciprocity`, `...System`: transport of local-constant systems
  along `g : F ≅ E`. They transport finite extensions inside the common closure
  (`mapExtension`, `fieldEquiv`, `subgroupWeilEquiv`), virtual Weil classes with a
  change of carrier universe (`virtualMap`), reciprocity families
  (`transportFamily`, normalized by the norm and normalization relations), and
  assignments (`transportAssignment`). `isSystem_transportAssignment` shows the
  transport of a system is a system: the additive, Haar-scaling, induction,
  rank-one and normalization laws all hold.
- `Langlands.Global.Factors.HenniartCompositeFactorPair`: the pair-factor clause
  at `K`.

By Worker 5731:

- `Langlands.Representation.RankinSelberg.FieldTransport.{Group, Integrals,
  Factors, Padic}`: Jacquet–Piatetski-Shapiro–Shalika L- and epsilon-factors of
  pairs along a field isomorphism `f`, with the transported additive character and
  Haar measure.
- `Langlands.Global.Factors.UnitaryPairFactorTransport`: the supercuspidal pair L-
  and epsilon-factor relations on unitary virtual classes along
  `unitaryLatticeEquiv`.
- `Langlands.LocalFactor.NonabelianSystemFieldTransportPairEpsilon`: Weil-side
  arithmetic pair epsilon certificates along `g`, for a system on `E` and its
  transport to `F` (`isUnitaryPairEpsilonFactor_transport`).

## Dependencies

- `Langlands.Global.Factors.HenniartCompositeMapStatement`: the target,
  `henniartCompositeMap` and `henniartCompositeMap_apply`.
- `Langlands.Global.Factors.RelativeIsometryFactorStatement`: the clauses at
  `F_v` and the Weil-side factor predicates.
- `Langlands.Global.Factors.CompletionReciprocityTransport`: transport of
  geometric reciprocity candidates from `K` to `F_v`.
- `Langlands.LocalFactor.Abelian.SelfDualTransport`: self-dual measures along a
  field isomorphism.

## Reference

G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique*, Invent. Math. 139 (2000), §§3.7–3.8, page 451.
