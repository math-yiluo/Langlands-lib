# Points of a similitude group over products of coefficient rings

Author: Worker 13.

This internal construction concerns the named similitude point groups
`σ.Points S` of the published `Langlands.Shimura.Unitary.Adelic` (Worker 57).
Here `σ : AlgebraInvolution R A` is an involution of an `R`-algebra `A` with
`[Ring A]` over a commutative ring `R`, and `S` is a commutative `R`-algebra.
The module proves that these groups are functorial in the coefficient ring,
that continuous algebra isomorphisms of coefficients induce isomorphisms of
topological point groups, and that the points over a product `S × T` of
coefficient rings are the product of the points over `S` and over `T`. For the
rational finite adeles and a nonzero natural number `n`, combined with the
published ring splitting `ratFiniteAdelesSplit` of
`Langlands.Global.FiniteAdeleSplit`, this gives an isomorphism of topological
groups

`σ.FiniteAdelicPoints ≃ₜ* σ.Points (Π_{v ∣ n} ℚ_v) × σ.Points (PrimeToFiniteAdeles n)`,

written `GG(A_f) ≃ₜ* GG(ℚ_S) × GG(A_f^S)` with `S` the finite places whose
prime ideal contains `n`.

All declarations are in namespace `Langlands.Shimura.AlgebraInvolution`.

## Functoriality in the coefficient ring

Here `S`, `T` and `U` are commutative `R`-algebras. No topology is assumed
until `pointsContinuousEquiv`.

- `pointsMap_id` says that the published `pointsMap` along the identity
  algebra map is the identity homomorphism of `σ.Points S`.
  `pointsMap_comp f g` says that `pointsMap (g.comp f)` is the composite of
  `pointsMap g` and `pointsMap f`. The proofs reduce to the published
  `changeCoefficients_id` and `changeCoefficients_comp` on the algebra
  coordinate; the multiplier coordinate holds by definition.
  `pointsMap_apply_apply` is the pointwise form of `pointsMap_comp`.
- The existing `pointsMap_diagonalPoints f g` from
  `Langlands.Shimura.Coefficients.Algebraic` says that `pointsMap f` sends the published
  diagonal point `σ.diagonalPoints S g` of a similitude `g : σ.similitudes`
  to `σ.diagonalPoints T g`.
- `pointsEquiv f` takes an algebra isomorphism `f : S ≃ₐ[R] T` and is the group
  isomorphism `σ.Points S ≃* σ.Points T` with forward map `pointsMap f` and
  inverse `pointsMap f.symm` (`pointsEquiv_apply`,
  `pointsEquiv_symm_apply`). The inverse laws are `pointsMap_comp` and
  `pointsMap_id`.
- `pointsContinuousEquiv f` assumes topological rings `S` and `T`,
  `[Module.Finite R A]`, and takes a continuous algebra isomorphism
  `f : S ≃A[R] T`. It is `pointsEquiv` as an isomorphism of topological groups
  `σ.Points S ≃ₜ* σ.Points T`, with the published topologies on the point
  groups. Continuity in both directions is the published
  `continuous_pointsMap`. `pointsContinuousEquiv_apply` gives the forward map.

## Products of coefficient rings

Here `S` and `T` are commutative `R`-algebras and `S × T` carries Mathlib's
product algebra structure.

- `prodTensorEquiv S T` is the `R`-algebra isomorphism
  `(S × T) ⊗[R] A ≃ₐ[R] (S ⊗[R] A) × (T ⊗[R] A)`. It is the composite of
  Mathlib's `Algebra.TensorProduct.comm`, `Algebra.TensorProduct.prodRight` and
  `AlgEquiv.prodCongr` of `comm` on each factor.
  `prodTensorEquiv_apply` says that its two components are the published
  coefficient changes `changeCoefficients` along `AlgHom.fst` and
  `AlgHom.snd`; the proof is induction on tensors.
- `prodTensorEquiv_baseChange` says that it intertwines the published
  base-changed involution `σ.baseChange (S × T)` with the pair
  `σ.baseChange S`, `σ.baseChange T`. This is the published
  `changeCoefficients_involution`. `prodTensorEquiv_algebraMap` says that the
  scalar `c : S × T` goes to the pair of scalars `c.1` and `c.2`.
- `fstTensorSemilinear S T` and `sndTensorSemilinear S T` are
  `changeCoefficients` along the two projections, as additive maps that are
  semilinear over the ring projections `RingHom.fst S T` and `RingHom.snd S T`.
- `continuous_prodTensorEquiv` assumes topological rings `S` and `T` and
  `[Module.Finite R A]`. It says that `prodTensorEquiv S T` is continuous when
  each scalar extension carries Mathlib's `moduleTopology` over its coefficient
  ring and the target carries the product topology. Each component is the
  published `continuous_changeCoefficients` along a projection.
- `continuous_prodTensorEquiv_symm` assumes only topologies on `S` and `T`.
  It says that the inverse is continuous for the same topologies. The two
  semilinear components are surjective, and the ring projections are open
  quotient maps (Mathlib's `isOpenQuotientMap_fst` and `isOpenQuotientMap_snd`),
  so Mathlib's `IsModuleTopology.isQuotientMap_of_surjectiveₛₗ` makes both
  components quotient maps. Composed with the first component, the map
  `x ↦ prodTensorEquiv.symm (x, 0)` is scalar multiplication by the idempotent
  `(1, 0)`, which is continuous. Similarly for `(0, 1)` on the second factor.
  The inverse is the sum of these two partial inverses.
- `changeCoefficients_fst_prodTensorEquiv_symm` and
  `changeCoefficients_snd_prodTensorEquiv_symm` say that the coefficient
  changes along the projections recover the two components of a pair.

The splitting of points is built from a pair of similitudes.

- `prodPoint x y` takes similitudes `x` of `σ.baseChange S` and `y` of
  `σ.baseChange T`. It is the point of `σ.Points (S × T)` whose algebra unit
  is the image of the pair of units of `x` and `y` under
  `(prodTensorEquiv S T).symm` and Mathlib's `MulEquiv.prodUnits`, and whose
  multiplier unit is the pair of multiplier units. The similitude condition is
  checked after applying `prodTensorEquiv S T`, by
  `prodTensorEquiv_baseChange`, `prodTensorEquiv_algebraMap` and the two
  similitude conditions. `prodPoint_one` and `prodPoint_mul` say that it is
  multiplicative.
- `pointsMap_fst_prodPoint` and `pointsMap_snd_prodPoint` say that the
  coefficient changes along the projections recover `x` and `y`.
  `prodPoint_pointsMap` says that a point over `S × T` is rebuilt from its two
  coefficient changes.
- `prodPointsInv S T : σ.Points S × σ.Points T →* σ.Points (S × T)` is
  `prodPoint` as a group homomorphism.
- `prodPointsEquiv S T : σ.Points (S × T) ≃* σ.Points S × σ.Points T` is the
  group isomorphism whose components are `pointsMap (AlgHom.fst R S T)` and
  `pointsMap (AlgHom.snd R S T)` (`prodPointsEquiv_apply_fst`,
  `prodPointsEquiv_apply_snd`), with inverse `prodPointsInv S T`
  (`prodPointsEquiv_symm_apply`).
- `multiplier_prodPointsInv` says that the published multiplier
  `Points.multiplier` of the point built from a pair is the image of the pair
  of multipliers under `MulEquiv.prodUnits.symm`. It holds by definition.
- `continuous_prodPointsInv` assumes topologies on `S` and `T` and
  `[Module.Finite R A]`. It says that `prodPointsInv S T` is continuous for
  the published topologies on the point groups. The proof uses
  `continuous_prodTensorEquiv_symm`, Mathlib's `Continuous.units_map`, and the
  homeomorphism `Homeomorph.prodUnits` between the units of a product and the
  product of the units.
- `prodPointsContinuousEquiv S T` assumes topological rings `S` and `T` and
  `[Module.Finite R A]`. It is `prodPointsEquiv S T` as an isomorphism of
  topological groups `σ.Points (S × T) ≃ₜ* σ.Points S × σ.Points T`. Forward
  continuity is the published `continuous_pointsMap` along the two continuous
  projections, and inverse continuity is `continuous_prodPointsInv`.
  `prodPointsContinuousEquiv_apply` gives the forward map.

## The rational finite adelic points

Here `A` is a `ℚ`-algebra with `[Ring A]`, `σ : AlgebraInvolution ℚ A`, and
`n` is a natural number. The index type
`{v : FinitePlace ℚ // (n : 𝓞 ℚ) ∈ v.asIdeal}` is the set of finite places of
`ℚ` whose prime ideal contains `n`.

- `DividingPoints n` is an `abbrev` for the points
  `σ.Points (Π v : {v : FinitePlace ℚ // (n : 𝓞 ℚ) ∈ v.asIdeal}, FiniteCompletion ℚ v.1)`
  over the full product of the completions at these places.
- `PrimeToPoints n` is an `abbrev` for `σ.Points (PrimeToFiniteAdeles n)`, the
  points over the published prime-to-`n` finite adeles.

From here on `[Module.Finite ℚ A]` is assumed.

- `finiteAdelicPointsSplit n hn` takes `hn : n ≠ 0`. It is the isomorphism of
  topological groups
  `σ.FiniteAdelicPoints ≃ₜ* σ.DividingPoints n × σ.PrimeToPoints n`. It
  composes `pointsContinuousEquiv` of the published continuous `ℚ`-algebra
  isomorphism `ratFiniteAdelesSplit n hn` with `prodPointsContinuousEquiv`.
  The coefficient rings carry their published topological-ring and
  `ℚ`-algebra structures: the completions and their product on the first
  factor, and the published diagonal `ℚ`-algebra structure of
  `PrimeToFiniteAdeles n` on the second.
- `finiteAdelicPointsSplit_apply_fst` says that the first component of `g` is
  `pointsMap` of the composite of the first projection with
  `ratFiniteAdelesSplit n hn`. `finiteAdelicPointsSplit_apply_snd` says that
  the second component is `pointsMap` of the published restriction
  `primeToFiniteRestriction n`.
- `dividingLocalMap n v` is the continuous homomorphism
  `σ.DividingPoints n →ₜ* σ.Points (FiniteCompletion ℚ v.1)` of coefficient
  change along evaluation at the place `v` (Mathlib's `Pi.evalAlgHom`).
  `dividingLocalMap_finiteAdelicPointsSplit` says that its composite with the
  first component of the splitting is the published local evaluation
  `σ.finiteLocalMap v.1`. Both are `pointsMap` of the same algebra map, by
  `pointsMap_apply_apply`.
- `finiteAdelicPointsSplit_diagonal` says that the splitting sends the
  published diagonal image `σ.finiteAdelicDiagonal g` of a rational similitude
  `g` to the pair of diagonal points `σ.diagonalPoints _ g` in the two factors.
  This is `pointsMap_diagonalPoints` on each component.

## Sources and provenance

The construction is internal. It is derived from Mathlib's
`Algebra.TensorProduct.comm`, `Algebra.TensorProduct.prodRight`,
`MulEquiv.prodUnits`, `Homeomorph.prodUnits`, `Continuous.units_map`,
`Pi.evalAlgHom` and `IsModuleTopology.isQuotientMap_of_surjectiveₛₗ`. It also
uses the published `Langlands.Shimura.Unitary.Involution`
(`baseChange`, `changeCoefficients` and its lemmas),
`Langlands.Shimura.Unitary.Similitude` (`similitudes`, `mem_similitudes_iff`),
`Langlands.Shimura.Unitary.Adelic` (Worker 57: `Points`, `pointsMap`,
`continuous_changeCoefficients`, `continuous_pointsMap`, `diagonalPoints`,
`Points.multiplier`, `FiniteAdelicPoints`, `finiteAdelicDiagonal`,
`finiteEvaluation`, `finiteLocalMap`) and
`Langlands.Global.FiniteAdeleSplit` (`ratFiniteAdelesSplit`). The point groups
over products of coefficient rings and the subtype indexing of the places are
implementation choices, not attributed to the sources below.

The ring decomposition being transported is the one in M. Harris and
R. Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*,
Annals of Mathematics Studies 151, Princeton, 2001
(`harris-taylor-2001-geometry-cohomology-simple-shimura`), Chapter I, printed
p.20 (PDF p.28): "If S is a finite set of places of L we decompose
A_L = A_L^S × L_S where A_L^S denotes the adeles away from S and where
L_S = Π_{x ∈ S} L_x". Worker 13 read this page through text extraction of the
registered PDF. That passage states the ring decomposition only; the
corresponding splitting of the points of a group is the standard consequence,
proved here for the similitude point groups.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on GL(n)*
(`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`), Prop. 4.10
on printed p.311, lets the level `K(N)^{ℓ,p}` away from `ℓ` and `p` vary, with
`GG(A_f^{ℓ,p})`-equivariance. Taking levels in a group of finite adelic points
away from finitely many places requires the group splitting above. Harris's
passage is motivation only; no statement from it is formalized here.

The rational splitting is stated only over `ℚ` and only for the predicate
"the prime ideal contains `n`" with `n ≠ 0`. The module does not split any
compact open subgroup or level, does not identify the dividing places with
rational primes or their completions with `ℚ_p`, does not treat the infinite
places, and constructs no level tower, Shimura variety or cohomology. It does
not identify `σ` with Harris's inner form or `σ.Points` with Harris's group
`GG`.
