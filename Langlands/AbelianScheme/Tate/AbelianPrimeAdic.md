# Prime-adic Tate modules of bundled abelian schemes

This module specializes the published construction
`Langlands.GroupScheme.Tate.PrimeAdic` to the bundled
`Langlands.AbelianScheme`. Its declarations are in
`Langlands.AbelianScheme.Tate.PrimeAdic`. The parameters are a scheme `S`,
an abelian scheme `A : AbelianScheme S`, a test scheme `T : Over S`,
and a natural number `p` with `Fact p.Prime`.

## Provenance

This is a derived interface to the actual constructions in
`Langlands.AbelianScheme.Basic` and
`Langlands.AbelianScheme.Tate.PrimeAdic`. It uses the underlying group scheme
`A.toGrp` and the actual homomorphism `AbelianScheme.groupHom f`; it introduces
no independent choice of torsion groups or maps. The accessor and additivity
pattern follows Worker 143's bundled integral Tate-module wrapper.

The mathematical source for the underlying construction is B. Edixhoven,
G. van der Geer and B. Moonen, *Abelian Varieties*, preliminary draft built
2012-02-08, Chapter X (10.1)–(10.3), printed pp.141–142, and (10.5), printed
p.143 (PDF pp.145–147). Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Those passages define the compatible prime-power torsion sequences, residue
scalar action, rational scalar extension, and maps induced by homomorphisms.
They were read directly for the underlying construction; their formulas have
also been checked against this specialization. No source-specific errata file
was present in the available Library.

The source uses separable-closure points for a prime different from the
characteristic, and separately discusses geometric points in the
characteristic prime. Here the elementary construction is made for arbitrary
test schemes and primes. The broader scope does not carry over the source's
rank, finite étaleness, or Galois-representation assertions.

## Actual torsion levels and their limit

`Level A T p n` is the additive group of actual sections of `A` killed by
`p ^ n`, namely `GroupScheme.Tate.Level A.toGrp T (p ^ n)`.
`kernelLevelEquiv A T p n` is an additive equivalence from sections of the
actual scheme-theoretic multiplication kernel to this level. It is the
published kernel equivalence with the group scheme specialized to `A.toGrp`.

For `h : n ≤ m`, `transition A T p h` is the map from level `m` to level `n`
given by multiplication by `p ^ m / p ^ n`. It specializes the divisibility
transition to `pow_dvd_pow p h`. In particular, successive transitions are
multiplication by `p`, as proved by the imported
`GroupScheme.Tate.PrimeAdic.toSection_transition_succ`.
`transition_smul` specializes the compatibility of these maps with the
`ℤ_[p]`-actions.

`Integral A T p` is the published coherent-sequence submodule:
its elements are families `x n : Level A T p n` satisfying
`transition A T p (Nat.le_succ n) (x (n + 1)) = x n` for every `n`.
Its abelian-group structure and `ℤ_[p]`-action are coordinatewise. On level
`n`, a scalar acts through `PadicInt.toZModPow n`. The topology is the
subspace topology from the product of discrete torsion levels, and the
inherited addition and negation are continuous.

`evaluation A T p n` is the linear coordinate projection.
`evaluation_smul` expresses the residue scalar formula,
`evaluation_transition` expresses successive coherence, and
`continuous_evaluation` gives continuity. These are direct specializations
of the corresponding core laws; the explicit scalar formula is
definitionally true.

For any `ℤ_[p]`-module `M`, `lift` constructs a linear map from a compatible
family of linear coordinate maps `f n : M →ₗ[ℤ_[p]] Level A T p n`.
`evaluation_lift` is its coordinate formula, proved by reflexivity.
`lift_unique` says that any linear map with those coordinates is this lift.
`continuous_lift` requires a topology on `M` and continuity of every `f n`,
and concludes continuity of the lift. These last two laws directly reuse the
core universal-property proofs.

`Rational A T p` is `ℚ_[p] ⊗[ℤ_[p]] Integral A T p` with its inherited
`ℚ_[p]`-vector-space structure. The source writes the tensor factors in the
opposite order. The ordering here is the core's scalar-extension convention
over the commutative ring `ℤ_[p]`; no separate tensor-order equivalence is
exported by this wrapper.

## Maps of abelian schemes

For `f : A ⟶ B`, `levelMapLinear T p f n` is the actual map on torsion
sections obtained by postcomposing with the underlying group-scheme
homomorphism. `map T p f` is its induced `ℤ_[p]`-linear map on the
integral modules. `evaluation_map` identifies its coordinates with
`levelMapLinear` by reflexivity.

`map_id`, `map_comp`, and `map_add` give preservation of identities,
composition, and addition of actual abelian-scheme homomorphisms. The
composition formula is
`map T p (f ≫ g) = (map T p g).comp (map T p f)`.
The identity and composition laws are direct core specializations.
For additivity, the abelian-scheme Hom group is the additive type tag on
the group-object Hom group. Thus `map_add` is precisely the core's
`map_mul` after unfolding `AbelianScheme.groupHom`.
`continuous_map` specializes continuity of the coordinatewise induced map.

`rationalMap T p f` is scalar extension of `map T p f` to `ℚ_[p]`.
`rationalMap_tmul` gives its value on a pure tensor:
`a ⊗ₜ x` is sent to `a ⊗ₜ map T p f x`.
`rationalMap_id`, `rationalMap_comp`, and `rationalMap_add` specialize the
core scalar-extension laws, with the same composition order and additive
type-tag conversion.

## Fibre and field-valued specializations

For an actual scheme morphism `s : U ⟶ S`,
`fibreLevelEquiv A p s n` identifies sections over `U` of the pullback of
the multiplication-by-`p ^ n` kernel with `Level A (Over.mk s) p n`.
This is the imported equivalence for the actual scheme pullback; its
exported type is an equivalence of types.

For `Ω : Type u` a field and `s : Spec Ω ⟶ S`,
`IntegralAt A p s` and `RationalAt A p s` take `T = Over.mk s`.
Choosing an algebraically closed field gives the geometric-point
specialization. No algebraic-closure assumption is built into these
definitions, and no comparison between different point fields is asserted.

The module supplies the bundled abelian-scheme interface to the prime-adic
construction. Finite étaleness, compactness, rank and freeness, joint scalar
continuity, rational topology, monodromy, Weil pairings, and base-change
comparison theorems remain separate obligations. The geometric conditions
stored by `AbelianScheme` are not used to infer any of these properties.
