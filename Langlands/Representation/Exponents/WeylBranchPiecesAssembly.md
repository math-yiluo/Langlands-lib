# Conditional assembly of the supported excess-multiplicity Weyl branch

Author: Worker 253. Coordinated with Worker 514, the first executor of the
proof task for
[`GLSupportedRegularMultiplicityBranchObstructionStatement`](SupportedRegularMultiplicityBranchObstructionStatement.md).

The module `Langlands.Representation.Exponents.WeylBranchPiecesAssembly`
proves

```lean
theorem Langlands.glSupportedRegularMultiplicityBranchObstruction_of_pieces
    (hP3 : GLGeometricPieceLiftingStatement.{uF, uM})
    (hP1 : GLGeometricExcessBranchStatement.{uF, uV, uW})
    (hP2 : GLProductLeviCuspidalLocalizationStatement.{uF, uV, uM})
    (hP2c : GLCuspidalInductionJacquetConstituentStatement.{uF, uV, uV}) :
    GLSupportedRegularMultiplicityBranchObstructionStatement.{uF, uV, uM, uW}
```

The four hypotheses are the Weyl-piece interfaces of
[`WeylBranchPiecesStatement`](WeylBranchPiecesStatement.md). This module
proves none of them, so here the target is proved only conditionally.
[`SupportedRegularMultiplicityBranchObstructionProof`](SupportedRegularMultiplicityBranchObstructionProof.md)
discharges the four hypotheses with published theorems and proves the target
unconditionally. The axioms are `propext`, `Classical.choice` and
`Quot.sound`.

The proof follows the branch-selection step of Silberger 1978, Lemma 5.6,
printed p.101. Silberger finds a Weyl element `s` with `τ ≅ s·τ` and
`s ∉ W_B`. Here `s` is constructed as a product `x g d` of three
geometric-lemma representatives. The almost-everywhere occurrence clause of
the target is proved for every middle unitary parameter `u`. The proof uses
no continuation argument, no relative regular comparison theorem, no head
theorem, no reflection theorem, no uniqueness of Langlands data and no
classification of square-integrable representations.

## Proof of the main theorem

Notation follows the target statement: `D = B.flatten Q`, `C = D.flatten R`,
`hSR : C = B.flatten S`, `ωB` and `vB` are the casts of `ω` and `v₀`,
`πt = |det|^t ⊗ π`, and `τ = fineTwist T B S ωB vB t`.

1. *Preliminaries.* `σ` and `π` are smooth because they are quotients of
   normalized inductions (`isSmooth_of_surjective`). Their real twists are
   then smooth. The facts used about `ωB` and `vB` come from the cast lemmas
   below. After that, `clear_value` makes `ωB` and `vB` opaque. Otherwise the
   elaborator tries to reduce the cast `hSR ▸ ω` by evaluating both shapes,
   and times out.
2. *Middle twist.* Let `t' k = t (parent_Q k)` on the blocks of `D` and
   `σt = |det|^{t'} ⊗ σ`. By `fineTwist_zero_zero`, `middleInduced T B Q σ`
   is the inner induction of `fineTwist T B Q σ 0 0`. The published
   `refinedLeviRealTwist` turns the given surjection onto `π` into a
   surjection from the inner induction of `fineTwist T B Q σ 0 t` onto `πt`.
   By `fineTwist_zero_left`, that inner induction is `middleInduced T B Q σt`.
3. *Excess branch (`hP1`).* Let `ρB` be the real twist of `ωB` by
   `k ↦ -vB k + t (parent_S k)`. It is irreducible and Levi-cuspidal, and
   `τ` is `ρB` pulled back to the refined subgroup. `hP1`, applied to `πt`
   and the given multiplicities, gives `x ∉ blockWeyl B`, minimal for
   `(B, B.flatten S)`, and a refinement `S'` with `ρB` a subquotient of the
   transport by `x` of the inner Jacquet module of `πt` along `S'`. Hence
   `ρ2 = transport x⁻¹ ρB` is a subquotient of that inner Jacquet module
   (`IsSubquotient.of_comp_symm`, `transport_inv`). `ρ2` is irreducible and
   cuspidal. For quasicuspidality, `x⁻¹` is minimal for
   `(B.flatten S, B.flatten S')` (`IsMinimalRepresentative.flatten_left`,
   `IsMinimalRepresentative.inv`), so `isLeviQuasicuspidal_transport`
   applies.
4. *Localization (`hP2`).* The Jacquet image of the surjection
   `middleInduced T B Q σt → πt` is surjective. Hence `ρ2` is a subquotient
   of the inner Jacquet module of `middleInduced T B Q σt`. `hP2` gives
   `g ∈ blockWeyl B`, minimal for `(D, B.flatten S')`, and a refinement `R'`
   of `D`. As in step 3, `ρ3 = transport g⁻¹ ρ2` is an irreducible cuspidal
   subquotient of the inner Jacquet module of `σt` along `R'`.
5. *Cuspidal constituent (`hP2c`).* Let `ω'` be the real twist of `ω` by
   `sC k = -v₀ k + t' (parent_R k)`. `refinedLeviRealTwist` at the middle
   level gives a surjection from the inner induction of the pullback of `ω'`
   onto `σt`. So `ρ3` is a subquotient of its inner Jacquet module along
   `R'`. `hP2c` gives `d ∈ blockWeyl D` and an equivalence
   `ρ3 ≃ transport d ω'`.
6. *The branch.* Let `w = x g d`. Its conjugacy witness `hw : C → C` comes
   from `conjugatesLevi_mul` and `hSR`. Then `w ∉ blockWeyl B`, because
   `g ∈ blockWeyl B` and `d ∈ blockWeyl D ≤ blockWeyl B`
   (`blockWeyl_flatten_le`, `mul_mul_not_mem_blockWeyl`).
   `transport_chain_equiv` gives `ρB ≃ transport (x g d) ω'`.
7. *Inverse-coordinate stabilizer.* The published unitary rigidity
   `glUnitaryWeylRealExponentRigidity`, clause 2, applies to `ω`, `ωB` and
   this equivalence. It gives
   `sB (blockIndex (B.flatten S) (w a)) = sC (blockIndex C a)` for every `a`.
   The parent of a fine block is the coarse block
   (`flattenBlockEquiv_symm_blockIndex`), and `vB` agrees with `v₀` at
   block indices. Hence `-v₀ + t` takes the same value at `w a` and at `a`,
   in block coordinates. Evaluating at `w⁻¹ a` gives the target clause.
8. *Occurrence at every unitary parameter.* Fix `u`. Twist the
   subquotient `transport d ω'` of the inner Jacquet module of `σt` by the
   middle complex character with exponent `z = i u - t'`. The surjection
   `normalizedTwistJacquetMap` and `leviComplexPowerRefinement` give
   `isSubquotient_innerJacquet_twist`. The twisted middle representation is
   `|det|^{i u} ⊗ σ` (`leviComplexPowerTwist_add`, `_ofReal`). The twisted
   constituent is `transport d` of the complex twist of `ω` by
   `refinedMixedAffine D R (-v₀) u`. This uses
   `transport_leviComplexPowerTwist` and `parent_blockEquiv`, which holds
   because `d ∈ blockWeyl D` preserves middle parents. `x g` is minimal for
   `(D, C)` (`isMinimalRepresentative_mul`). So `hP3` makes the transport by
   `x g` of that inner Jacquet module a subquotient of the opposite Jacquet
   module of the whole unitary middle induction. By transitivity and
   `transport_mul`, the transported candidate `transport w (...)` is such a
   subquotient. It is irreducible and admissible, which is
   `ComplexTwistFamilies.Occurs` by `occurs_iff`. Since this holds for all
   `u`, it holds almost everywhere.

## Helper results

Weyl combinatorics (namespace `Langlands.WeylBranchPieces`):

- `strictMono_blocks_iff`: increase on every block, in coordinate form.
- `IsMinimalRepresentative.inv`: if `w` is minimal for `(E, E')`, then `w⁻¹`
  is minimal for `(E', E)`.
- `IsMinimalRepresentative.flatten_left`: minimality persists when the source
  shape is refined.
- `isMinimalRepresentative_mul`: if `x` is minimal for `(B, B.flatten S)` and
  conjugates `B.flatten S'` onto `B.flatten S`, and `g ∈ blockWeyl B` is
  minimal for `(B.flatten Q, B.flatten S')`, then `x g` is minimal for
  `(B.flatten Q, B.flatten S)`.
- `mul_mul_not_mem_blockWeyl`: `x g h ∉ W` when `x ∉ W` and `g, h ∈ W`.
- `parent_blockEquiv`: a permutation in `blockWeyl D` that conjugates
  `D.flatten R` onto `D.flatten R'` preserves middle parents of fine blocks.

Representations:

- `topologicalRing_carrier`: the canonical topology makes `F` a topological
  ring.
- `refinedOppositeUnipotent_le_ker`: the refined opposite radical lies in the
  kernel of every coarse complex determinant character. Its blocks have
  determinant one (`lower_determinant_one`).
- `normalizedTwistJacquetMap`, `normalizedTwistJacquetMap_surjective`: the
  intertwiner, class to class, from the normalized refined opposite Jacquet
  module of `twist χ ρ` to the twist by `χ`, restricted to the refined
  subgroup, of the normalized refined opposite Jacquet module of `ρ`. Its
  underlying linear map is the published equivalence
  `Jacquet.twistCoinvariantsLinearEquiv` (`Jacquet/CharacterTwistEquiv`).
  This module proves only that it intertwines the normalized actions, and
  that it is surjective.
- `jacquetMap_surjective`, `normalizedRefinedOppositeJacquetMap_surjective`:
  the coinvariant map `Jacquet.map` of a surjective intertwiner is
  surjective. Hence so is the published normalized refined opposite Jacquet
  map.
- `isSubquotient_innerJacquet_of_surjective`,
  `isSubquotient_innerJacquet_twist`: subquotients of pulled-back inner
  Jacquet modules pull back along surjections. Under a coarse complex twist
  by `z` they move to the fine twist by `k ↦ z (parent k)`.
- `IsSubquotient.transport`, `transport_congr`, `transport_eq_self`,
  `transport_transport_inv`, `transport_chain_equiv`: transport preserves
  subquotients, and transports along a permutation, its inverse and a product
  compose as expected.
- `cast_isIrreducible`, `cast_isLeviCuspidal`, `cast_isUnitarizable`,
  `cast_param_blockIndex`: properties of the casts `h ▸ ω` and `h ▸ v` along a
  shape equality `h`.
- `fineTwist_zero_zero`, `fineTwist_zero_left`: `fineTwist` with zero fine
  offset is the untwisted, respectively the parent-twisted, flattened action.

The twist intertwiner is used only through its surjectivity, to move
subquotients. The equivalence and naturality laws of twisted Jacquet modules
are in the published modules `Jacquet/CharacterTwistEquiv` and
`Jacquet/NormalizedCharacterTwistEquiv`.
