# The commutator pairing of a multipliable relative-root subgroup

This module applies the commutator pairing `CommutatorDescent.pairing` of
`GroupScheme/CentralIsogeny/CommutatorPairing` to relative root subgroups. The setting is
a smooth affine group scheme `G` over a field `k`, a split torus `S` with a homomorphism
`i : S ⟶ G` (`hS : IsSplitTorus S.toGrp`), and a nonzero character `a` of `S`. No positive
multiple `n • a` with `n ≥ 3` is a relative root of `i`
(`hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i`). We are given represented root
subgroups: `j : U ⟶ G` represents the intrinsic root functor `subgroup i a`
(`hj : (subgroup i a).IsRepresentedBy j`), and `j₂ : U₂ ⟶ G` represents `subgroup i (2 • a)`
(`hj₂`). The module does not assume that `2 • a` is a relative root.

The result has the following meaning. The quotient `V = U / U₂` carries a vector structure
on which `S` acts through `a`. The commutator `(g, h) ↦ g h g⁻¹ h⁻¹` of `U` descends to a
biadditive, alternating, `S`-equivariant pairing `V × V ⟶ U₂`.

## The structure

`DoubleRootCommutatorPairing i a hj hj₂` (structure) packages:

- `V : GroupScheme (Spec k)`, a homomorphism `q : U ⟶ V`, and an automorphic action
  `action` of `S` on `V`;
- `isFppfQuotient`: `q` is an fppf quotient of `U` by the preimage
  `(subgroup i (2 • a)).comap j` of the doubled root functor;
- `quasiCompact`: the underlying scheme map of `q` is quasi-compact;
- `weightVectorStructure : HasUniqueWeightVectorStructure action a`. In the sense of
  `GroupScheme/Rational/WeightSemigroupStatement`, `V` has natural vector coordinates on
  which `S` acts through the single character `a`, and scalar multiplication does not
  depend on the choice of such coordinates;
- `act_comp`: `q` intertwines `subgroupAction i a j hj` (the conjugation action of `S`
  on `U` transported through `j`) with `action`;
- `pairing : V.X ⊗ V.X ⟶ U₂.X`;
- `lift_pairing`: on `T`-points `g, h` of `U`, the composite
  `(lift (q g) (q h) ≫ pairing) ≫ j₂` equals the commutator
  `(j g)(j h)(j g)⁻¹(j h)⁻¹` in `G`;
- `lift_mul_pairing`, `lift_pairing_mul`: the pairing is multiplicative in each argument
  on all `T`-points of `V`;
- `lift_self_pairing`: `lift x x ≫ pairing = 1`;
- `lift_pairing_act`: the pairing intertwines the diagonal action of `S` on `V × V` with
  the conjugation action `subgroupAction i (2 • a) j₂ hj₂` on `U₂`.

## Auxiliary statements

- `commute_of_hasUniqueWeightVectorStructure hc T x y`: if `V` has vector coordinates of
  some weight, any two `T`-points of `V` commute. The coordinates are a multiplicative
  bijection onto an additive group.
- `commute_comap_double_of_noHigherRoots hS i ha hhigh hj T x y hx`: a `T`-point `x` of `U`
  in the preimage of `subgroup i (2 • a)` commutes with every `T`-point `y` of `U`. The
  proof reads the published `double_subgroup_commute_of_noHigherRoots` (module
  `GroupScheme/Rational/RootSubgroupCentrality`) through the monomorphism `j`.

## Existence

`nonempty_doubleRootCommutatorPairing hS i ha hhigh hj hj₂` proves
`Nonempty (DoubleRootCommutatorPairing i a hj hj₂)` under the instance hypotheses
`[IsAffineHom G.X.hom] [Smooth G.X.hom] [QuasiCompact U.X.hom]`.
`doubleRootCommutatorPairing` is a chosen instance (via `Classical.choice`).

The proof proceeds as follows.

1. The published `cyclicRootFunctorComparison` identifies the first term
   `weightFiltration b a 1` of the cyclic weight filtration of the conjugation action `b`
   with `subgroup i a`. So `j` represents that term.
2. The published `cyclicWeightFiltration` (CGP 3.3.8) at `r = 1` gives `V`, `q`, an action
   `c` on `V`, an action `d` on `U`, and four facts. First, `q` is an fppf quotient by the
   preimage of `weightFiltration b a 2`. Second, `c` has unique weight-vector structure of
   weight `1 • a`. Third, `j` intertwines `d` with conjugation. Fourth, `q` intertwines
   `d` with `c`.
3. By `hhigh`, no multiple `n • a` with `n ≥ 3` lies in the weight support of `b`
   (`mem_actionWeightSupport_conjugation_iff`). Hence the published
   `weightFiltration_two_eq_double` and `cyclicRootFunctorComparison` for `2 • a` identify
   `weightFiltration b a 2` with `subgroup i (2 • a)`. This gives `isFppfQuotient`.
   `act_comp` follows by comparing `d` with `subgroupAction i a j hj` after `j`.
4. The scheme map `q` is flat and surjective (from the fppf quotient). It is quasi-compact
   because `U → Spec k` is quasi-compact and `V` is separated over the field
   (`fieldSeparated`).
5. The fppf quotient identifies the range of the actual kernel inclusion `kernelι q` with
   `(subgroup i (2 • a)).comap j`. By `commute_comap_double_of_noHigherRoots` and
   `isCentral_kernelι_of_commute`, this kernel is central.
6. The published `double_subgroup_le_of_cyclicComparison` gives
   `subgroup i (2 • a) ≤ subgroup i a`. So `j₂` factors through `j` by
   `factorHom`, and the factor represents the preimage
   (`SubgroupFunctor.IsRepresentedBy.factor`), that is, the range of `kernelι q`.
7. The pairing is `CommutatorDescent.pairing q hπ hV hκ`. Here `hπ` is the centrality from
   step 5, `hV` is `commute_of_hasUniqueWeightVectorStructure`, and `hκ` is the
   representation from step 6. Its multiplicativity, alternation and equivariance are the
   corresponding properties of `CommutatorDescent.pairing`. Equivariance uses the
   compatibility of the two `subgroupAction`s with the factor of `j₂` through `j`.
   `lift_pairing` composes the published `CommutatorDescent.lift_pairing` with `j` and
   uses that `j` is multiplicative.

## Provenance

The construction is internal. Its literature input is the cyclic weight filtration of
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, Proposition 3.3.8. This enters only
through the published Library theorem `cyclicWeightFiltration`. The resulting pairing
is the scheme-theoretic form of the commutator description of a multipliable root group:
`U_a / U_{2a}` is a vector group of weight `a`, and its commutator pairing takes values in
`U_{2a}`. Compare Kaletha–Prasad, *Bruhat–Tits theory: a new approach*, §2.9 and
Construction 6.1.17. This module proves only the existence of the pairing and the
properties listed above. It does not identify the pairing with a hermitian or
trace form, prove bilinearity over `k` in coordinates, or construct the coordinates of
`RootUnitaryCoordinates`.
