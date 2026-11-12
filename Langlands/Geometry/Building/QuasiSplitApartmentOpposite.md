# The opposite-pair axiom for the descended quasi-split family

Author: Worker 4783.

Lean module: `Langlands.Geometry.Building.QuasiSplitApartmentOpposite`.

This internal unit belongs to task 8ffe0456. It proves the opposite-pair axiom V 5 over
the original field for the torus-then-field restriction of a Galois-fixed split
valuation, at every relative root `a` whose double `2a` is not a root. In the
classification of Kaletha–Prasad §2.6(c) (printed p. 96, PDF p. 127) these are the roots
of type R1 (neither divisible nor multipliable) and of type R3 (divisible, `a = 2b`). The
published constructor `torusFieldRestrictedValuationOfOriginalPointShifts` needs V 5
for all relative roots. Multipliable roots (type R2) are not treated here.

Notation. `k` is a field and `K/k` a field extension. `S` and `T` are commutative
group schemes, `G` is a group scheme, and `j : T.toGrp ⟶ G`. For `f : S ⟶ T`, the
composite `CommGroupScheme.groupHom f ≫ j` is the torus `S` acting through `T`. The
roots of `j` are `relativeRoots j`. Its rational root group at `χ` is
`rootGroupPoints j χ`, the rational points of `RelativeRoot.subgroup j χ`. In the
section on Galois descent, base changes to `K` are written `S_K`, `T_K`, `G_K`,
`j_K`, `t_K`, and `a_K` is the base change of a character `a` of `S`.

## Commutation of root groups

- `commute_of_no_strict_root_combinations`: let `T` be a split torus, `G` affine and
  smooth, and `i : T.toGrp ⟶ G`. Let `c, d` be nonzero characters such that no
  `n • c + m • d` with `n, m > 0` is zero or a root of `i`. Then points of the root
  groups `RelativeRoot.subgroup i c` and `RelativeRoot.subgroup i d` commute. This is
  the argument of the published `SplitPinning.commute_of_no_strict_root_combinations`,
  stated for an arbitrary split torus. The published
  `semigroupSubgroup_eq_bot_of_noAmbientWeights_without_realization` shows that the
  subgroup of the strict combinations is trivial. The published `semigroupCommutator`
  places the commutator in that subgroup.
- `NoStrictRootCombinations i c d` (definition): the hypothesis above, that no
  `n • c + m • d` with `n, m > 0` is zero or a root of `i`.
  `NoStrictRootCombinations.symm` swaps `c` and `d`.

## Root pairings

- `rootDatum_nsmul_sub_nsmul_notMem`: let `P` be a root datum with finitely many
  roots, and `αᵢ ≠ αⱼ` two roots with `αᵢ ≠ -αⱼ`. Suppose no `p αᵢ + q αⱼ`
  (`p, q > 0`) is a root and `αᵢ - αⱼ` is not a root. Then no `p αᵢ - q αⱼ`
  (`p, q > 0`) is zero or a root. Proof: Mathlib's
  `RootPairing.pairing_eq_zero_of_add_notMem_of_sub_notMem` makes the two roots
  orthogonal. The reflection in `αⱼ` then carries `p αᵢ - q αⱼ` to `p αᵢ + q αⱼ`,
  and its pairing with the coroot of `αⱼ` is `-2q ≠ 0`.

## Roots over one relative root

Let `S` be split, `f : S ⟶ T`, and let `β` be a nonzero character of `S` such that no
root `χ` of `j` has `f ≫ χ = n • β` with `n ≥ 2` (hypothesis `hhigh`). The fibre of
`β` is the set of roots `χ` of `j` with `f ≫ χ = β`.

- `semigroupIndivisibleRoots_preimage_eq_fiber`: the published selection
  `RelativeRoot.semigroupIndivisibleRoots` of indivisible roots over the positive
  multiples of `β` is exactly the fibre of `β`.
- `neg_mem_relativeRoots_of_isRootDatumOf`: if `P` is a root datum of `j`
  (`IsRootDatumOf j P`), the roots of `j` are closed under negation.
- `noStrictRootCombinations_fiber_pos`: two roots `χ, χ'` in the fibre satisfy
  `NoStrictRootCombinations j χ χ'`. A combination `n • χ + m • χ'` restricts to
  `(n + m) • β`.
- `noStrictRootCombinations_fiber_neg`: the same for `-χ` and `-χ'`.
- `noStrictRootCombinations_fiber_pos_neg`: suppose no root of `j` restricts to zero
  (hypothesis `hzero`). Then two distinct roots `χ ≠ χ'` in the fibre satisfy
  `NoStrictRootCombinations j χ (-χ')`. Proof: `χ + χ'` restricts to `2 • β`, and
  `χ - χ'` restricts to zero, so neither is a root. Also `χ ≠ -χ'`, because
  `2 • β ≠ 0`. Then `rootDatum_nsmul_sub_nsmul_notMem` applies.

## Separation and elementary helpers

- `list_ofFn_prod_mul_mul`: in a monoid, `∏ₗ (A l * B l * C l)` equals
  `(∏ A) * (∏ B) * (∏ C)` (ordered products over `Fin n`), provided `B l` commutes
  with `A m`, `C l` with `A m`, and `C l` with `B m` whenever `l ≠ m`.
- `withTop_eq_neg_of_add_coe_eq_zero`: in `WithTop ℝ`, `x + c = 0` gives `x = -c`.
- `normalizer_eq_one_of_mul_opposite_torusHom`: let `G` be affine, `S` split and
  `α ≠ 0` a character of `S`. Let `n` be a normalizer point of `j` whose value is
  `x * y`, where `x` and `y` are points of the root groups of `α` and `-α` for
  `groupHom f ≫ j`. Then `n = 1`. Proof: choose a cocharacter `ν` of `S` pairing
  positively with `α` (`IsSplitTorus.exists_pairing_eq_pos`). The two root groups lie
  in the opposite dynamic unipotent subgroups of the cocharacter `ν ≫ f` of `T`
  (`RelativeRoot.subgroup_le_dynamicUnipotent`). The published
  `normalizer_eq_one_of_unipotent_product` concludes.
- `IsOppositeFactorPair.inv_conj_mem`: let `i : S.toGrp ⟶ G` be a monomorphism with
  `S` split, `α ≠ 0`, and `x ≠ 1` a point of the root group of `α`. Let `(p₁, p₂)` be
  an opposite factor pair of `x`, and `n = p₁ * x * p₂` its normalizer point. Then
  `n⁻¹ y n` lies in the root group of `α` for every point `y` of the root group of
  `-α`. Proof: `n` acts on characters by sending `α` to `-α` (published
  `IsOppositeFactorPair.weylAction_eq_neg`), and `RelativeRoot.normalizer_conj_mem`
  applies to `n⁻¹`.

## The opposite pair over a fibre

In this section `G` is affine and smooth, `j` is a monomorphism, `S` and `T` are
split, `hE` gives opposite factor pairs for `j`, and `φ` is a valuation of the root
datum of `j` (`IsRootDatumValuation j φ`). The published
`torusRestrictedRootFunctionFamily hS hT hE hφ f` is the torus restriction of `φ`
along `f`. Let `α` be a root of `groupHom f ≫ j` satisfying `hhigh`. Let
`a : Fin n → characterLattice T` be an injective enumeration of the fibre of `α`, and
let `X l` be points of the root groups of `a l`. Their ordered product is the
published `RelativeRoot.rootPointsProduct j a _ X`.

- `torusRestrictedRootFunctionFamily_eq_of_coordinates`: if `n > 0` and every
  `φ (a l) (X l)` equals one real number `c`, then the restricted value of the
  product at `α` is `c`. Proof: the published
  `mem_torusRestrictedRootDepthSubgroup_iff_coordinate_bounds`, with all
  multiplicities `1`, and `le_torusRestrictedRootFunctionFamily_iff`.
- `list_ofFn_prod_mem_rootGroupPoints_comp`: an ordered product of points of root
  groups of roots in the fibre of `β ≠ 0` is a point of the root group of `β` for
  `groupHom f ≫ j`. This uses the published
  `RelativeRoot.subgroup_comp_torusHom_carrier_eq_iSup`.
- `torusRestrictedRootFunctionFamily_neg_eq_of_fiber`: suppose also that `P` is a
  finite root datum of `j`, that no root of `j` restricts to zero (`hzero`), that
  `groupHom f ≫ j` is a monomorphism, and that every `φ (a l) (X l)` equals `c`. Let
  `g` be the product of the `X l`, and `g', g''` points of the root group of `-α` for
  `groupHom f ≫ j`. If `g' * g * g''` normalizes both `j` and `groupHom f ≫ j`, then
  the restricted value of `g'` at `-α` is `-c`.

  Proof. Every `X l` is nontrivial, since its value is finite. Choose upper opposite
  factor pairs `(Y l, Z l)` of `X l` by `hE`. The upper axiom V 5 gives
  `φ (-(a l)) (Y l) = -c`. For `l ≠ m`, the commutation lemmas make `X l`, `Y l`, `Z l`
  commute with `X m`, `Y m`, `Z m` as needed. So `N' = ∏ₗ (Y l * X l * Z l)` equals
  `Y' * g * Z'`, with `Y' = ∏ Y l` and `Z' = ∏ Z l`. `N'` normalizes `j`, and `Y'`,
  `Z'` lie in the root group of `-α`. The product `g` is not `1`, by uniqueness of
  coordinates (published
  `RelativeRoot.mem_subgroup_comp_torusHom_iff_existsUnique_rootPointsProduct`). Put
  `n = g' * g * g''`. Then
  `n⁻¹ * N' = (n⁻¹ * (g' * Y'⁻¹)⁻¹ * n) * (g''⁻¹ * Z')`. By
  `IsOppositeFactorPair.inv_conj_mem` for the pair `(g', g'')`, the first factor lies
  in the root group of `α`; the second lies in that of `-α`. Since `n⁻¹ * N'`
  normalizes `j`, `normalizer_eq_one_of_mul_opposite_torusHom` gives `n⁻¹ * N' = 1`.
  The published `RelativeRoot.eq_one_of_mem_subgroup_of_mem_opposite` then gives
  `g' = Y'`. Finally, `Y'` is the product of the coordinates `Y l` over the fibre of
  `-α`, all of value `-c`. By `torusRestrictedRootFunctionFamily_eq_of_coordinates`,
  its restricted value is `-c`.

## Galois descent

Let `K/k` be a field extension, `t : S ⟶ T`, and `jT : T.toGrp ⟶ G` with `G` affine
and smooth and `j_K` a monomorphism. The published coefficient action is
`rationalConjugate k K G σ` on points, `characterLattice.galoisRepresentation` on
characters of `T_K`, and `RootFunctionFamily.galoisAction` on root function
families.

- `rationalConjugate_fiber_coordinate`: let `S` and `T_K` be split, `a_K α ≠ 0` with
  `hhigh` for `t_K`, and `a`, `X` an enumeration of the fibre of `a_K α` with
  coordinates as above. Suppose the product of the `X l` is the scalar extension
  `rationalExtend k K G g` of an original point. If `σ` carries `a l` to `a m`, then
  `σ` carries `X l` to `X m`. Proof: `σ` permutes the fibre
  (`mem_roots_galois_iff`, `characterLattice.galoisRepresentation_baseChange`) and the
  root groups (`RelativeRoot.rationalConjugate_mem_subgroup_iff`). The conjugated
  coordinates, reindexed along this permutation, commute pairwise. Their product is
  therefore again the scalar extension of `g` (`Equiv.Perm.ofFn_comp_perm`,
  `List.Perm.prod_eq'`, `rationalConjugate_rationalExtend`). Uniqueness of
  coordinates concludes.
- `fiber_coordinate_value_eq_of_galois`: if moreover `φ` is fixed by every
  `RootFunctionFamily.galoisAction σ`, then `φ (a m) (X m) = φ (a l) (X l)`. This uses
  `RootFunctionFamily.galoisAction_apply_conjugate`.
- `torusFieldRestrictedRootFunctionFamily_opposite_of_two_not_mem` (main theorem):
  assume
  - `i : S.toGrp ⟶ G` and `groupHom t_K ≫ j_K` are monomorphisms, `S` and `T_K` are
    split, and `groupHom t_K ≫ j_K` equals the base change of `i` (`hfactor`);
  - `φ` is a valuation of the root datum of `j_K` with opposite factor pairs `hE`,
    fixed by every `RootFunctionFamily.galoisAction σ` (`hfix`);
  - `P` is a finite root datum of `j_K`, and no root of `j_K` restricts to zero along
    `t_K` (`hzero`);
  - every rational normalizer point of `i` normalizes `jT` (`hnorm`), and `i` has
    opposite factor pairs (`hEbase`);
  - `a` is a root of `i` with `2 • a` not a root, and any two roots of `j_K` in the
    fibre of `a_K a` are related by some `σ` (`horbit`).

  Let `g ≠ 1` be a point of the root group of `a`, and `g', g''` points of the root
  group of `-a`, with `g' * g * g''` normalizing `i`. Then the published
  `torusFieldRestrictedRootFunctionFamily` of `φ` along `t_K` satisfies
  `ψ (-a) g' + ψ a g = 0`.

  Proof. The published `HasOppositeFactorPairs.hasNoHigherRoots_of_two_not_mem`
  excludes roots over `n • a` for `n ≥ 2`. Base change (`mem_roots_baseChange_iff`)
  transfers this to `hhigh` for `a_K a`. The fibre is finite since `P` has finitely
  many roots, so it has an injective enumeration. The scalar extension of `g` has
  coordinates `X l` over the fibre, and some `X l₀` is nontrivial because
  `rationalExtend` is injective. Let `c` be the value of `X l₀`. By `horbit` and
  `fiber_coordinate_value_eq_of_galois`, all coordinates have value `c`. The scalar
  extension of `g' * g * g''` normalizes `j_K` (by `hnorm`) and `i_K`
  (`normalizerPointsFieldExtend`). So `torusRestrictedRootFunctionFamily_neg_eq_of_fiber`
  gives the value `-c` at `-a` for `g'`, and
  `torusRestrictedRootFunctionFamily_eq_of_coordinates` gives the value `c` at `a`
  for `g`. The field restriction evaluates on scalar extensions
  (`RootFunctionFamily.fieldRestrict_apply`).

## Provenance

The statement is axiom V 5 of Kaletha–Prasad, Definition 6.1.2, for the valuation of
the relative root datum of a quasi-split group. Kaletha–Prasad prove it in
Proposition 6.1.19 (printed pp. 206–207, PDF pp. 237–238), by reduction to rank-one
subgroups. For a root of type R1 this is the restriction of scalars of `SL₂`, with Lemma
6.1.1. For a root of type R3 (`a = 2b`) they treat `b` and `2b` together in the `SU₃` case.
The valuation itself is Construction 6.1.17 (printed pp. 205–206, PDF pp. 236–237): for
R1 roots, `U_a(k) ≅ k_ã` and `φ_a` is the valuation of the coordinate. The Lean theorem
covers both types R1 and R3 by one argument, since it only uses that `2a` is not a root.

The Lean proof takes a different, internal route. It does not use the restriction of
scalars. Instead it uses the published torus-then-field restriction of a Galois-fixed
upper valuation. The roots over `a` are pairwise orthogonal, and by the hypothesis
`horbit` they form one Galois orbit. So the upper opposite pairs of the Galois-conjugate
coordinates commute, and their product is the opposite pair of `g` over `K`. Separation
by opposite dynamic unipotent subgroups identifies it with `(g', g'')`. The generic lemmas
(commutation, root pairing, separation, list products) are internal helpers derived
from published Library results and Mathlib.

## Scope

- Only relative roots `a` with `2a` not a root (types R1 and R3) are treated. V 5 at
  multipliable roots (type R2) is not proved here.
- The hypotheses `horbit`, `hzero` and `hnorm` are explicit premises, left to the caller.
  They are not automatic for an arbitrary extension `K/k`. In the intended application,
  `K/k` is a finite Galois extension splitting `T` and `jT` represents the full
  centralizer of the maximal split torus `i`. There the published
  `rootOrbit_eq_restrictionFiber_of_torusCentralizer` (which assumes `K/k` finite
  Galois) and `root_restrict_ne_zero_of_torusCentralizer` supply `horbit` and `hzero`, and
  `hnorm` holds because normalizer points of `i` normalize its full centralizer.
- This unit does not construct the quasi-split apartment, and it does not prove the
  task target.
