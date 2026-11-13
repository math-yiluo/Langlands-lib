# Rational torus points acting on rational root groups through root values

## Setting

Throughout, `k` and `L` are fields with `L / k` finite Galois (`FiniteDimensional k L`,
`IsGalois k L`). `G` is a group scheme over `Spec k` with `[IsAffineHom G.X.hom]`,
`[LocallyOfFiniteType G.X.hom]` and `[Smooth G.X.hom]`. `S` and `T` are commutative group
schemes over `Spec k`, with `f : S ⟶ T` and `j : T.toGrp ⟶ G`. The hypotheses used are the
following:

- `IsConnectedReductive G`;
- `j` is a maximal torus (`IsMaximalTorus j`);
- `S` is split (`IsSplitTorus S.toGrp`);
- `j` represents the centralizer of `f ≫ j` (`hcent`);
- the base change `T_L` is split.

`a` is a relative root of `f ≫ j`. `β` is an absolute root of `j_L`, and its Galois orbit is
the restriction fiber `rootRestrictionFiber k L j f a`. `U_a(k)` is `rootGroupPoints (f ≫ j) a`.
For a rational point `z ∈ T(k)`, the root value `rootOrbitCharacterValue k L j β z_L` is the
value of `β` at `z` viewed over `L`. It lies in the stabilizer field `rootOrbitField k L j β`.

The module rests on two Library formulas. Conjugation by `z` multiplies field coordinates by
the root value. On `U_a(k)` for non-multipliable `a` this is
`conjugation_rootPointLieEquiv_symm`, in the coordinates `rootPointLieEquiv` and
`rootOrbitFieldWeightSpaceLinearEquiv`. On the quotient `U_a(k)/U_{2a}(k)` for multipliable
`a` it is `quotientFieldEquiv_act`, in the coordinates `quotientFieldEquiv`.

## Non-multipliable roots

Here `a` has no multiple `n • a`, `n ≥ 2`, among the relative roots
(`RelativeRoot.HasNoHigherRoots`).

- `exists_rootPointLieEquiv_symm_eq`: every `g ∈ U_a(k)` is the root point with some field
  coordinate `x ∈ rootOrbitField k L j β`. Take `x` to be the inverse image of the
  coordinate of `g`.
- `commute_of_rootOrbitCharacterValue_eq_one`: if the root value of `z` at `β` is `1`, then
  `j(z)` commutes with every `g ∈ U_a(k)`. By the conjugation formula, conjugation by `j(z)`
  multiplies the coordinate of `g` by `1`.
- `exists_rootOrbitCharacterValue_conj_eq`: for `u, u' ∈ U_a(k)` with `u ≠ 1` and `u' ≠ 1`
  there is a nonzero `c ∈ rootOrbitField k L j β` with the following property. Every
  `z ∈ T(k)` with root value `c` at `β` satisfies `j(z) u j(z)⁻¹ = u'`. If `x` and `x'` are
  the coordinates of `u` and `u'`, they are nonzero, because coordinate `0` gives the point `1`.
  Take `c = x' x⁻¹`.

## Multipliable roots

Here `a ≠ 0`, and no multiple `n • a` with `n ≥ 3` is a relative root.

- `QuotientPackage k i a` is a structure that bundles the following data:
  - a representative `jU : U ⟶ G` of the root subgroup `U_a`, with `U` affine over the base;
  - a representative `j₂ : U₂ ⟶ G` of `U_{2a}`;
  - a Library `DoubleRootCommutatorPairing` `C` for these representatives, which contains the
    quotient `q : U → V`;
  - affineness of `V`.
- `nonempty_quotientPackage` shows that such a package exists. It uses the Library theorems
  `subgroup_has_smooth_closed_representative` and `nonempty_doubleRootCommutatorPairing`.
  Affineness of `V` comes from its vector-group structure.
- `QuotientPackage.exists_point`: every `g ∈ U_a(k)` is the image of a rational point of `U`.
- `QuotientPackage.mem_double_of_comp_q_eq_one` and
  `QuotientPackage.comp_q_eq_one_of_mem_double`: a rational point `y` of `U` maps into
  `U_{2a}(k)` exactly when `q(y) = 1`. This holds because `U_{2a}` represents the kernel of
  `q`.
- `exists_rootOrbitCharacterValue_conj_eq_mul`: let `u, u' ∈ U_a(k)` with `u, u' ∉ U_{2a}(k)`.
  There is a nonzero `c` such that every `z ∈ T(k)` with root value `c` at `β` satisfies
  `j(z) u j(z)⁻¹ = u' w` for some `w ∈ U_{2a}(k)`. Write `u` and `u'` as images of `y` and `y'`
  in `U(k)`, and let `x` and `x'` be the field coordinates of `q(y)` and `q(y')`. They are
  nonzero because `u, u' ∉ U_{2a}(k)`. Take `c = x' x⁻¹`. By `quotientFieldEquiv_act`, the
  torus action of `z` on `U` sends `y` to a point with the same image under `q` as `y'`. Then
  `w` is the image of `y'⁻¹ (z · y)`, which lies in `U_{2a}(k)` because `q` kills it.
- `commute_of_rootOrbitCharacterValue_eq_one_of_multipliable`: assume also that `2a` is a
  relative root. Let `β₂` be an absolute root whose Galois orbit is the restriction fiber of
  `2a`. If the root values of `z` at `β` and at `β₂` are both `1`, then `j(z)` commutes with
  every point of `U_a(k)`. The steps are as follows.
  1. `z` fixes every rational point of `V`, by `quotientFieldEquiv_act`.
  2. `z` fixes every rational point of `U₂`, by the non-multipliable case applied to `2a`.
  3. The Library's equivariant Heisenberg normal form (`nonempty_equivariantHeisenbergNormalForm`)
     gives an equivariant inclusion of `U₂` and an equivariant section of `q`. Every `y ∈ U(k)`
     is the product of the inclusion of some `w ∈ U₂(k)` and the section applied to `q(y)`.
  4. Both factors are fixed by steps 1 and 2, so `z` fixes `y`.

## Provenance

These are the root-group computations behind Kaletha and Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), §6.6 for quasi-split groups. There the elements of `Z(k)` act on the root
groups `U_a(k)`, and on `U_a(k)/U_{2a}(k)`, through the root values in field coordinates. The
Lean module is internal infrastructure for the proof of
`QuasiSplitAdjointSimpleRootTransitivityStatement`. It derives everything from the Library's
field-coordinate and Heisenberg normal-form theorems.
