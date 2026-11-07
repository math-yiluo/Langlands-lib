# Heisenberg normal forms equivariant for a torus fixing the split torus

The published module `GroupScheme/Rational/RootHeisenbergNormalForm` puts a multipliable
relative root group into normal form. Let `U = U_a`, `U₂ = U_{2a}` and `V = U / U₂`. The
normal form is a section `sec : V ⟶ U` of schemes, equivariant for the split torus `S`, with
group law `sec(x) sec(y) = β(x, y) · sec(x y)`. This module adds equivariance for a second
group `D`. The group `D` acts on `G` by an automorphic action that fixes every point of the
image of `S`. If `D` is a torus and the conjugation action of `S` factors through a
homomorphism `S ⟶ D`, the section can be chosen `D`-equivariant as well. The cocycle `β` and
the commutator pairing are then `D`-equivariant. The intended case is
`D = Z_G(S)`, acting by conjugation, when this centralizer is a torus. This module does not
treat that case.

Provenance: the module is internal. It combines the published modules
`RootHeisenbergNormalForm`, `TorusEquivariantSection` (`IsTorus.exists_equivariantSection`),
`RootSubgroupCentralizerAction` (`rootActionOfFixesTorus`, the action on a root group of an
action fixing the torus), `FppfQuotientAction` (`IsFppfQuotient.action`, actions on
fppf quotients) and `VectorActionWeightCommuting` (`isLinearVectorCoordinates_of_commute`).
The existence proof follows the published proof of `nonempty_heisenbergNormalForm`, with the
split-torus equivariant section replaced by the torus one.

All declarations live in namespace `Langlands.GroupScheme.RelativeRoot`.

## Setting

`k` is a field and `S` a commutative group scheme over `Spec k` with `i : S.toGrp ⟶ G`. `D`
is a group scheme over `Spec k` and `b : AutomorphicAction D G` an action. The hypothesis
`hfix` states `b.act z (t ≫ i) = t ≫ i` for every test scheme `T` and points `z` of `D` and
`t` of `S`. Then `rootActionOfFixesTorus b i hfix a j hj` is the induced action of `D` on a
represented root group `j : U ⟶ G` (published), with
`rootActionOfFixesTorus_act_comp : (z · g) ≫ j = b.act z (g ≫ j)`.

Some statements assume that the action of `S` factors through `s : S.toGrp ⟶ D`. This is the
hypothesis `hs : b.act (t ≫ s) g = (t ≫ i) · g · (t ≫ i)⁻¹` for all points `t` of `S` and
`g` of `G`.

## Actions on root groups (section `Actions`)

- `rootActionOfFixesTorus_commute`: the action of `D` on `U_a` commutes with the action of
  `S` by conjugation (`subgroupAction i a j hj`).
- `subgroupAction_eq_rootActionOfFixesTorus s hs`: under `hs`, the action of a point `t` of
  `S` on `U_a` equals the action of `t ≫ s`.
- `isLinearVectorCoordinates_rootActionOfFixesTorus`. Assume `D` and `U_a` are affine over
  `Spec k`, `S` is a split torus, `a ≠ 0`, and `e` are weight vector coordinates of weight
  `a` on `U_a`. Then the action of `D` is linear in `e`.

## Actions on the quotient (namespace `DoubleRootCommutatorPairing`)

Here `C : DoubleRootCommutatorPairing i a hj hj₂` is the published quotient datum: the
quotient `C.q : U ⟶ C.V` by `U₂`, the action `C.action` of `S` on `C.V`, and the commutator
pairing `C.pairing`.

- `rootActionOfFixesTorus_isStable_double`: the action of `D` on `U_a` preserves the
  preimage of the doubled root functor.
- `torusQuotientAction C b hfix`: the induced action of `D` on `C.V`, by the published
  `IsFppfQuotient.action`. `torusQuotientAction_act_comp`:
  `z · (g ≫ C.q) = (z · g) ≫ C.q`.
- `hom_ext_of_local_lift`: two maps out of a test scheme `T` agree if they agree after
  every refinement on which a given point of `C.V` lifts to `U_a` (published
  `hom_ext_of_local_quotient_lift`).
- `torusQuotientAction_commute`: the actions of `D` and `S` on `C.V` commute.
- `action_eq_torusQuotientAction s hs`: under `hs`,
  `C.action.act t x = (torusQuotientAction C b hfix).act (t ≫ s) x`.
- `isLinearVectorCoordinates_torusQuotientAction`. Assume `D` and `C.V` are affine over
  `Spec k`, `S` is split, `a ≠ 0`, and `e` are weight vector coordinates of weight `a` for
  `C.action`. Then the action of `D` on `C.V` is linear in `e`.

## The equivariant normal form (section `NormalForm`)

- `EquivariantHeisenbergNormalForm C b hfix`: a structure extending the published
  `HeisenbergNormalForm C` by the field `act_sec_torus`. It states
  `z · (x ≫ sec) = (z · x) ≫ sec` for every test scheme `T`, point `z` of `D` and point `x`
  of `C.V`. The action on the left is the one on `U_a`, the one on the right is
  `torusQuotientAction`.
- `act_inclusion_torus`: the inclusion `U₂ ⟶ U_a` intertwines the actions of `D`.
- `cocycle_act_torus`: `β(z · x, z · y) = z · β(x, y)`, with `D` acting on `U₂` by
  `rootActionOfFixesTorus b i hfix (2 • a) j₂ hj₂`.
- `pairing_act_torus N`: the same identity for the commutator pairing `C.pairing`. The
  normal form `N` is an explicit argument, used only in the proof.
- `nonempty_equivariantHeisenbergNormalForm`. Assume `G` and `U_a` are affine over
  `Spec k`, `G` is smooth, `S` is a split torus, `a ≠ 0`, no `n • a` with `n ≥ 3` is a
  relative root, `D` is a torus (`IsTorus D`), and `hfix` and `hs` hold. Then
  `EquivariantHeisenbergNormalForm C b hfix` is nonempty.
- `equivariantHeisenbergNormalForm`: a chosen one, by `Classical.choice`.

## Proofs

**Actions.** The commutation and factorization identities are checked after composing with
the monomorphism `j`. There, `hfix`, `hs` and the action laws reduce them to identities in
the group of points of `G`. Linearity is the published `isLinearVectorCoordinates_of_commute`
applied to the commuting actions. On the quotient, every point lifts to `U_a` fppf-locally.
So the identities on `C.V` follow from those on `U_a` and the compatibilities
`C.act_comp` and `torusQuotientAction_act_comp`.

**Equivariance of the cocycle and the pairing.** The proof is that of the published
`cocycle_act`, with `act_inclusion_torus` and `act_sec_torus` in place of their `S`
versions. The pairing is `β(x, y) β(y, x)⁻¹` (published `pairing_eq`).

**Existence.** The setup follows the published proof of `nonempty_heisenbergNormalForm`.
It provides the inclusion `n : U₂ ⟶ U_a`, weight vector coordinates `e'` of weight `2 • a`
on `U₂`, a scheme section `s₀` of `C.q`, and the kernel description of `C.q`. The torus `D`
is affine (published `SplittingAssembly.isAffine_of_isTorus`). So the action of `D` on `U₂`
is linear in `e'` by `isLinearVectorCoordinates_rootActionOfFixesTorus`. The inclusion
intertwines the actions of `D` (checked after `j`). Then `IsTorus.exists_equivariantSection`
gives a `D`-equivariant section `σ` of `C.q`. Its normalization `σ' = σ · σ(1)⁻¹` is still
`D`-equivariant, since `D` fixes the identity of `C.V`. By
`subgroupAction_eq_rootActionOfFixesTorus` and `action_eq_torusQuotientAction`, `σ'` is also
`S`-equivariant. The cocycle is the factorization through `n` of
`σ'(x) σ'(y) σ'(x y)⁻¹` on the universal pair, as in the published proof.

## Scope

The module does not prove that `Z_G(S)` is a torus, nor the hypotheses `hfix` and `hs` for
it. It does not compare the cocycle with the quadratic unitary law of Kaletha–Prasad (2.7.2).
