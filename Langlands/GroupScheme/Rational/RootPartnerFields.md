# Fields of an absolute root and of its sum with an orbit partner

This module applies two earlier modules to the actual roots of a torus `j : T ⟶ G` that
splits over a finite Galois extension `L / k`:

- `Langlands.GroupScheme.Reductive.RootDatumOrbitPartners` (namespace
  `RootPairing.OrbitPartner`), the combinatorics of orbit partners in a root datum with a
  group action;
- `Langlands.Algebra.QuadraticFixedFields`, index-two Galois subgroups and separable
  quadratic intermediate extensions.

Let `β` be an actual root of `T_L` and `β' = σ • β ≠ β` a member of its Galois orbit with
`μ = β + β'` also a root. Assume that no actual root has zero Galois orbit sum. Then the
field of `μ` lies in the field of `β`, and the field of `β` is a separable quadratic
extension of it. Every Galois element moving `β` to `β'` acts on the field of `β` as the
conjugation of this quadratic extension. These are the field data `E ⊇ L₀` of a multipliable
relative root `a` of a quasi-split group, with `E = rootOrbitField β` and
`L₀ = rootOrbitField μ`. The unitary coordinates of the root group `U_a` are taken over
these fields.

Provenance: internal. The statements are standard. The proofs combine the Library's Galois
action on actual roots and root data with the two modules above.

## Setting

All declarations live in namespace `Langlands.GroupScheme.RootPartnerFields`. The variables
are fields `k L : Type u` with `[Algebra k L]`, a commutative group scheme `T` and an affine
group scheme `G` over `Spec k`, and `j : T.toGrp ⟶ G`. The base changes to `L` are written
`T_L`, `G_L` and `j_L`. The Library's `rootsGaloisAction` is a local instance: `σ • β` is
the Galois transport of the character `β` (`rootsGaloisAction_coe`). `rootOrbitField k L j β`
is the Library's field of `β`, the fixed field of the stabilizer of `β`.

- `IsRootPartner k L j β β'` (a `Prop`-valued `def`) for actual roots `β β'` of `j_L` holds
  when some `σ : L ≃ₐ[k] L` has `σ • β = β'`, `β' ≠ β`, and `β.val + β'.val` is an actual
  root of `j_L`.
- `fixingSubgroup_rootOrbitField` (needs `[FiniteDimensional k L]`): the fixing subgroup of
  `rootOrbitField k L j β` is `MulAction.stabilizer (L ≃ₐ[k] L) β`. This is
  `IntermediateField.fixingSubgroup_fixedField`.

## Root data

Section `RootDatum` assumes `[LocallyOfFiniteType G.X.hom]` and the following:

- `hT`: `T_L` is a split torus;
- `hj`: `j_L` is a closed immersion;
- `hP : IsRootDatumOf j_L P`, for a root datum `P` indexed by a type `J` on the character
  and cocharacter lattices of `T_L`.

Write `ρ` for `IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k L j hT hj hP`, the
Library's Galois action on `P`.

- `root_mem_roots`: each `P.root m` is an actual root.
- `exists_root_eq`: each actual root `β` is `P.root p` for some `p : J`.
- `root_smul`: `P.root (ρ σ • p)` is the Galois transport of `P.root p`.
  This is `IsRootDatumOf.galoisRootIndexEquiv_root`.
- `orbitSum_eq_galoisOrbitSum` (with `[Fintype (L ≃ₐ[k] L)]`): the orbit sum
  `RootPairing.OrbitPartner.orbitSum P ρ p` equals
  `CharacterAveraging.galoisOrbitSum k L T (P.root p)`. Both are sums over the Galois group,
  and the summands agree by `root_smul`.
- `orbitSum_ne_zero`: if no actual root has zero `galoisOrbitSum`, then no orbit sum of `P`
  is zero. This is the standing hypothesis of the orbit-partner lemmas.
- `stabilizer_eq`: if `P.root p = β.val`, then `RootPairing.OrbitPartner.stabilizer P ρ p`
  is the stabilizer of `β`. The proof uses `root_smul` and injectivity of `P.root`.
- `isOrbitPartner`: if `IsRootPartner k L j β β'` holds, with `P.root p = β.val` and
  `P.root q = β'.val`, then `RootPairing.OrbitPartner.IsOrbitPartner P ρ p q`.

## Orbit partners and their fields

Now also assume `[Finite J]` and the hypothesis

`hne : ∀ γ, CharacterAveraging.galoisOrbitSum k L T γ.val ≠ 0`

over all actual roots `γ` of `j_L`. Fix actual roots `β β' μ` with
`h : IsRootPartner k L j β β'` and `hμ : μ.val = β.val + β'.val`.

- `smul_partner`: if `σ • β = β'`, then `σ • β' = β`. Proof. Lift to indices `p` and `q` with
  `ρ σ • p = q`. By `IsOrbitPartner.smul`, `q` and `ρ σ • q` are orbit partners. So `ρ σ • q`
  and `p` are both partners of `q`, and `IsOrbitPartner.unique` gives `ρ σ • q = p`.
- `stabilizer_le_and_relIndex`: the stabilizer of `β` is contained in the stabilizer of `μ`,
  with relative index `2`. These are `IsOrbitPartner.stabilizer_le` and
  `IsOrbitPartner.relIndex_stabilizer` of `RootDatumOrbitPartners`. `stabilizer_eq` translates
  them to stabilizers of roots.
- `rootOrbitField_le`: `rootOrbitField k L j μ ≤ rootOrbitField k L j β`, by
  `IntermediateField.fixedField_le`.
- `relIndex_fixingSubgroup` (with `[FiniteDimensional k L]`): the fixing subgroup of the
  field of `β` has relative index `2` in the fixing subgroup of the field of `μ`.

The last three results also assume `[IsGalois k L]`. Mathlib has no algebra instance
between nested intermediate fields, so they also assume
`[Algebra (rootOrbitField k L j μ) (rootOrbitField k L j β)]` and the scalar tower over `L`.
A caller can supply these from `rootOrbitField_le` with
`Langlands.Algebra.QuadraticFixedFields.nestedAlgebra` and
`nestedAlgebra_isScalarTower`.

- `isQuadraticExtension`: `Algebra.IsQuadraticExtension` from the field of `μ` to the field
  of `β`, by `QuadraticFixedFields.isQuadraticExtension` and `relIndex_fixingSubgroup`.
- `isSeparable`: this extension is separable. It needs none of the root hypotheses
  (`QuadraticFixedFields.isSeparable`).
- `conjugation_apply`: if `σ • β = β'`, then for every `x` in the field of `β`,
  `(SU3Root.conjugation (rootOrbitField k L j μ) (rootOrbitField k L j β) x : L) = σ x`.
  The two instances in the statement are `isQuadraticExtension` and `isSeparable`.
  Proof. `σ` fixes `μ`, since `σ • μ = β' + β = μ` by `smul_partner`. `σ` does not fix `β`.
  So `σ` lies in the fixing subgroup of the field of `μ` but not of the field of `β`.
  `QuadraticFixedFields.conjugation_apply` then applies.

## Scope

The module takes the decomposition `μ = β + β'` and the nonvanishing of Galois orbit sums
as hypotheses. It does not show that a multipliable relative root has such a decomposition.
Reducedness of the absolute roots is available as `rootReducedness` in
`Reductive/RootReducednessProof`; `RootPairNoncommutation.isReduced` supplies the
root-datum consequence under the connected-reductive and split-maximal-torus hypotheses.
The decomposition comparison remains to be supplied here. In the
intended application the nonvanishing comes from the condition that no root restricts to
zero on the largest split subtorus; this module does not prove that. It does not identify the Lie-algebra root spaces with these fields, and it does not prove the
formula `μ(z) = β(z) · conj(β(z))` for points `z` of the torus.
