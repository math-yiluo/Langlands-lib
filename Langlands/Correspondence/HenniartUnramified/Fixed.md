# Fixed inertia types and torsion-one classes over unramified extensions

## General lemmas

- `equivOfEq` turns an equality of representations into an equivalence.
- `restrictConjEquiv`: for a representation `τ` of a split group, the inertia
  restriction conjugated by `lift ^ k` is equivalent to the inertia restriction itself,
  via `τ(lift^k)⁻¹`.

## Good types

Fix a p-adic field `F` and a degree-one `φ`.

- `TypeGood F φ hφ r t B` says that the inertia type `B` has dimension `r` and
  satisfies `r · inertiaBreak F B = t`.
- `goodTypes F φ hφ r t` is the set of classes of such types. Membership of a class
  depends only on the class (`typeGood_congr`, `mem_goodTypes_iff`).
- Frobenius conjugation preserves goodness (`typeGood_conjObj`,
  `conjType_mem_goodTypes`). Conjugation preserves the normal upper groups, so the
  break is unchanged (`inertiaBreak_comp_cj`).

## Fixed types and torsion-one orbits

Let `L` be the unramified stage of degree `m + 1`. `encard_fixed_goodTypes` states

`encard (weilRefinedStratum L r' t 1) = encard {x ∈ goodTypes (r' + 1) t | conjType (m + 1) x = x}`,

in `ℕ∞`. The left side is the Library's `T_L(r' + 1, t)`. The relation used relates an
orbit class `c` over `L` to an inertia class `x` over `F` when some representative `A`
of `c` has first block `A ∘ κ` (in the stage `weilStage F φ hφ m`) in the class `x`.

- From an orbit to a class: if the class has torsion number one, the inertia
  restriction of `A` is irreducible (`inertia_irreducible_of_torsion_one`), so the
  first block is an irreducible type.
  - `blockConjEquiv` shows that the type is fixed by conjugation with `φ^{m+1}`.
  - Its dimension is the rank `r' + 1`.
  - Its break is the last break of `A` (`lastBreak_stage`), so the Swan exponent `t`
    gives `(r' + 1) · break = t` (`hasWeilSwan_weilClassOf`).
- From a class to an orbit: a fixed good type extends to a continuous representation
  `τ` of `W_L` (`exists_extension`).
  - `τ` is irreducible because its inertia restriction is.
  - Its Swan exponent is `t`.
  - Its torsion number is one by `weilTorsionNumber_eq_period`, since its own inertia
    restriction is a type of period one for the stage lift (`restrictConjEquiv`).
- Functional: unramified twists of a representative have the same first block
  (`block_twist`).
- Injective: two representatives with equivalent first blocks have equivalent inertia
  restrictions, by `comp_inertia_eq_block`. Hence they differ by an unramified twist
  (`twist_equiv_of_inertia_ne_zero`) and lie in the same orbit.

This is the fixed-point step of the proof of Henniart (1988), Proposition 2.2, for the
unramified extension of each degree.
