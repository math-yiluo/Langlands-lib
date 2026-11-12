# Normal-quotient coinvariants as the Hecke tensor induction

Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, III.2.10 Proposition and (III.2.10.2), printed pp.81–82 /
PDF pp.87–88, source `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`coinvariantTensorIso N μP μM` is a natural isomorphism

```text
coinvariantHeckeFunctor N μM ≅ quotientTensorHeckeFunctor N μP μM
```

between the published functors of `NormalQuotientStatements`: the actual
coinvariants `j_N` (Mathlib's quotient-to-coinvariants) followed by the
integrated `H(M)`-module functor, and the original balanced tensor
`H(M) ⊗_{H(P)} W` (`P μM μP q _` after the integrated `H(P)`-module functor).
Its two prescribed formulas are:

- `coinvariantTensorIso_inv_tmul`: the inverse sends `T ⊗ w` to `T·[w]`, the
  integrated action of `normalQuotientAction` on the class of `w` (true by
  definition);
- `coinvariantTensorIso_hom_mk`: for `w` fixed by a compact open `K ≤ P`,
  the forward map sends `[w]` to `e_{q(K)} ⊗ w`, map (III.2.10.2).

## Construction

The inverse direction is the source's `Ψ`. `tensorToCoinvariants W` is the
published `NonUnitalBimoduleTensor.leftLift` of the pairing
`coinvariantPairing : (T, w) ↦ T·[w]`:

- balanced by `heckeAction_rightModule_coinvariant`, `(T·a)·[w] = T·[a·w]`,
  which is `heckeAction_rightModule` for `normalQuotientAction` combined with
  `heckeAction_coinvariant` (the coinvariant projection intertwines `W` with
  the pulled-back quotient action, `coinvariantIntertwiner`, so it commutes
  with integrated actions);
- `H(M)`-linear since the integrated action is multiplicative.

`tensorToCoinvariants_bijective`:

- Surjective. Every vector is fixed by a compact open subgroup
  (`exists_compact_fixed`), and `tensorToCoinvariants_normalizedIndicator`
  gives `e_{q(K)} ⊗ w ↦ [w]` because `[w]` is `q(K)`-fixed
  (`coinvariant_mem_fixedVectors`, `heckeAction_coinvariant_of_fixed`).
- Normal form `tensor_eq_tmul_normalizedIndicator`: every tensor equals
  `e_{q(K)} ⊗ u` for some compact open `K ≤ P` and `u ∈ W`. Write the tensor as
  a finite sum of `T_i ⊗ w_i`, choose a compact open subgroup of `M` leaving all
  `T_i` left invariant and `K` inside its preimage, and expand each `T_i` over
  right cosets of `q(K)` (`finite_leftCoset_expansion`). By
  `rightCosetIndicator_eq_smul`, `1_{q(K) q(p)}` is a scalar multiple of
  `r(p⁻¹) e_{q(K)}`, so `tmul_rightCosetIndicator` (from
  `tensor_scalar_balanced` and `tensor_group_balanced`) moves every coset to
  the second factor.
- Injective. If `e_{q(K)} ⊗ u ↦ 0`, replace `u` by `e_K·u` (balance and
  `e_{q(K)} * e_{q(K)} = e_{q(K)}`); this vector is `K`-fixed, so its class is
  zero, i.e. it lies in the coinvariant relations. `tmul_relations` shows
  `T ⊗ x = 0` for every relation `x`: on generators `ρ(n)w − w` use
  `tensor_group_balanced` and `rightRepresentation_of_mem` (`r(n)` is trivial on
  `H(M)` for `n ∈ N`), and closure under sums and complex scalars uses
  `tensor_scalar_balanced`.

`tensorToCoinvariantsHom_naturality` checks naturality on pure tensors with
`integratedAction_intertwiner`. `coinvariantTensorIso` is the inverse of the
resulting `NatIso.ofComponents` (through `nondegenerateIsoOfBijective`), and
the forward formula follows from the inverse formula by injectivity.

The source proves independence of `K` and well-definedness of `Φ` directly and
leaves the inverse check to the reader; this proof instead builds `Ψ` and proves
it bijective, which yields `Φ = Ψ⁻¹` with the stated formula.
