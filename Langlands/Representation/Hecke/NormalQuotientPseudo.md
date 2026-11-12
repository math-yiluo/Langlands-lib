# Pseudo-forgetting equals forgetting for a normal quotient

Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, III.2.10, printed p.81 / PDF p.87, source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:
for `M = P ⧸ N`, `ˇF(V) = Hom_{H(M)}(H(M), V)_{H(P)} ≃ V ≃ F(V)`, naturally.

`pseudoFIsoF` is a natural isomorphism between the published functors
`pseudoF μM μP q _` and `F μM μP q _` from nondegenerate `H(M)`-modules to
nondegenerate `H(P)`-modules, for the quotient projection `q` of a closed
normal subgroup `N`. Here `F V` is the original balanced tensor
`H(M) ⊗_{H(M)} V` with the left `H(P)`-action on `H(M)`, and `pseudoF V` is the
nondegenerate part of `Hom_{H(M)}(H(M), V)` for the right `H(P)`-action.

## General lemmas

- `rightModule_mul` (any continuous `φ : H →* G`): `(T·a) * S = T * (a·S)`,
  the balance of the right and left `H(H)`-actions on `H(G)` against
  convolution. It is `heckeAction_rightModule` for the left regular action,
  with `heckeAction_leftTests_eq_mul` on both sides.
- `nondegenerateIsoOfBijective`: a morphism of nondegenerate modules whose
  underlying additive map is bijective is an isomorphism (same construction as
  the published `contractionIso`).
- `regularOrbit m`: the module map `b ↦ b • m` out of the left regular module.

## The comparison

- `smul_contraction_smul`: `c • contraction(a • t) = (c·a) • contraction(t)`
  for `a ∈ H(P)`, `c ∈ H(M)` and a tensor `t ∈ F V`. On pure tensors this is
  `(c * (a·b)) • m = ((c·a) * b) • m`, i.e. `rightModule_mul`; the general case
  follows from `NonUnitalModuleTensor.hom_ext`.
- `forgetToPseudo V : F V ⟶ pseudoF V` sends `t` to `regularOrbit
  (contraction t)`, i.e. `c ↦ c • contraction t`. It is `H(P)`-linear by
  `smul_contraction_smul`; its values lie in the pseudo part
  (`regularOrbit_contraction_mem`) because `F V` is nondegenerate.
- `forgetToPseudo_bijective`. Injective: if `c • contraction t = 0` for all
  `c`, nondegeneracy of `V` gives `contraction t = 0`, and the published
  contraction is injective (`contraction_injective`). Surjective: a pseudo-part
  element `ψ` is fixed by some idempotent `e` of `H(P)`; a normalized indicator
  `e_K` of `P` with `e_K * e = e` (`finiteFamilyLocalUnits`) gives
  `ψ(b) = ψ(b·e_K) = ψ(b * e_{q(K)}) = b • ψ(e_{q(K)})`
  by `rightModule_normalizedIndicator`, so `ψ` is the image of
  `f ⊗ ψ(e_{q(K)})` for an idempotent `f` fixing `ψ(e_{q(K)})`.
- `forgetToPseudo_naturality` follows from naturality of the contraction.
- `pseudoFIsoF` is the inverse of the resulting `NatIso.ofComponents`.
