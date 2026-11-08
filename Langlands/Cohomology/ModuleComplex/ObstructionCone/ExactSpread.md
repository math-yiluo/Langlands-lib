# Spreading middle exactness of a three-term complex from a field point to modules

Module `Langlands.Cohomology.ModuleComplex.ObstructionCone.ExactSpread`, namespace of the same
name. This is an internal commutative-algebra helper for
`Langlands.Cohomology.ModuleComplex.ObstructionCone.openStatement`. All rings and modules of
the main theorem have one universe `u`.

## Main theorem

`exists_exact_rTensor_spread`. Let `A` be a commutative ring, and let `a : F₁ → F₂` and
`b : F₂ → F₃` be `A`-linear maps with `b ∘ₗ a = 0`. Assume `F₁` is finite and `F₂`, `F₃` are
finite projective. Let `k` be a field with an `A`-algebra structure, and assume the base
changes `a.baseChange k`, `b.baseChange k` (on `k ⊗[A] -`) are exact at the middle
(`Function.Exact`). Then there is `g : A` with `algebraMap A k g ≠ 0` such that for every
`A`-module `M` on which `m ↦ g • m` is bijective, the maps `a.rTensor M`, `b.rTensor M` (on
`- ⊗[A] M`) are exact at the middle.

No noetherian hypothesis is used, and `k` need not be a residue field of `A`.

## Proof

1. Choose a surjection `π₁ : A^p → F₁`. The images under `a ⊗ k` of the vectors `1 ⊗ π₁(eₗ)`
   span the range of `a ⊗ k` (`span_range_baseChange`). By `exists_linearIndependent'` some
   of them, indexed by a finite type `κ₁`, form a basis of that range; write `x : κ₁ → F₁`.
   Choose `z : κ₂ → F₂` in the same way so that the images of `1 ⊗ zⱼ` under `b ⊗ k` form a
   basis of the range of `b ⊗ k`.
2. Put `X = Fintype.linearCombination A x`, `Z = Fintype.linearCombination A z`, and
   `e = a ∘ X ∘ (restriction to κ₁) + Z ∘ (restriction to κ₂) : A^(κ₁ ⊕ κ₂) → F₂`,
   with `h₂ = b ∘ Z`. Then `b ∘ e = h₂ ∘ (restriction to κ₂)` (`hbe`). Over `k`, `e` sends
   the standard basis to the family `Sum.elim (a(xᵢ)) (zⱼ)`. That family is linearly
   independent: the `zⱼ` part maps to a basis under `b`, and its span meets the kernel of
   `b ⊗ k` only in `0`. It spans, by exactness at `k`. So `e ⊗ k` is bijective, and `h₂ ⊗ k`
   is injective.
3. `exists_retract` writes `F₂` and `F₃` as retracts `π ∘ s = id` of finite free modules.
   The published `FibreH0Spread.exists_split_of_baseChange`, applied to `s₂ ∘ e` and
   `s₃ ∘ h₂`, gives `L : F₂ → A^(κ₁ ⊕ κ₂)` and `H : F₃ → A^κ₂` with `L ∘ e = g₁ • id` and
   `H ∘ h₂ = g₃ • id`, where `g₁` and `g₃` are nonzero in `k`.
4. The endomorphism `Φ = s₂ e L π₂ + (id − s₂ π₂)` of `A^m` satisfies `π₂ ∘ Φ = e ∘ L ∘ π₂`.
   Over `k`, `e L = g₁ • id`, so `Φ ⊗ k` is injective, hence bijective, and
   `algebraMap A k (det Φ) ≠ 0` (`algebraMap_det_ne_zero`, using `LinearMap.det_baseChange`).
   The adjugate gives `Φ'` with `Φ ∘ Φ' = det Φ • id` (`exists_comp_eq_det_smul`).
5. Take `g = det Φ * g₃`. If `g` acts bijectively on `M`, so do both factors
   (`smul_bijective_of_mul`) and hence on every `N ⊗ M` (`smul_bijective_tensor`).
   Then `Φ ⊗ M` is surjective, so `e ⊗ M` is surjective by `π₂ ∘ Φ = e ∘ L ∘ π₂`, and
   `h₂ ⊗ M` is injective (`surjective_rTensor_of_comp_eq_smul`,
   `injective_rTensor_of_comp_eq_smul`).
6. If `(b ⊗ M) y = 0`, write `y = (e ⊗ M) c`. Then `(h₂ ⊗ M)` of the `κ₂`-part of `c` is
   `0`, so that part vanishes, and `y` lies in the range of `a ⊗ M`. The converse inclusion
   is `b ∘ a = 0`.

The remaining lemmas (`rTensor_injective_of_retract`, `baseChange_injective_of_retract`,
`funLeft_single_*`) are the routine identities used above.

## Provenance

Internal. This is a linear-algebra form of the openness statement of The Stacks Project,
More on Algebra, Lemma 78.4, as used in Artin's Axioms, Lemma 98.23.4 (Tag 07YN). That lemma
says that vanishing of `H^i(C ⊗^L κ(𝔭))` for a pseudo-coherent `C` spreads to all modules over
some `A_f`. Here the complex is a three-term piece of finite projective modules. The proof
implemented is the direct determinant and splitting argument above, not the Stacks argument.
