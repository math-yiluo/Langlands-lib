# Separating an actual Brauer relation by unramified types

Author: Worker 1838. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. Following
Deligne (1973), §4.10, an actual relation among induced character differences
splits into separate relations, one for each class of unramified twists. This
module proves that splitting at the level of trace characters, for any admissible
choice of exponents. It asserts no epsilon or L-factor identity. The existence of
admissible exponents is a separate unit.

## Abstract lemmas (`Langlands.LocalFactor.BrauerKernel`)

- `eq_zero_of_sum_mul_pow_eq_zero`: suppose `x : ι → ℂ` is injective on a finite type
  and `Σ_i a_i x_i^k = 0` for every `k : ℕ`. Then every `a_i` is zero. The maps
  `k ↦ x_i^k` are distinct monoid homomorphisms `Multiplicative ℕ →* ℂ`, so Mathlib's
  Dedekind independence of characters (`linearIndependent_monoidHom`) applies.
- `type_separation`: let `deg : W →* ℤ` (multiplicatively) and `c ∈ ℂ`. Suppose
  exponents `τ_i` satisfy `exp(-(τ_i - τ_j) c m) ≠ 1` for `i ≠ j` and every nonzero
  integer `m`. Suppose also that functions `B_i` are invariant under right
  multiplication by an element `n₀` of nonzero degree `d`, and that
  `Σ_i exp(-τ_i c)^{deg w} B_i(w) = 0` for every `w`. Then every `B_i` vanishes. To
  see this, evaluate at `w n₀^k`: the ratios `exp(-τ_i c)^d` are distinct, and the
  previous lemma applies.

## Frobenius sums (`Langlands.VirtualRepresentation.ExactGrothendieckGroup`)

These use the published `frobeniusFunctional` of `BrauerKernel.Trace`.

- `frobeniusFunctional_mul_character`: a character `Ω` of the ambient group factors
  out of the Frobenius sum at `g` as `Ω(g)`. On a fixed coset the factor
  `q.out · g · q.out⁻¹` has the same `Ω`-value as `g`.
- `frobeniusFunctional_mul_right`: right translation of `g` by an element of a
  normal subgroup `N ≤ S` does not change the sum, provided the function is
  invariant under right multiplication by `N`. The fixed cosets are unchanged, and
  the subgroup factor changes by a conjugate of the translating element.

## Generators (`Langlands.LocalFactor.NonabelianBrauer`)

For a generator `g = (L, χ, χ')` over `E`, `Generator.nested` is the subgroup
`W_L ∩ W_E` of `W_E`. For a character `ψ` of `W_L`, `frobeniusSum F g ψ w` is the
Frobenius sum of `ψ ∘ nestedWeilEquiv` at `w`, that is, the trace of
`Ind_{W_L}^{W_E} ψ` at `w`.

- `trace_generatorClass`: the trace of `generatorClass F e E g` at `w` is
  `frobeniusSum` of the Weil character of `χ` minus that of `χ'`. This uses the
  published `CommonClosure.trace_induce` and `trace_characterClass`.
- `twistedWeilCharacter F e L χ t` is the Weil character of `χ` times the published
  base-degree twist `CommonClosureSpectral.character F L (-t)`, that is,
  `w ↦ q_F^{t·deg_F w}`. `weilCharacter_eq_twisted` writes the Weil character as
  `character F L t` times this twisted character. `character_nested`:
  the twist is the same function on `W_L ∩ W_E` whether read in `W_L` or in `W_E`.
- `frobeniusSum_weilCharacter`: the Frobenius sum of the Weil character equals
  `character F E t w` times the Frobenius sum of the twisted character.
- `frobeniusSum_mul_right`: invariance under right translation by a normal
  subgroup of `W_E` contained in `W_L ∩ W_E` on which the twisted character is
  trivial.

`typeComponent F e z t₁ t₂ τ w` takes a presentation `z` and exponents `t₁`, `t₂` for
the first and second characters of each generator. It is
`Σ_{g ∈ supp z} z(g) ([t₁ g = τ] S₁(g, w) − [t₂ g = τ] S₂(g, w))`, where `S₁` and `S₂`
are the Frobenius sums of the two twisted characters.

`trace_virtualPresentation_apply` expands the trace of the actual virtual class
`virtualPresentation F e E z` generator by generator. `trace_eq_sum_typeComponent`
regroups it as `Σ_{τ ∈ T} character F E τ w · typeComponent … τ w`. Here `T` is the
finite set of exponents used on the support.

`exists_mem_baseDegree_ne_one`: every finite-index subgroup of `W_E` contains an
element of nonzero base degree. Take a power of a degree-one element of `W_F`
(published `localDegree_surjective`) lying in `W_E`, then a power of that lying in
the subgroup. Both powers exist by `Subgroup.exists_pow_mem_of_index_ne_zero`.

`typeComponent_eq_zero` is the main result. Assume:

1. `presentationMap F e E z = 0`;
2. all twisted characters of the support are trivial on a normal finite-index
   subgroup `N` of `W_E` contained in each `W_L ∩ W_E`;
3. any two distinct exponents `τ ≠ τ'` in use satisfy
   `exp(-(τ - τ') log q_F · m) ≠ 1` for every nonzero integer `m`, that is,
   `τ − τ' ∉ (2πi / log q_F) ℚ`.

Then every type component vanishes at every element of `W_E`. Proof: the trace of
the zero class vanishes. Hence `Σ_τ character F E τ (w) · B_τ(w) = 0` with
`B_τ = typeComponent … τ`. Each `B_τ` is invariant under right translation by `N`,
which contains an element of nonzero degree. `type_separation` with
`c = log q_F` and `deg = baseDegree` gives `B_τ = 0` for `τ ∈ T`. Outside `T`
the component is an empty sum.

The normalized-reciprocity premise is not used; only the actual relation and its
trace are. Field and representation universes remain independent.

## Provenance

Deligne, *Les constantes des équations fonctionnelles des fonctions L* (1973),
registered as `deligne-1973-local-constants`, SHA256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`, §4.10
(printed page 542, PDF page 42). There, representations of type `r` form an
abelian subcategory, `R(W) = ⊕_r R_r(W)` (4.10.1), and twisting by an unramified
character of type `r` identifies `R_r` with the Galois part (4.10.2). This module
is an internal derivation of the needed consequence for the free presentation. The
actual relation splits by classes of unramified exponents modulo
`(2πi / log q_F) ℚ`, with traces as the separating invariant.
