# Restriction of the transfer along a homomorphism

Helper module for the proof of
`Langlands.ClassField.Global.RelativeWeilGroup.TransferNormCompatibilityStatement`
(task `d02b213c-6237-44c1-a667-4a8c19662bfe`). It uses only Mathlib's transfer
(`MonoidHom.transfer`) and left transversals. It states and proves nothing about Weil
groups.

## Declarations

Let `G` and `G'` be groups, `M` a commutative group, `A` a subgroup of `G` and `A'` a
subgroup of `G'`.

- `Langlands.GroupTheory.Transfer.conjComap ι hι w : A' →* A` (definition). Here `A` is
  normal, `ι : G' →* G` is a homomorphism, `hι` says that `ι` maps `A'` into `A`, and
  `w ∈ G`. It sends `a` to `w * ι a * w⁻¹`, which lies in `A` because `A` is normal.
  `coe_conjComap` is the defining formula. This is an internal auxiliary construction.
- `Langlands.GroupTheory.Transfer.transfer_apply_eq_prod` (theorem). Assume `A` is normal
  of finite index in `G` and `A'` has finite index in `G'`. Assume `x ∈ A' ↔ ι x ∈ A` for
  every `x`, so `A'` is the inverse image of `A`. Assume `A ≤ ι.range`. Then for every
  `ϕ : A →* M` and `h ∈ G'`,

  ```text
  transfer ϕ (ι h) = ∏ q : G ⧸ ι.range, transfer (ϕ ∘ conjComap ι _ q.out) h.
  ```

  Here `q.out` is the chosen representative of the left coset `q`. A `Fintype` instance on
  `G ⧸ ι.range` is a hypothesis only so that the product can be written. It always exists,
  because `ι.range` contains `A` and so has finite index.

## Provenance

This is the coset computation behind Tate (1979), *Number theoretic background*, (1.2.2)
and the remark after it, p.4. Tate treats a normal subgroup `H` of finite index in `G`.
Here `ι` need not be injective, and its range need not be normal. The lemma is derived and
internal: it is the group-theory step of the target proof.

## Implemented proof

Fix the default left transversal `T'` of `A'` in `G'`, and write `t' r` for its
representative of the coset `r ∈ G' ⧸ A'`.

1. *A transversal of `A` built from `ι`.* Define

   ```text
   e : (G ⧸ ι.range) × (G' ⧸ A') → G ⧸ A,   e (q, r) = [ι (t' r) * q.out⁻¹].
   ```

   The map `e` is bijective.
   - Injectivity. Suppose `e (q₁, r₁) = e (q₂, r₂)`. Conjugating the difference by
     `q₁.out⁻¹` gives an element of `A` (normality), hence an element `ι y` of the range
     (`A ≤ ι.range`). This element gives `q₁.out⁻¹ * q₂.out = ι ((t' r₁ * y)⁻¹ * t' r₂)`,
     so `q₁ = q₂`. Then the same element is `ι ((t' r₁)⁻¹ * t' r₂) ∈ A`, so
     `(t' r₁)⁻¹ * t' r₂ ∈ A'` by `hι`, and `r₁ = r₂`.
   - Surjectivity. For `g ∈ G`, put `q = [g⁻¹]`. Then `g * q.out = ι y` for some `y`, and
     `e (q, [y]) = [g]`.

   Let `f` send `p ∈ G ⧸ A` to `ι (t' r) * q.out⁻¹`, where `(q, r) = e⁻¹ p`. Then
   `[f p] = p`, so `Set.range f` is a left transversal `S` of `A` (Mathlib's
   `isComplement_range_left`), and its representatives are `f`
   (`IsComplement.leftQuotientEquiv_apply`).
2. *The action.* For every pair, `(ι h)⁻¹ • e (q, r) = e (q, h⁻¹ • r)`. The quotient of the
   two representatives is the conjugate by `q.out` of `ι ((h⁻¹ * t' r)⁻¹ * t' (h⁻¹ • r))`.
   That element lies in `A`, because `t' (h⁻¹ • r)` represents the coset of `h⁻¹ * t' r`.
3. *The product.* Expand both sides with `MonoidHom.transfer_def`, using `S` on the left
   and `T'` in each factor on the right. Merge the double product into one product over
   pairs (`Fintype.prod_prod_type'`). Reindex the left side along `e`
   (`Fintype.prod_bijective`). Rewrite the translated transversals with
   `smul_apply_eq_smul_apply_inv_smul`, then with step 2 and the formula for `f`. For the
   pair `(q, r)`, both factors are then `ϕ` applied to
   `q.out * ι ((t' r)⁻¹ * h * t' (h⁻¹ • r)) * q.out⁻¹`. The tactic `group` checks this
   identity.
