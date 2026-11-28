# The unitary embedding theorem from Landherr's theorem and a global twist class

Module: `Langlands.Algebra.CentralSimple.NumberFieldUnitaryEmbeddingReduction`.

`Langlands.CentralSimple.NumberFieldUnitaryEmbeddingReductionStatement.{u}` is the implication

```text
NumberFieldLandherrStatement → NumberFieldLocalGlobalEmbeddingStatement →
  MaximalSubfieldConjugacyStatement → NumberFieldUnitaryEmbeddingClassStatement →
  NumberFieldUnitaryEmbeddingStatement
```

in one universe `u`. The five propositions are stated in the modules
`Langlands.Algebra.CentralSimple.NumberFieldLandherrStatement`,
`Langlands.Algebra.CentralSimple.NumberFieldLocalGlobalEmbeddingStatement`,
`Langlands.Algebra.CentralSimple.MaximalSubfieldConjugacyStatement`,
`Langlands.Algebra.CentralSimple.NumberFieldUnitaryEmbeddingClassStatement` and
`Langlands.Algebra.CentralSimple.NumberFieldUnitaryEmbeddingStatement`; this module does not
prove the four premises. The theorem `Langlands.CentralSimple.numberFieldUnitaryEmbeddingReduction`
proves the implication.

## Auxiliary declarations

They are in the namespace `Langlands.CentralSimple.UnitaryEmbeddingReduction`. In the first
two groups `R` is a commutative ring, `A` an `R`-algebra, `L` a commutative `R`-algebra,
`τ : FirstKindInvolution R A`, `σ : FirstKindInvolution R L` and `f : L →ₐ[R] A`.

- `involutionUnit τ u` is `τ u` as a unit, with inverse `τ u⁻¹`
  (`involutionUnit_val`, `involutionUnit_inv`); `involution_inv_of_fixed` proves
  `τ t⁻¹ = t⁻¹` when `τ t = t`.
- `exists_class_of_conjugate`: assume `f` is injective, `t` is a unit with `τ t = t` and
  `τ (f y) = t f(σ y) t⁻¹`, every element commuting with the image of `f` lies in it, and
  `y ↦ u f(y) u⁻¹` intertwines `σ` and `τ` for a unit `u`. Then `t f(a) = h τ(h)` for a unit
  `a` of `L` with `σ a = a` and the unit `h = τ u`. Proof: `m = t⁻¹ τ(u) u` commutes with every
  `f z` (apply the intertwining identity to `σ z` and the twisting identity), and so does
  `m⁻¹`; hence `m = f β` and `m⁻¹ = f β'` with `β β' = 1` by injectivity. Applying `τ` to
  `m` gives `t f(σ β) t⁻¹ = τ(u) u t⁻¹`, so `f (σ β) = m = f β` and `σ β = β`. Finally
  `t f(β) = t m = τ(u) u`.
- `conjugate_intertwines`: if `τ (f y) = t f(σ y) t⁻¹` and `t f(a) = x τ(x)` for units `a` of
  `L` and `x` of `A`, then with `w = τ x` one has `τ (w f(y) w⁻¹) = w f(σ y) w⁻¹`. Proof: the
  left side is `x⁻¹ t f(σ y) t⁻¹ x`; the unit identities `x⁻¹ t = w f(a)⁻¹` and
  `t⁻¹ x = f(a) w⁻¹`, consequences of `t f(a) = x w`, turn it into
  `w f(a)⁻¹ f(σ y) f(a) w⁻¹`, and `f(a)` commutes with `f(σ y)` because `L` is commutative.
- `conjugateHom w f` is the algebra homomorphism `p ↦ w f(p) w⁻¹` (`conjugateHom_apply`).
- `exists_symmetric_twist` (for a field `L`): if `σ θ ≠ θ` for some `θ`, `f` is injective,
  `τ (f (σ y)) = g f(y) g⁻¹` for a unit `g`, and the image of `f` is self-centralizing, then
  there is a unit `t` with `τ t = t` and `τ (f y) = t f(σ y) t⁻¹`. Proof: applying `τ` to the
  hypothesis shows that `c = g⁻¹ τ(g)` commutes with the image of `f`, so `c = f γ`; applying
  `τ` to `c` gives `f(σ γ) = τ(g)⁻¹ g`, hence `γ σ(γ) = 1`. Hilbert's Theorem 90 for `σ`, in
  the explicit form `μ = b + γ σ(b)` with `b = 1` if `1 + γ ≠ 0` and `b = θ` otherwise, gives
  `μ ≠ 0` with `γ σ(μ) = μ`; then `t = g f(μ)` is as required.

For fields `F ⊆ E`, an `E`-algebra `B` and a field `P` over `E`, both `F`-algebras through `E`:

- `extend F K f = Algebra.TensorProduct.map (AlgHom.id K K) (f.restrictScalars F)` is
  `id_K ⊗ f : K ⊗[F] P → K ⊗[F] B` for `f : P →ₐ[E] B` (`extend_tmul`).
  `extend_injective` proves that it is injective when `f` is and `K` is a field: its underlying
  map is `LinearMap.lTensor K f`, and `K` is flat over the field `F`.
- `tensorUnit F K t` is the unit `1 ⊗ t` of `K ⊗[F] B` (`tensorUnit_val`, `tensorUnit_inv`).
  `extend_twist` proves that `τ (f p) = t f(σ p) t⁻¹` implies
  `τ_K (extend F K f y) = (1 ⊗ t) (extend F K f (σ_K y)) (1 ⊗ t⁻¹)`, by induction on tensors.
- `global_conjugacy` deduces from `MaximalSubfieldConjugacyStatement` with `K = F`, for
  injective `f g : P →ₐ[E] B`, a unit `u` of `B` with `g p = u f(p) u⁻¹` and the
  self-centralization of the image of `f`. It transports along
  `Algebra.TensorProduct.lid`, using `extend F F h = lid⁻¹ ∘ h ∘ lid`.
- `placeCompletion_isField` proves that each `Global.placeCompletion F v` is a field.

## Proof of the implication

Let `F`, `E`, `B`, `P`, `τ`, `σ` satisfy the hypotheses of `NumberFieldUnitaryEmbeddingStatement`,
with local homomorphisms `φ_v`. The extension `E/F` is finite (its degree is two), `E` has
characteristic zero, so `P/E` is separable.

1. Forgetting the involutions, the `φ_v` satisfy the hypotheses of
   `NumberFieldLocalGlobalEmbeddingStatement`, which gives an `E`-algebra homomorphism
   `ε : P → B`; it is injective because `P` is a field.
2. `p ↦ τ(ε(σ p))` is again an `E`-algebra homomorphism `ε' : P → B`: it is multiplicative
   because `σ` and `τ` both reverse products, and `E`-linear because `σ` and `τ` both act on
   `E` by the conjugation, an involution. `global_conjugacy` gives a unit `g₀` with
   `τ(ε(σ p)) = g₀ ε(p) g₀⁻¹` and the self-centralization of `ε(P)`.
3. `σ` is nontrivial on the image of `E`, since `SU3Root.conjugation F E ≠ 1`.
   `exists_symmetric_twist` gives a unit `t` of `B` with `τ t = t` and
   `τ(ε p) = t ε(σ p) t⁻¹`.
4. At a place `v`, with the field structure of `K_v = Global.placeCompletion F v`,
   `MaximalSubfieldConjugacyStatement` applied to `extend F K_v ε` (injective by
   `extend_injective`) and `φ_v` gives a unit `u` with `φ_v y = u ε_v(y) u⁻¹` and the
   self-centralization of the image of `ε_v = extend F K_v ε`. The twisting identity extends to
   `K_v` (`extend_twist`) with the symmetric unit `1 ⊗ t`, and `φ_v` intertwines `σ_v` and
   `τ_v`, so `exists_class_of_conjugate` gives a `σ_v`-fixed unit `a_v` of `K_v ⊗[F] P` and a
   unit `h_v` with `(1 ⊗ t) ε_v(a_v) = h_v τ_v(h_v)`.
5. These are the hypotheses of `NumberFieldUnitaryEmbeddingClassStatement` for `ε` and `t`,
   which gives a nonzero `a ∈ P` with `σ a = a` such that `t ε(a)` has the form `h τ_v(h)` at
   every place.
6. The unit `y = t ε(a)` is symmetric: `τ(t ε(a)) = τ(ε a) t = t ε(σ a) t⁻¹ t = t ε(a)`.
   `NumberFieldLandherrStatement` gives a unit `x` of `B` with `t ε(a) = x τ(x)`.
7. By `conjugate_intertwines`, `φ = conjugateHom (τ x) ε`, that is `p ↦ τ(x) ε(p) τ(x)⁻¹`, is
   an `E`-algebra homomorphism with `φ (σ p) = τ (φ p)`.

## Provenance

The argument is that of G. Prasad and A. S. Rapinchuk, *Local-global principles for
embedding of fields with involution into simple algebras with involution*, Comment. Math.
Helv. 85 (2010), cited in its arXiv version 0806.0596v5 (source
`prasad-rapinchuk-2010-embedding-fields-involution`), proof of Theorem 4.1, pp. 13–17: the
global embedding `ε` by Proposition 2.7 (step 1), the symmetric twisting element of
Proposition 3.1, p. 10 (steps 2–3, `exists_symmetric_twist`), the criterion of Theorem 3.2,
pp. 11–12, in the directions (i) ⇒ (iii) locally (step 4, `exists_class_of_conjugate`) and
(iii) ⇒ (i) globally (step 7, `conjugate_intertwines`). The source then solves the global
equation with the multinorm principle, Eichler's norm theorem and Lemma 4.3, which uses the
Hasse principle for `SU(A, τ)`; here that part is replaced by the premise
`NumberFieldUnitaryEmbeddingClassStatement` (a global `σ`-fixed `a` with everywhere local
solutions) and Landherr's theorem (a global solution from local ones).
