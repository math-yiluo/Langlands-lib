# Joint surjectivity of analytified spectrum-surjective families

This module proves, without extra hypotheses, input 7 of the published conditional reduction
`SpaceAnalytificationExistenceReductionStatement`. If a family of `K`-algebra maps
`fᵢ : A → Bᵢ` is jointly surjective on prime spectra, then the analytified maps
`Spec(Bᵢ)ᵃⁿ → Spec(A)ᵃⁿ` are jointly surjective on underlying points. The corresponding
classical fact is Berkovich (1990), Proposition 3.4.6(7), together with the fibre
description in its proof. The Lean proof below is a direct seminorm argument.

## Declarations

- `JointSurjectivity.exists_ringHom_comp_algebraMap` (pure algebra). Let `B` be a finite type
  `A`-algebra, `Ω` an algebraically closed field and `g : A →+* Ω` a ring map. Suppose the
  prime `ker g` is the contraction of some prime of `B`. Then `g` extends to a ring map
  `g' : B →+* Ω` with `g' ∘ algebraMap A B = g`.

  Proof. Let `k` be the residue field of `ker g`. Since `ker g` lies in the image of
  `Spec B → Spec A`, the fibre ring `k ⊗[A] B` is nontrivial
  (`PrimeSpectrum.nontrivial_iff_mem_rangeComap`). Choose a maximal ideal `m` of it. The
  quotient `(k ⊗[A] B)/m` is a field of finite type over `k`, hence finite over `k` by the
  Zariski lemma (`finite_of_finite_type_of_isJacobsonRing`). The map `g` induces
  `k →+* Ω` (`Ideal.ResidueField.lift`). Since `Ω` is algebraically closed, this map extends
  to `(k ⊗[A] B)/m` (`IsAlgClosed.lift`). Then `g'` is the composite
  `B → k ⊗[A] B → (k ⊗[A] B)/m → Ω`.

- `exists_baseMap_eq`. Let `P` and `Q` be finite polynomial presentations of `A` and `B`, and
  let `f : A →ₐ[K] B`. Let `z` be a point of `Spec(A)ᵃⁿ` whose center (the prime
  `kernel K P z` of its seminorm) is `comap f 𝔮` for a prime `𝔮` of `B`. Then
  `baseMap K P Q f y = z` for some point `y` of `Spec(B)ᵃⁿ`.

  Proof.
  1. `BaseChangeComparison.normedRealization` realizes the seminorm `ν` of `z`. It gives a
     complete ultrametric normed field `H` and `f₀ : A →ₐ[K] H` with `‖f₀ a‖ = ν a`.
  2. Let `Ω = ValuedField.CompleteAlgebraicClosure H`, and let `g : A → Ω` be `f₀` followed
     by `H → Ω`. Then `‖g a‖ = ν a` (`norm_algebraMap`), so `ker g` is the center of `z`.
  3. Make `B` an `A`-algebra via `f`. It is of finite type over `K` (via `Q`), hence over
     `A`. The algebraic lemma gives `g' : B → Ω` with `g' ∘ f = g`.
  4. The seminorm `μ b = ‖g' b‖` on `B` (`BaseChangeComparison.pullback` of the norm of `Ω`)
     extends the norm of `K`, because `μ (f a) = ν a`.
  5. By `SeminormComparison.range_pointSeminorm`, `μ` is the seminorm of some point `y` of
     `Spec(B)ᵃⁿ`. By `pointSeminorm_baseMap`, the seminorm of `baseMap K P Q f y` is
     `a ↦ μ (f a) = ν a`.
  6. Points are determined by their seminorms (`SeminormComparison.pointSeminorm_injective`),
     so `baseMap K P Q f y = z`.

- `exists_mem_range_localizedHom` (input 7 in the exact form of the published reduction, with
  `A`, `Bᵢ : Type u` and an index type in any universe). Assume every prime of `A` is
  `comap (fᵢ) 𝔮` for some `i` and some prime `𝔮` of `Bᵢ`. Then every point `z` of
  `localizedSpaceFunctor.obj (localized K P)` lies in the range of
  `localizedSpaceFunctor.map (localizedHom K P (Qᵢ) (fᵢ))` for some `i`.

  Proof. Apply the hypothesis to the center of `z` to get `i`. Then `exists_baseMap_eq`
  gives a preimage `y`. Finally `localizedSpaceFunctor_map_localizedHom` identifies the
  underlying map of the localized morphism with `baseMap`.

## Scope

The base field `K` is complete, ultrametric and nontrivially normed. In `exists_baseMap_eq`
the algebras `A` and `B` may live in different universes. Nothing here depends on unproved
hypotheses.
