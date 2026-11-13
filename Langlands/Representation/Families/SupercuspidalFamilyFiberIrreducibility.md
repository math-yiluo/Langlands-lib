# Fibers of the induced universal unramified family

This module proves the **fiber step** of Renard's VI.8.6 Example. The main theorem is
`Langlands.Renard.AlgebraicFamily.isIrreducible_supercuspidalFamilyFiber`. Take the
universal unramified family `ρ_B` of a smooth representation `σ` of `M(F)`, induce it to
`G(F)`, and specialize the induced family at the evaluation `χ : B → ℂ` at an unramified
character `ψ`. The theorem says this specialization is irreducible whenever the complex
induction `i_P^G(σ ⊗ ψ)` is irreducible.

The module does **not** prove the task target `SupercuspidalFamilyEndomorphismStatement`.
That proof also needs generic irreducibility (VI.8.5) and admissibility of irreducible
supercuspidal representations of `M(F)`. Neither is in the Library unconditionally.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026. Literature ID `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

- VI.8.1, the Example (printed p. 189 / PDF p. 195). For a smooth `(π, V)`,
  `V_B = V ⊗_ℂ B` with `π_B(g)(v ⊗ b) = π(g) v ⊗ χ_un(g) b`. For `χ ∈ X(G)`, "la
  spécialisation de `π_B` en `χ` est isomorphe à `π ⊗ χ`": `V_B ⊗_B ℂ_χ = V ⊗_ℂ χ`.
- VI.8.2, the Proposition (printed p. 190 / PDF p. 196). "Le changement de base commute à
  l'induction": `i_P^G(E) ⊗_B C ≅ i_P^G(E ⊗_B C)` as `(G, C)`-modules.
- VI.8.4, the notation of the proof (printed p. 192 / PDF p. 198), and the VI.8.6 Example
  (printed p. 195 / PDF p. 201). There the fibers of `π_B = i_P^G(ρ_B)` are the complex
  inductions `i_P^G(ρ ⊗ χ)`, and their irreducibility is the input to the VI.8.6
  Proposition.

The Example applies these facts without proof. The module derives them from the published
VI.8.2 base-change equivalence and from the definitions of the published objects, so its
provenance is **derived**.

## Lean model

The setting is the one in the published `SupercuspidalFamilyEndomorphismStatement`:

- `k` is a nonarchimedean local field and `G` a group scheme over `Spec k`, with the
  canonical topology on its rational points.
- `p : P ⟶ G` is a rational parabolic, with rational Levi `l`, geometric unipotent radical
  `r`, and `IsIso (subgroupMultiplication l r)`.
- `M(F)` carries the published Levi point topology.
- `ν` is the family of rational norm characters of `M(F)`, and
  `B = Plancherel.unramifiedRegularFunctions ν`.
- `ρB = Plancherel.universalUnramifiedRepresentation ν σ` acts on `B ⊗[ℂ] W`.
- `χ : B →ₐ[ℂ] ℂ` satisfies `∀ b, χ b = b.val ψ`, and makes `ℂ` a `B`-algebra.

The specialization of a `(G, B)`-module `V` along `χ` is
`(Module.End.baseChangeHom B ℂ V).toMonoidHom.comp ρ` on `ℂ ⊗[B] V`. By definition this
is the published `Langlands.Renard.AlgebraicFamily.baseChange ℂ ρ`
(`RenardFamilyParabolicFunctors`), and that is the form the module works with. "Irreducible"
means `Representation.IsIrreducible`.

## Declarations

### `SupercuspidalFiber.isIrreducible_of_equiv`

Irreducibility of complex representations transfers along a `Representation.Equiv`. The
proof uses `Representation.irreducible_iff_isSimpleModule_asModule` and the bijective
module map induced by the equivalence.

### Section `Fiber`: cancelling the base change

Let `A` be a commutative `ℂ`-algebra, and let `ℂ` be an `A`-algebra with scalar tower
`ℂ → A → ℂ`.

- `universalFiberCancel : ℂ ⊗[A] (A ⊗[ℂ] V) ≃ₗ[ℂ] V` is Mathlib's
  `AlgebraTensorModule.cancelBaseChange` followed by `TensorProduct.lid`.
- `universalFiberCancel_tmul` computes it on pure tensors:
  `c ⊗ (b ⊗ v) ↦ (algebraMap A ℂ b * c) • v`.
- `universalFiberCancel_baseChange` is the induction lemma behind the next section. If the
  map intertwines `baseChange ℂ ρ g` with `σ g` on all pure tensors `c ⊗ (b ⊗ v)`, then it
  does so on every element of `ℂ ⊗[A] (A ⊗[ℂ] V)`. The proof is a double
  `TensorProduct.inductionOn`.

### Section `Universal`: VI.8.1 Example

In this section, `B = Plancherel.unramifiedRegularFunctions ν`, and `ℂ` carries some
`B`-algebra structure with `algebraMap B ℂ b = b.val ψ` (hypothesis `hψ`).

- `isScalarTower_of_evaluation` shows that `hψ` makes `ℂ → B → ℂ` a scalar tower.
- `universalFiberCancel_universal` shows that `universalFiberCancel` intertwines
  `baseChange ℂ (universalUnramifiedRepresentation ν π)` with
  `Langlands.twist ψ.val.toMonoidHom π`. On a pure tensor, `g` sends `c ⊗ (b ⊗ v)` to
  `c ⊗ (ev_g · b ⊗ π(g) v)` (`universalUnramifiedRepresentation_tmul`). Cancelling gives
  `(ψ(g) b(ψ) c) • π(g) v`, which is `ψ(g) • π(g) ((b(ψ) c) • v)`.
- **`universalFiberEquiv ν ψ hψ π`** is the resulting `Representation.Equiv` from
  `baseChange ℂ ρ_B` to the twist `π ⊗ ψ`. This is the specialization isomorphism of the
  VI.8.1 Example, given by `c ⊗ (b ⊗ v) ↦ c b(ψ) v`. Renard writes `V ⊗ B`; the Library
  writes `B ⊗ V`.

### Section `Parabolic`

- `representationEquivComp e f` restricts an equivalence `e : σ₁ ≃ σ₂` of representations
  of `K` along a group homomorphism `f : H →* K`.
- `inducingRepresentationEquiv h hU e` builds an equivalence of the published inducing
  representations from an equivalence `e` of Levi representations. It applies
  `Langlands.twistEquiv` to the modulus character and then restricts along the projection
  `P → M`.

### Section `Represented`

- `leviInducedEquiv p l r hp hl hr hmul e` turns an equivalence `σ₁ ≃ σ₂` of
  `(M(F), B)`-modules into an equivalence of the normalized inductions
  `leviInducedRepresentation … σ₁ ≃ leviInducedRepresentation … σ₂`. The proof is
  `Induction.smoothInducedEquiv` applied to `inducingRepresentationEquiv`, after
  transport along `leviPointsEquiv`.
- `exists_leviInducedBaseChangeRepEquiv` restates the published
  `exists_leviInducedBaseChangeEquiv` (VI.8.2 Proposition) as a nonempty type of
  `Representation.Equiv`s, from `baseChange C (leviInducedRepresentation … σ)` to
  `leviInducedRepresentation … (baseChange C σ)`. It needs compactness of `P(F)\G(F)` and
  smoothness of `σ`.

### Section `Complex`

- `constantCharacter_complex` states that the published `constantCharacter ℂ χ` is `χ`.
- `leviInducedComplexEquiv` handles `B = ℂ`. Normalized family induction of a smooth complex
  representation `A` of `M(F)` is equivalent to the published complex induction
  `(leviInductionFunctor …).obj A`. Both are `Induction.smoothInduced` of an inducing
  representation, and the two inducing representations agree:
  `inducingRepresentation_eq_twist_of_isUnimodularModulus` applies because the radical is
  unimodular (`isUnimodularModulus_pointImage_radical`), and then
  `constantCharacter_complex` applies.
- `isIrreducible_baseChange_leviInduced` is the general fiber step. Assume `ρ` is a smooth
  `(M(F), B)`-module, `ℂ` is a `B`-algebra with scalar tower `ℂ → B → ℂ`, and
  `e : baseChange ℂ ρ ≃ A` for a smooth complex `A` whose complex induction is irreducible.
  Then `baseChange ℂ (leviInducedRepresentation … ρ)` is irreducible. The proof composes
  three equivalences and then applies `isIrreducible_of_equiv`:
  1. E1: `exists_leviInducedBaseChangeRepEquiv`, i.e. base change commutes with induction;
  2. E2: `leviInducedEquiv e`, i.e. the specialized Levi family is `A`;
  3. E3: `leviInducedComplexEquiv A`, i.e. family induction at `ℂ` is complex induction.

### Section `Main`

**`isIrreducible_supercuspidalFamilyFiber hG p l r hp hl hr hmul`** takes the binders of
`SupercuspidalFamilyEndomorphismStatement`: a smooth `σ`, `ν`, `ρB`, `ψ`, and `χ` with
`∀ b, χ b = b.val ψ`. Assume the complex induction
`(leviInductionFunctor …).obj ((SmoothRep.of σ hσ).twist ψ.val.toMonoidHom _)` is
irreducible. Then the specialization along `χ`,
`(Module.End.baseChangeHom B ℂ (LeviInduced … ρB)).toMonoidHom.comp
(leviInducedRepresentation … ρB)`, is irreducible. This is the fiber hypothesis of the
published `EndomorphismScalarStatement` at the point `χ`. The conclusion is word for word
the body of `SupercuspidalFamilyFiberStatement` from Worker 5205's reduction module
`RenardSupercuspidalFamilyEndomorphismReduction`.

The proof supplies the inputs of `isIrreducible_baseChange_leviInduced`:

- `ρB` is smooth by `Plancherel.isSmooth_universalUnramifiedRepresentation_of_continuous`.
  The norm characters are continuous by `Plancherel.rationalNormContinuousCharacter`, which
  needs `IsAffine M.X.left`, a consequence of `isAffine_of_isAffineHom`.
- `P(F)\G(F)` is compact by `compactSpace_leftQuotient_pointImage_of_dynamic`, applied to
  the published dynamic-parabolic compactness.
- The scalar tower `ℂ → B → ℂ` is `IsScalarTower.of_algebraMap_eq`, from `χ.commutes`.
- `e` is `universalFiberEquiv ν ψ hψ σ`, and `A` is the twist `σ ⊗ ψ`.

Inside the proof, local `let` instances of `AddCommGroup` and `Module B` on `B ⊗[ℂ] W`
restate the instances that the statement fixes with `letI`. Without them, elaboration of
the smoothness and base-change steps timed out.
