# Algebra of cyclic carry classes

This module proves the basic algebraic properties of the Library's explicit cyclic class
`cyclicClass K L χ a ∈ H²(Gal(L/K), Lˣ)` (module `Langlands.ClassFieldTheory.Local.CyclicClass`).
Here `χ : Gal(L/K) →* Multiplicative (ZMod n)` is any homomorphism with `n ≠ 0`, and `a ∈ Kˣ`.
The class is represented by the carry cocycle `(g, h) ↦ a ^ ⌊(r(g) + r(h)) / n⌋`, where
`r(g) ∈ [0, n)` is the standard representative of `χ g`. In classical notation it is the cup
product `κ(a) ∪ δχ` of Artin–Tate. The results serve the proof of the reciprocity law for
cyclic cyclotomic extensions (task fb66219f).

The module has one definition, `cyclicClassHom`; everything else is a theorem. All
declarations are in the namespace `Langlands.ClassFieldTheory.Local.CyclicClassAlgebra`.

## Definition

- `cyclicClassHom χ : Additive Kˣ →+ relativeCohomology K L 2` is the carry class
  `a ↦ cyclicClass K L χ a`, packaged as an additive map. `cyclicClassHom_apply` is its
  defining equation.

## Additivity in the unit

- `baseUnit_mul` and `baseUnit_one`: the inclusion `baseUnit K L : Kˣ → Additive Lˣ` is
  multiplicative.
- `cyclicUnitCocycle_apply` gives the value of the carry cocycle.
- `cyclicClass_mul`: `cyclicClass K L χ (a * b) = cyclicClass K L χ a + cyclicClass K L χ b`.
  The two cocycles agree pointwise.
- Consequences: `cyclicClass_one` (the class of `1` is `0`), `cyclicClass_pow`
  (`a ^ k` gives `k •`) and `cyclicClass_inv`.

## Additivity in the character

- `carry_mul_identity`: for `x₁ x₂ y₁ y₂ ∈ ℤ/n`, the carries satisfy
  `c(x₁+x₂, y₁+y₂) + c(x₁, x₂) + c(y₁, y₂) = c(x₁, y₁) + c(x₂, y₂) + c(x₁+y₁, x₂+y₂)`.
  The proof multiplies by `n` and uses `n · c(x, y) + (x + y).val = x.val + y.val`
  (`cyclicCarry_spec`).
- `cyclicClass_mul_character`:
  `cyclicClass K L (χ₁ * χ₂) a = cyclicClass K L χ₁ a + cyclicClass K L χ₂ a`.
  By the identity above, the carry cocycle of `χ₁ * χ₂` minus those of `χ₁` and `χ₂` is the
  coboundary of `g ↦ a ^ (-ε(g))` with `ε(g) = c(χ₁ g, χ₂ g)`. The unit `a` is fixed by the
  Galois action.
- Consequences: `cyclicClass_one_character` (the trivial character gives `0`),
  `cyclicClass_pow_character` (`χ ^ k` gives `k •`) and `cyclicClass_inv_character`.

## Change of modulus

- `cyclicClass_eq_of_val_eq`: let `n = e * k`, and let `ψ` be a character into `ℤ/n` and `χ`
  a character into `ℤ/e` whose standard representatives satisfy `r_ψ(g) = k · r_χ(g)` for
  all `g`. Then `cyclicClass K L ψ a = cyclicClass K L χ a`. The carries agree:
  `⌊(k x + k y) / (e k)⌋ = ⌊(x + y) / e⌋`.

## Naturality

- `map_cyclicClass`: let `φ : Gal(L'/K') →* Gal(L/K)` be a group homomorphism and let
  `f : Rep.res φ (unitsRepresentation K L) ⟶ unitsRepresentation K' L'` be a morphism of
  representations with `f (baseUnit K L a) = baseUnit K' L' a'`. Then
  `groupCohomology.map φ f 2 (cyclicClass K L χ a) = cyclicClass K' L' (χ.comp φ) a'`.
  Here `L` and `L'` share a universe, as the coefficient categories require. The proof
  compares the image cocycle with the carry cocycle pointwise.
- `relativeInflation_cyclicClass`: for a tower `K ⊆ L ⊆ M` with `L / K` normal,
  `relativeInflation K L M 2 (cyclicClass K L χ a)` is the carry class of `a` for the
  inflated character `χ ∘ restrictNormal`. The Library's `inflationCoefficients_baseUnit`
  supplies the coefficient condition.
- `relativeRestriction_cyclicClass`: for a tower `K ⊆ L ⊆ M`,
  `relativeRestriction K L M 2 (cyclicClass K M χ a)` is the carry class over `L` of the
  image of `a` in `Lˣ`, for the restricted character `χ ∘ restrictScalars`.

## The norm criterion

- `exists_mulEquiv_of_injective`: let `G` be a finite group and
  `ψ : G →* Multiplicative (ZMod n)` an injective homomorphism. Then `n = |G| · k` for some
  `k`, and there is a group isomorphism `χ : G ≃* Multiplicative (ZMod |G|)` with
  `r_ψ(g) = k · r_χ(g)` for all `g`. The proof goes in three steps.
  - The image of `ψ` has order `|G|`, so `|G|` divides `n`.
  - Since `ψ(g)^{|G|} = 1`, `n` divides `|G| · r_ψ(g)`, so `k` divides `r_ψ(g)`.
  - The quotients `r_ψ(g) / k` define a homomorphism into `ℤ/|G|`. It is injective because
    `ψ` is, hence bijective by counting.

The remaining results assume `L / K` finite Galois.

- `cyclicClass_eq_zero_iff`: for a group isomorphism `χ : Gal(L/K) ≃* Multiplicative (ZMod n)`,
  `cyclicClass K L χ a = 0 ↔ a ∈ normSubgroup K L`. Here `normSubgroup K L` is the image of
  the field norm `Lˣ → Kˣ`. The proof uses the Library's proven
  `cyclicClassNormNormalization`: the injective comparison `cyclicH2NormEquiv` sends the
  carry class of `b` to the class of `b` in `Kˣ / N(Lˣ)`. It is applied to `a` and to `1`.
- `cyclicClass_eq_zero_iff_of_injective`: the same criterion for any injective character
  `ψ : Gal(L/K) →* Multiplicative (ZMod n)`. It follows from the two previous results and
  `cyclicClass_eq_of_val_eq`.
- `exists_cyclicClass_eq`: for a group isomorphism `χ : Gal(L/K) ≃* Multiplicative (ZMod n)`,
  every class of `H²(Gal(L/K), Lˣ)` is `cyclicClass K L χ a` for some `a ∈ Kˣ`. The
  comparison `cyclicH2NormEquiv` is bijective and `Kˣ → Kˣ / N(Lˣ)` is surjective. The
  Library has the same statement for fields in one universe, as
  `UnramifiedInflation.exists_cyclicClass_eq` (with `cyclicClassNormNormalization` as a
  hypothesis). Here it holds for independent universes, with no hypothesis.

## Provenance

These are the standard properties of the cyclic cup-product class `κ(a) ∪ δχ`, used
throughout Artin–Tate Chapter VII §3. Examples are the local components
`c_p = κ(a_p) ∪ δχ_p` on printed p.44 (PDF p.53) and Theorem 6, Case 1, on printed p.45
(PDF p.54). Cup product with `δχ` is also the tool in the proof of Milne, *Class Field
Theory* VII, Lemma 8.5, printed p.223 (PDF p.232). The Lean statements and proofs are internal to this
formalization. They work with the Library's explicit carry cocycle, not with a general cup
product. In particular, the change-of-modulus and naturality results are exact identities
of cocycles.
