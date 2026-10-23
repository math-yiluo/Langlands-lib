# The reciprocity law for cyclic subextensions of cyclotomic extensions

This module proves the reciprocity law for cyclic subextensions of cyclotomic extensions
(reciprocity proof, task fb66219f). The proof assumes the unramified cyclotomic input
`UnramifiedCyclotomicFrobenius` of `Langlands.ClassField.Global.UnramifiedCyclotomicStatement`
as an explicit hypothesis `hU`:

`cyclicCyclotomicReciprocity_of (hU : UnramifiedCyclotomicFrobenius.{u}) : CyclicCyclotomicReciprocity.{u}`.

`CyclicCyclotomicReciprocity` is the proposition of
`Langlands.ClassField.Global.ReciprocityStatement`. Let `I` be a family of local invariant
maps satisfying the class-formation axioms and the arithmetic normalization. Let `E / F` be
a cyclic Galois extension of number fields that embeds over `F` into a cyclotomic field
`F(μ_m)`. Then every class of `H²(Gal(E/F), Eˣ)` satisfies `SumOfInvariantsVanishes I`:
for every choice of places of `E` above the places of `F`, only finitely many finite local
invariants are nonzero, and the sum of all finite and archimedean local invariants is `0`.

The auxiliary results are in `Langlands.ClassField.Global.CyclicReciprocityParts`. All
declarations below are in the namespace `Langlands.ClassField.Global.CyclicReciprocity`.

## Setting

- `F ⊆ E ⊆ L` are number fields in `Type u`, with `E / F` and `L / F` Galois.
- `ζ ∈ L` is a primitive `m`-th root of unity, and `hinj` says that
  `autToPow F : Gal(L/F) → (ℤ/m)ˣ` is injective.
- `χ : Gal(E/F) → ℤ/n` is a character and `a ∈ Fˣ`. `cyclicClass F E χ a` is the Library's
  carry class of `a` and `χ`.
- `artinSymbol hζ hinj v : F_vˣ → Gal(L/F)` is the local Artin symbol of
  `Langlands.ClassField.Global.LocalSymbolIdentity`. It sends `b` to the automorphism acting
  on `ζ` by the cyclotomic symbol `normSymbolAt m (rationalPlace v) v b`.

## Residue fields

- `one_lt_card_residue`: the residue field `𝓞_F / v` has `q > 1` elements.
- `natCast_card_pow_sub_one_not_mem`: `q^n − 1 ∉ v` for `n > 0`.
- `orderOf_natCast_pow_sub_one`: for `q > 1` and `n > 0`, the order of `q` modulo `q^n − 1`
  is `n`.

## The local identity at a finite place

- `finiteLocalInvariant_cyclicClass_of_modulus`. Here `ζ` is a primitive `M`-th root of
  unity, `N ∣ M` with `N ∉ v`, and `n` is the order of `q` modulo `N`. For `w ∣ v` a place
  of `E`,

  `finiteLocalInvariant v w I (cyclicClass F E χ a) = χ(artinSymbol v a |_E).val / n`.

  Proof. `hU` supplies the unramified data at `v` for `U = F(ζ^{M/N})`: the order `e = n`, an
  arithmetic coordinate `χ_U`, and the Frobenius hypothesis. Let `u = placeAbove L w`. The
  local image of the carry class at `w` is the local carry class
  (`unitsLocalMap_cyclicClass`). Inflate it from `E_w` to `L_u` with the inflation axiom of
  `I` and `relativeInflation_cyclicClass`. The inflated character is
  `(χ ∘ res_E) ∘ decompositionHom v u` (`decompositionHom_restrictNormal`).
  `relative_cyclicClass` of `LocalSymbolIdentity` then evaluates the invariant.
- `finiteLocalInvariant_cyclicClass`: the same identity at every finite place `v`, when
  `L = F(μ_m)` (`IsCyclotomicExtension {m} F L`).

  Proof. Put `N = q^n − 1` and `L' = F(μ_{N m})`, and embed `L` into `L'` over `F` as a
  splitting field of `X^m − 1`. Then `N ∉ v` and the order of `q` modulo `N` is `n`. The
  previous theorem for `L'` with `M = N m` gives the identity with the Artin symbol of `L'`.
  Its restriction to `L` is the Artin symbol of `L`
  (`artinSymbol_restrictNormal` of `CyclicReciprocityParts`), and restricting from `L'` to
  `E` is restricting first to `L`.

## The sum of the local invariants

Here `L = F(μ_m)`.

- `neg_one_mem_galoisImage`: if `F` has a real place, `-1` lies in the Galois image
  `galoisImage F hζ ⊆ (ℤ/m)ˣ`: a complex conjugation sends `ζ` to `ζ⁻¹`.
- `imageCharacter hζ hinj χ : Additive (galoisImage F hζ) →+ ℚ/ℤ` (definition) sends `s` to
  `χ(σ_s|_E).val / n`, where `σ_s ∈ Gal(L/F)` acts on `ζ` by `s`. It is the composite of the
  isomorphism `galoisImage F hζ ≅ Gal(L/F)`, restriction to `E`, `χ`, and
  `zmodClass n : ℤ/n → ℚ/ℤ`. `imageCharacter_apply` states this value.
- `signElement hζ a v ∈ galoisImage F hζ` (definition) is `-1` if `v` is real and
  `v(a) < 0`, and `1` otherwise. `coe_signElement` states its value in `(ℤ/m)ˣ`.
- `archimedeanInvariant_eq_imageCharacter`: for an injective `χ` and `w` above an infinite
  place `v`, the archimedean invariant of `cyclicClass F E χ a` at `w` is
  `imageCharacter (signElement a v)`. If `v` is real, a complex conjugation `τ` of `L / F`
  restricts to a conjugation at `w`, with `autToPow τ = -1`
  (`archimedeanInvariant_cyclicClass_of_isConj`). If `v` is complex, both sides are `0`.
- `finiteLocalInvariant_eq_imageCharacter`: for `w` above a finite place `v`, the finite
  local invariant of `cyclicClass F E χ a` at `w` is `imageCharacter` of the cyclotomic
  symbol of `a` at `v`. This is `finiteLocalInvariant_cyclicClass`.
- `sumOfInvariantsVanishes_cyclicClass`: for an injective `χ` and every `a ∈ Fˣ`,
  `SumOfInvariantsVanishes I (cyclicClass F E χ a)`.

  Proof. By the two previous results every local invariant is `imageCharacter` of a local
  symbol or of a sign element. The finite local invariants vanish wherever the symbol of
  `a` is `1`, which is all but finitely many places (`mulSupport_normSymbolAt_finite`). The
  sum of the invariants is `imageCharacter` of the product of all local symbols and all
  sign elements. This product is
  `symbolProduct m (N_{F/ℚ} a) · signUnit m (N_{F/ℚ} a)`, by the finite product formula
  `finprod_normSymbolAt` and the sign formula `signUnit_norm`. It is `1` by the rational
  product formula `product_formula` of `Langlands.Global.CyclotomicSymbol`.

## The main theorem

`cyclicCyclotomicReciprocity_of`. Take `E / F` cyclic with an `F`-embedding
`ι : E → L = F(μ_m)`, and make `L` an `E`-algebra through `ι`. Let `ζ` be the chosen
primitive `m`-th root of unity of `L`; `autToPow` is injective because `L = F(ζ)`. A
generator gives an isomorphism `χ : Gal(E/F) ≅ ℤ/[E:F]` (`zmodCyclicMulEquiv`). Every class
of `H²(Gal(E/F), Eˣ)` is a carry class `cyclicClass F E χ a`
(`CyclicClassAlgebra.exists_cyclicClass_eq`), and `sumOfInvariantsVanishes_cyclicClass`
applies.

## Provenance

This is Case 1 of the proof of Theorem 6 in Artin–Tate, Chapter VII §3, printed p.45
(PDF p.54). For a cyclic cyclotomic `K / ℚ` every class is `κ(α) ∪ δχ`, its invariant is
`χ((α, K/ℚ))`, and `(α, K/ℚ) = 1`. The identity
`Σ_p inv_p κ(a) ∪ δχ = χ(∏_p (a_p, K_p/k_p))` is on the same page. The identification of
the local norm residue symbol with the cyclotomic symbol is Theorem 5 of Chapter VII §2,
printed p.41 (PDF p.50); here it is `LocalSymbolIdentity.relative_cyclicClass`.

Artin–Tate prove Case 1 over `ℚ` and reach a general base field by inflation and transfer.
This module works over an arbitrary number field `F` instead, with the abstract invariant
family `I` in place of a constructed norm residue symbol. The enlargement of the
cyclotomic field to `F(μ_{(q^n − 1) m})` at each place, the use of `imageCharacter` and
`signElement`, and the reduction to the rational product formula through `N_{F/ℚ}` are
internal to this project.
