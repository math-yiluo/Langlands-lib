# Proof of Stacks 07E2 (first map): `H₁(L_{L/K}) ⊗_L M → H₁(L_{M/K})` is injective

`FieldH1.fieldH1CotangentInjective : FieldH1CotangentInjectiveStatement` takes no hypotheses and uses
only the standard axioms.

## `δ_map`

The Jacobi–Zariski connecting map `δ : H₁(L_{T/S}) → T ⊗_S Ω_{S/R}` (`Algebra.H1Cotangent.δ R S T`)
is natural in `T`. For `T → T'` and `x ∈ H₁(L_{T/S})`:

`δ_{T'}(H1Cotangent.map S S T T' x) = cancelBaseChange (1 ⊗ δ_T x)`.

Proof: write `x` as the class of `g ∈ S[T]`. Its image in `H₁(L_{T'/S})` is the class of
`rename g` (`defaultHom_self_toAlgHom`). Mathlib's `δ_eq_δAux` computes `δ` on such classes by
`δAux`, and `δAux_rename` finishes the proof.

## `liftBaseChange_map_injective_of_base`

Let `F → K → L → M` with `K, L, M` fields and `H₁(L_{L/F}) = 0`. Then
`M ⊗_L H₁(L_{L/K}) → H₁(L_{M/K})` is injective.

Proof:
1. Jacobi–Zariski for `F → K → L` (`Algebra.H1Cotangent.exact_map_δ`), together with
   `H₁(L_{L/F}) = 0`, makes `δ_L : H₁(L_{L/K}) → L ⊗_K Ω_{K/F}` injective.
2. By `δ_map`, `δ_M` composed with our map equals the base change of `δ_L` followed by the
   isomorphism `M ⊗_L (L ⊗_K Ω) ≅ M ⊗_K Ω`.
3. `M` is flat over the field `L`, so the base change of `δ_L` is injective. Hence our map is
   injective.

## `fieldH1CotangentInjective`

Let `p` be the characteristic of `K`.
- If `p` is prime, take `F = ZMod p` with the algebra structures from `CharP`.
- If `p = 0`, take `F = ℚ`.

`F` is perfect in both cases, so `H₁(L_{L/F}) = 0` by `subsingleton_h1Cotangent_of_perfectField`.
The scalar towers hold because ring maps out of `ZMod p` and out of `ℚ` are unique.

## Relation to Stacks

Stacks, More on Algebra, Lemma 15.35.2 (Tag 07E2; source
`stacks-field-extension-cotangent-07E1-07E3-2026-11-14`, file `07E2.html`) proves the lemma by
combining Lemma 15.34.7 (Tag 07D5) with Algebra, Lemma 10.158.11 (Tag 07BV). Lemma 15.34.7 and
Lemma 15.34.6 (Tag 07D4) (source `stacks-lci-jacobi-zariski-07D4-07D5-2026-11-15`, files
`07D5.html` and `07D4.html`) say that for ring maps `A → B → C` with `B → C` a local complete
intersection homomorphism, or a filtered colimit of such, the six-term Jacobi–Zariski sequence
extends by a zero on the left. Lemma 15.34.6 proves this by showing that `I/I² ⊗ C → K/K²` is
injective for presentations of `B` and `C`, using Koszul regularity. Algebra, Lemma 10.158.11
(source `stacks-commutative-algebra-chapter-ed88ff78`, PDF page 434) says that every field
extension is a filtered colimit of global complete intersection algebras.

This proof avoids local complete intersections and Koszul regularity. It uses the connecting map
to `Ω_{K/F}` over the prime field `F` instead. The argument is original to this formalization.
