# Kottwitz's Hodge-type function and the reflex field of the Harris datum

Author: Worker 57. This module defines Kottwitz's function `i ↦ n(i)` on the
complex embeddings of the CM field, its stabilizer in `Aut(ℂ/ℚ)` and the
reflex field as the fixed field of that stabilizer. It computes the function
for Harris's datum and compares the reflex field with `Φ τ₁ (K)`.

## The source definition

Kottwitz (1992), printed pp.654-655, writes `F` for the CM center of `D` and
`F₀` for its totally real subfield; here they are `K` and `E`. From the
homomorphism `h₀` (see `Unitary.Positivity`) he gets
`h_{0,ℂ}: ℂ ⊗_ℝ ℂ → D ⊗_ℚ ℂ` and continues:

> Let I denote the set of embeddings of F in ℂ, and for i ∈ I let i′ denote
> the composition of i with the non-trivial automorphism of F/F₀. Then
> D ⊗_ℚ ℂ = ∏_{i∈I} D ⊗_{F,i} ℂ and we write h_i for the composition of
> h_{0,ℂ} with the projection of D ⊗_ℚ ℂ onto D ⊗_{F,i} ℂ. Let V be a simple
> D ⊗_{F,i} ℂ-module; then dim_ℂ V = n. The homomorphism h_i makes V into a
> ℂ ⊗_ℝ ℂ-module. Of course ℂ ⊗_ℝ ℂ ≅ ℂ × ℂ, z₁ ⊗ z₂ ↦ (z₁z₂, z̄₁z₂) and
> corresponding to this product decomposition we have a direct sum
> decomposition V = V₁ ⊕ V₂. Let n(i) = dim_ℂ V₁. Note that n(i) + n(i′) = n
> for all i ∈ I and that G₀ is isomorphic over ℝ to ∏_j U(n(i), n(i′)) where
> j runs over the set of embeddings j: F₀ → ℝ and i, i′ are the two
> embeddings F → ℂ that extend j. The group Aut(ℂ/ℚ) acts on I and hence on
> the set of ℤ-valued functions on I. The reflex field E is the fixed field of
> the stabilizer in Aut(ℂ/ℚ) of the function i ↦ n(i).

## How the definition is modelled

Take `V = ℂⁿ` and let `ℂ` act on it through the second tensor factor. On
`V₁` the element `z₁ ⊗ z₂` acts by `z₁z₂`. So `V₁` is the set of `v` with
`h_i(z ⊗ 1) v = z v` for all `z`.

The published charts of `Unitary.HarrisLevels` identify each real factor
`ℝ ⊗_{E,τ} A` with `M_n(ℂ)`, complex linearly for `K` acting through `Φ τ`.
Complexifying `M_n(ℂ)` gives `M_n(ℂ) ⊗_ℝ ℂ ≅ M_n(ℂ) × M_n(ℂ)` by
`x ⊗ w ↦ (x w, x̄ w)`, where `x̄` is entrywise conjugation. The element
`1 ⊗ k` of `K` acts on the first factor by `Φ τ (k)` and on the second by its
complex conjugate. So the first factor is `D ⊗_{K,Φ τ} ℂ`, and on it `h_i(z ⊗ 1)`
is `h₀(z)`. The second factor is `D ⊗_{K,(Φ τ)′} ℂ`, and on it `h_i(z ⊗ 1)` is
the entrywise conjugate of `h₀(z)`. This derivation explains the definitions
below; the decomposition `D ⊗_ℚ ℂ ≅ ∏_i M_n(ℂ)` itself is not formalized.

## Declarations

General part:

- `hodgeSubspace h`, for `h : ℂ →ₐ[ℝ] M_n(ℂ)`, is the complex subspace
  `{v ∈ ℂⁿ | h(z) v = z v for all z}`. This is Kottwitz's `V₁`.
  `hodgeNumber h` is its complex dimension, Kottwitz's `n(i)`.
- `hodgeSubspace_eq_of_diagonal` and `hodgeNumber_of_diagonal`: if `h(z)` is
  diagonal with entries `z` on a set `p` of coordinates and `z̄` elsewhere,
  then `V₁` is spanned by the coordinates in `p`, and `n(i)` is their number.
- `hodgeNumber_correctedComplexHom_conj r hr`, with `hr : r ≤ n`: at a
  factor of signature `(r, n-r)`, Kottwitz's homomorphism is
  `correctedComplexHom n r ∘ conj`, which is `z` on the first `r` coordinates
  and `z̄` on the rest, so `n(i) = hodgeNumber = r`. Here `n` remains the
  ambient matrix rank, `dim_ℂ V = n`.
  `hodgeNumber_correctedComplexHom r hr`, under the same hypothesis: on the
  entrywise conjugate factor the Hodge number is `n - r`.
- `realPlaceBelow E i` is the real embedding of the totally real field `E`
  below a complex embedding `i` of `K`. `realPlaceBelow_eq_iff`,
  `comp_realPlaceBelow`, `realPlaceBelow_conjugate` (an embedding and its
  conjugate lie above the same place) and `realPlaceBelow_of_isCMSection`
  relate it to restriction and to a CM-type section `Φ`.
- `standardHodgeFunction Φ h i`, for `h : ℂ →ₐ[ℝ] ∏_τ M_n(ℂ)`, is the
  number `n(i)` read off in the model above. Let `τ` be the place below `i`.
  If `i = Φ τ`, it is `hodgeNumber` of the factor `h_τ`. Otherwise `i` is the
  conjugate of `Φ τ`, and it is `hodgeNumber` of the entrywise conjugate of
  `h_τ`.
- `hodgeStabilizer f` is the subgroup of `ℂ ≃ₐ[ℚ] ℂ` (all field
  automorphisms of `ℂ`) of those `s` with `f (s ∘ i) = f i` for all `i`. The
  action of `s` on functions is `(s · f)(i) = f (s⁻¹ ∘ i)`, so this is
  exactly the stabilizer of `f`. `mem_hodgeStabilizer` unfolds membership,
  and `autComp_eq_iff` records that `s ∘ j = s ∘ j'` only if `j = j'`.
- `reflexField f` is `IntermediateField.fixedField (hodgeStabilizer f)`,
  Kottwitz's reflex field.

The Harris datum, for `C : HarrisSignatureCharts σ n Φ` with distinguished
real place `τ₁`:

- `C.hodgeFunction` is `standardHodgeFunction Φ` of
  `kottwitzHom n (E →+* ℝ) τ₁` from `Unitary.Positivity`, and
  `C.reflexField` is its reflex field. The charts enter only through `Φ`
  and `τ₁`; the charts are complex linear for `Φ` (field `center`), which is
  what the model above requires.
- `evalAlgHom_comp_kottwitzHom` identifies the factor at `τ`, and
  `hodgeFunction_apply` gives the values: at `Φ τ` the number `r_τ`, at its
  conjugate `n - r_τ`, where `r_τ = n - 1` at `τ₁` and `r_τ = n` elsewhere.
  These values satisfy `n(i) + n(i′) = n`, and the factor at `τ₁` gives
  `U(n-1, 1)` in Kottwitz's formula for `G₀`, in agreement with
  Harris (1999), (1.1). Both remarks are read off the values; they are not
  stated as separate theorems.
- `distinguishedEmbedding = Φ τ₁` and `distinguishedImage` is its image
  `Φ τ₁ (K)` as an intermediate field of `ℂ / ℚ`.
  `mem_fixingSubgroup_distinguishedImage_iff`: an automorphism fixes this
  image pointwise exactly when `s ∘ Φ τ₁ = Φ τ₁`.
- `hodgeFunction_eq` (for a CM-type section `Φ`): `n - 1` at `Φ τ₁`, `1` at
  its conjugate, `n` at the other `Φ τ` and `0` at their conjugates.
- `hodgeFunction_eq_one` and `hodgeStabilizer_eq_top`: if `n = 2` and `E`
  has only one real embedding, the function is constantly `1`, so its
  stabilizer is all of `Aut(ℂ/ℚ)`.

Harris's CM type, `Φ = harrisCMSection E ι τ₀` for an imaginary quadratic
field `F` with `ι : F →+* K` and a complex embedding `τ₀` of `F`
(Harris 1999, pp.308-309; published in `Unitary.HarrisLevels`):

- `eq_harrisCMSection_realPlaceBelow_iff`: an embedding `i` is the selected
  one above its real place exactly when `i ∘ ι = τ₀`.
- `hodgeFunction_eq_harris`: `n(i)` is `n - 1` at `Φ τ₁`, `1` at its
  conjugate, `n` at the other embeddings inducing `τ₀` on `F`, and `0` at
  the rest. `distinguishedEmbedding_comp`: `Φ τ₁` induces `τ₀`.
- `fixingSubgroup_le_hodgeStabilizer`: every automorphism fixing
  `Φ τ₁ (K)` pointwise stabilizes the function. Such an automorphism fixes
  `Φ τ₁`, its conjugate (because `K` is stable under its CM conjugation)
  and `τ₀`, and these determine the values.
- `hodgeStabilizer_le_fixingSubgroup`, assuming `3 ≤ n` or a real place
  `τ ≠ τ₁`: every stabilizing automorphism `s` fixes `Φ τ₁ (K)`. If
  `s ∘ Φ τ₁ ≠ Φ τ₁`, the value `n - 1` forces `s ∘ Φ τ₁` to be the conjugate
  of `Φ τ₁`, whose value is `1`, so `n = 2`. Then a second real place `τ`
  gives the value `n` at `Φ τ`, so `s ∘ Φ τ` induces `τ₀`, that is,
  `s ∘ τ₀ = τ₀`. But `s ∘ Φ τ₁ = (Φ τ₁)′` gives `s ∘ τ₀ = τ̄₀`, so `τ₀`
  would be real, which is impossible for an imaginary quadratic field.
- `distinguishedImage_le_reflexField` (same hypothesis):
  `Φ τ₁ (K) ⊆ E(G, X)`. `reflexField_le_fixedField` (no hypothesis): the
  reflex field lies in the fixed field of the automorphisms fixing
  `Φ τ₁ (K)`.
- `reflexField_eq_distinguishedImage`: under the same hypothesis, and
  assuming `hgal`, that `Φ τ₁ (K)` is the fixed field of its own fixing
  group in `Aut(ℂ/ℚ)`, the reflex field equals `Φ τ₁ (K)`.

## Comparison with Harris and what is not proved

Harris (1997), printed p.89, lets the first matrix factor "correspond to the
complex place t₁ ∈ Φ above σ₁", and states that the reflex field
`E(GG, X_{n-1})` "is just t₁(K)". In the present notation `t₁` is `Φ τ₁`.
Harris (1997) selects the CM type `Φ` through a `p`-adic embedding, and
Harris (1999) through a complex embedding of the imaginary quadratic
subfield; this module uses the latter. The module proves that Kottwitz's
definition gives `Φ τ₁ (K)` when `3 ≤ n` or `E` has a second real
embedding, given `hgal`.

`hgal` holds for every subfield of `ℂ` that is finite dimensional over `ℚ`.
That is a Galois-theoretic fact about `ℂ` (automorphisms of a subfield extend
to `ℂ`, and every element outside the subfield is moved). It is not proved
here and is kept as an explicit hypothesis. It is a separate target.

In the remaining case, `n = 2` with a single real embedding of `E`, the
stabilizer is all of `Aut(ℂ/ℚ)` and Kottwitz's definition gives the fixed
field of `Aut(ℂ/ℚ)`. The module does not prove that this field is `ℚ`.

The function is computed in the standard archimedean model of the charts.
The module does not construct `D ⊗_ℚ ℂ ≅ ∏_i M_n(ℂ)` for the global algebra,
does not prove that `n(i)` is independent of the chosen charts or of `h₀`
within its conjugacy class, and constructs no canonical model over the
reflex field.

## Sources

- Kottwitz (1992), Section 1, printed pp.654-655 (PDF pp.2-3): `h_{0,ℂ}`, the
  factors `D ⊗_{F,i} ℂ`, `V₁`, `n(i)`, the formula for `G₀` over `ℝ`, and the
  reflex field as a fixed field.
- Harris (1997), Section 2, printed p.89 (PDF p.15): the identification of
  `B ⊗ ℂ` with `d` copies of `M(n, ℂ)` using `Φ`, the place `t₁` above `σ₁`,
  and `E(GG, X_{n-1}) = t₁(K)`. Harris (1998), Erratum, printed pp.180-182:
  the corrected homomorphism.
- Harris (1999), Section 1, printed p.301 (PDF p.3), (1.1): signature
  `U(n-1,1)` at `σ₁` and `U(n)` elsewhere; Section 4, printed pp.308-309
  (PDF pp.10-11): the CM type induced from the imaginary quadratic subfield.

These passages were read in the original. The matrix model of
`D ⊗_{K,i} ℂ`, the stabilizer comparison and the case analysis are derived.

Source IDs and SHA-256 fingerprints:

- `kottwitz-1992-lambda-adic-simple-shimura`:
  `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
- `harris-1997-drinfeld-cohomology`:
  `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.
- `harris-1998-local-langlands`:
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Formal dependencies: `Langlands.Shimura.Unitary.Positivity` (`kottwitzHom`),
`Unitary.HarrisLevels` (`HarrisSignatureCharts`, `matrixConj`,
`IsCMSection`, `eq_or_eq_conjugate_of_comp_eq`, `harrisCMSection` and its
lemmas), `Unitary.Domain` (`correctedComplexHom`), `Unitary.CMData`
(`cmConjugation`, `embedding_cmConjugation`), and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, in particular
`LinearMap.iInfKerProjEquiv`, `IntermediateField.fixedField`,
`IntermediateField.fixingSubgroup`, `IntermediateField.le_iff_le` and
`NumberField.ComplexEmbedding.IsReal.embedding`.
