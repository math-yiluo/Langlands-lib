# Speh representations are Hermitian

Author: Worker 1808. Module `Langlands.Representation.Classification.SpehHermitian`.

## Result

```lean
theorem Langlands.Classification.SpehDatum.hasNonzeroInvariantSesquilinearForm_of_isSpeh
    (d : SpehDatum.{uF, uV} F T) (S : SmoothRep.{0, uF, max uF uV} ℂ
      (GeneralLinear d.degree F.Carrier)) (hS : d.IsSpeh S) :
    HasNonzeroInvariantSesquilinearForm S.representation
```

for every prime `p` with `[Fact p.Prime]`, `F : PadicField.{uF} p`,
`T : F.TopologicalData` (with `T.topology` installed) and independent universes
`uF`, `uV`. `d.IsSpeh S` (published in `TadicUnitaryStatement`) contains
`d.IsDiscreteSeries`: `δ = d.delta` is irreducible, unitarizable and
square-integrable, `S` is an actual irreducible quotient of the centered product
`ν^((k-1)/2) δ × ⋯ × ν^(-(k-1)/2) δ` (`k = d.length`), and every irreducible smooth
quotient of that product is isomorphic to `S`. `HasNonzeroInvariantSesquilinearForm`
(published in `BernsteinUnitaryStatement`) asks for a nonzero form
`b : S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ`, conjugate-linear in the first variable, with
`b (S g v) (S g w) = b v w`. The theorem uses no hypothesis beyond `d.IsSpeh S`.

## Source

Tadic 1986 (`tadic-1986-unitary`, SHA-256
`08e4e1e7c1ccc1e340999287867bc0448f3d8f4bab49906fbf1deda866ae4683`), Proposition
5.6(iii), printed p.363 (PDF p.30): `L(a)^+ ≅ L(a^+)`, where `π^+` is the Hermitian
contragredient (§2.1, p.345). For the Langlands datum
`a(δ,k) = (ν^((k-1)/2) δ, …, ν^(-(k-1)/2) δ)` of `u(δ,k)` and unitarizable `δ`,
`δ^+ ≅ δ` and `(ν^x δ)^+ ≅ ν^(-x) δ`, so `a(δ,k)^+ = a(δ,k)` and `u(δ,k)^+ ≅ u(δ,k)`.
For an irreducible admissible representation, `π ≅ π^+` is equivalent to the
existence of a nonzero invariant sesquilinear form, which is the form stated here.
Tadic's own proof of 5.6(iii) cites the relation (3.3.13) of his reference [15] for
contragredients and Proposition 9.5 of his reference [33]. The Lean proof below takes
a different route, through the Gelfand–Kazhdan theorem.

## Implemented proof

Write `θ = GeneralLinear.inverseTranspose`, `C` for the centered product and `q` for
the quotient map `C ↠ S`.

1. **A `θ`-twisted conjugate-linear automorphism of `δ`**
   (`exists_inverseTransposeConj`). For an irreducible admissible unitarizable `ρ` of
   positive rank, the positive form gives the conjugate-linear equivariant
   `H : ρ ≃ ρ^∨`, `v ↦ b(v, -)` (`InvariantPositiveForm.smoothDualEquiv`,
   `toSmoothDual_apply_action`), and Gelfand–Kazhdan gives a linear
   `E : ρ ∘ θ ≃ ρ^∨` (`hermitianGelfandKazhdanEquiv`, the published
   `gelfandKazhdanContragredient` transported to `T.topology` exactly as in
   `IrreducibleTwoFactorProductSwapProof`). Then `J = E⁻¹ ∘ H` satisfies
   `J (ρ (θ g) v) = ρ g (J v)`. Admissibility of `δ` is
   `IsSquareIntegrable.isAdmissible`. The theorem uses `K = J⁻¹`, with
   `K (δ g v) = δ (θ g) (K v)`.
2. **Blocks** (`segmentFactor_conj_intertwine`). `K` intertwines `ν^s δ` with the
   inverse-transpose pullback of `ν^(-s) δ`: the twisting scalar `|det g|^s` is real,
   hence fixed by conjugation, and `|det (θ g)|^(-s) = |det g|^s`
   (`Parabolic.determinantPowerCharacter_inverseTranspose`).
3. **The product** (`exists_productConj`). The centered exponents satisfy
   `a(rev i) = -a(i)` (`SpehDatum.exponent_rev`). On the uniform shape, the blockwise
   `K` give, by `tensorConjEquiv` and `tensorConjEquiv_external`
   (`ConjugateSpace`), a conjugate-linear automorphism of the Levi tensor product
   intertwining `⊗ᵢ ν^(a i) δ` with `⊗ᵢ (ν^(a (rev i)) δ) ∘ θ`. The half modulus is real,
   so the published `Induction.smoothFunctionsConjEquiv` applies pointwise and gives
   a conjugate-linear equivalence `N` from `C` onto the product of the pullbacks
   `(ν^(a (rev i)) δ) ∘ θ`, commuting with right translation by definition.
4. **Inverse transpose of the product** (`hermitianItPullbackProductIso`,
   `uniformReverseProductIso`). The published
   `Parabolic.normalizedProductInverseTranspose` identifies `C ∘ θ` with the product
   over the reversed shape of the blocks `(ν^(a (rev i)) δ) ∘ θ`. The reversed uniform
   shape is the uniform shape (`uniform_reverse`, by `rfl`), so
   `hermitianProductFunctor_obj_congr` identifies the two products. Call the
   composite isomorphism `L : C ∘ θ ≅ ⊗ᵢ (ν^(a (rev i)) δ) ∘ θ`.
5. **A second quotient.** `Q = q ∘ L⁻¹ ∘ N : C → S` is conjugate-linear, surjective,
   and `Q (C g f) = S (θ g) (Q f)`. `conjTwist F T S` is the representation
   `g ↦ S (θ g)` on `ConjSpace S`. It is smooth because `θ` is continuous, and
   irreducible by `isIrreducible_conjComp_iff`, since `θ` is surjective. As a linear map
   into `ConjSpace S`, `Q` is a surjective intertwiner from `C`
   (`isIrreducibleQuotient_conjTwist`). The uniqueness clause of `d.IsSpeh S` then
   gives an isomorphism `ψ : conjTwist F T S ≅ S`.
6. **The form** (`hasNonzeroInvariantSesquilinearForm_of_conjTwist`). The map
   `P = ψ ∘ equiv` is a conjugate-linear automorphism of `S` with
   `P (S (θ g) v) = S g (P v)`. `S` is admissible
   (`CuspidalSupport.cuspidalEmbedding`), so Gelfand–Kazhdan gives
   `E_S : S ∘ θ ≃ S^∨`. Then `Φ = E_S ∘ P⁻¹` is a conjugate-linear equivariant
   bijection `S → S^∨`. `b v w = ⟨Φ v, w⟩` is invariant
   (`smoothDualPairing_contragredient`) and nonzero: `S` has a nonzero vector,
   because it is irreducible, and `Φ` is injective.

## Declarations

All in namespace `Langlands.Classification`; `F` and `T` are explicit arguments.

| Declaration | Content |
| --- | --- |
| `hermitianGelfandKazhdanEquiv` | Gelfand–Kazhdan `ρ ∘ θ ≃ ρ^∨` under `T.topology`, positive rank. |
| `exists_inverseTransposeConj` | Step 1. |
| `hermitianItPullback` | The pullback `A ∘ θ` on the same carrier (an `abbrev`). |
| `segmentFactor_conj_intertwine` | Step 2. |
| `exists_productConj` | Step 3. |
| `hermitianProductFunctor_obj_congr` | Equal shapes and heterogeneously equal families give isomorphic products. |
| `uniform_reverse` | `(BlockShape.uniform k r hr).reverse = BlockShape.uniform k r hr`. |
| `hermitianItPullbackProductIso` | `(B-product of A) ∘ θ ≅ B.reverse-product of A (rev i) ∘ θ`. |
| `uniformReverseProductIso` | The reversed uniform product is the uniform product. |
| `SpehDatum.exponent_rev` | `d.exponent i.rev = -d.exponent i`. |
| `smoothDualPairing_contragredient` | `⟨g · ℓ, ρ g w⟩ = ⟨ℓ, w⟩`. |
| `conjTwist` | `S̄ ∘ θ` as a smooth representation (an `abbrev`). |
| `isIrreducibleQuotient_conjTwist` | Step 5. |
| `hasNonzeroInvariantSesquilinearForm_of_conjTwist` | Step 6. |
| `SpehDatum.hasNonzeroInvariantSesquilinearForm_of_isSpeh` | The result. |

`hermitianGelfandKazhdanEquiv`, `hermitianItPullback`,
`hermitianProductFunctor_obj_congr` and `hermitianItPullbackProductIso` reuse
the helpers extracted from `IrreducibleTwoFactorProductSwapProof` (Worker 1023)
into the shared `InverseTransposeHelpers` module. The module uses no axiom beyond `propext`, `Classical.choice` and `Quot.sound`,
and no `sorry`.

The four inverse-transpose helpers are shared through
`Langlands.Representation.Classification.InverseTransposeHelpers`.
The original statements and defining terms are preserved; the former private
helpers of `IrreducibleTwoFactorProductSwapProof` have the public `hermitian` names.
