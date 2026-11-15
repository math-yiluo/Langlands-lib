# Proof of the transposition of intertwinings between complex principal series

Module: `Langlands.Representation.Archimedean.ComplexStandardHomTransposeProof`, namespace
`Langlands.Archimedean.ComplexStandardHomTransposeProof`.

## Result

The theorem `complexStandardHomTranspose` proves the Library statement
`Langlands.Archimedean.ComplexStandardHomTransposeStatement` (module
`Langlands.Representation.Archimedean.ComplexStandardHomTranspose`) and adds no hypotheses:

```
theorem complexStandardHomTranspose : ComplexStandardHomTransposeStatement
```

The statement says the following. Let `d c : Fin n → ComplexCharacterData`, and let `T : X(d) → X(c)`
be a nonzero `ℂ`-linear map that satisfies `IsComplexStandardIntertwining`. Here `X(ds)` is
`kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)`, the `U(n)`-finite functions
of the principal series of `ds`. Then there is a nonzero intertwining map `T' : X(c⁻¹) → X(d⁻¹)`,
where `c⁻¹ = fun j => complexCharacterDataInv (c j)` and `d⁻¹` is defined the same way.
`ComplexStandardHomTranspose.md` explains the statement and the notation.

The map `T'` is the transpose of `T` under the integration pairings
`⟨f, h⟩ = ∫_{U(n)} f(k) h(k) dk`. The proof follows the route sketched in
`ComplexStandardHomTranspose.md` with one change. The representability of `U(n)`-finite functionals
(step 2 there) is not proved by matching isotypic components and counting dimensions. Instead it
uses the Library's `KFiniteDual.mem_of_separating`. That lemma needs only that every
`U(n)`-isotypic block of `X(ds)` is finite-dimensional, which follows from admissibility.

Throughout, `integralPairing n χ χ'` is the Library's integration pairing (module
`ComplexDuality.Pairing`) of the `U(n)`-finite functions of `principalSeries ℂ n χ` with those of
`principalSeries ℂ n χ'`. Its integral is taken against the normalized Haar measure
`unitaryHaar n` on `U(n)`. For a list `ds`, the position characters are
`complexPositionCharacter ds`, and `X(ds)` is the `U(n)`-finite part of
`principalSeries ℂ n (complexPositionCharacter ds)`.

## Proof

### 1. Admissibility of the complex principal series

`isAdmissibleGKModule_principalSeriesRep χ : IsAdmissibleGKModule (principalSeriesRep ℂ n χ)`
holds for every family of characters `χ : ℕ → ℂˣ → ℂ`. That is, for every matrix representation
`τ` of `U(n)` of degree `d`, the space `gkIntertwiners (principalSeriesRep ℂ n χ) d τ` of
`U(n)`-intertwiners from `τ` into the `U(n)`-finite functions is finite-dimensional. The proof
carries over the real-case argument of the Library module `RealStandardModuleAdmissible`
(`gkIntertwinerValueAtOne`, `gkIntertwinerValueAtOne_injective`) to `GL_n(ℂ)`:

- `complexValueAtOne χ d τ` is the linear map that sends an intertwiner `T` to the functional
  `x ↦ (T x)(1)` on `ℂ^d`. Its target `(Fin d → ℂ) →ₗ[ℂ] ℂ` is finite-dimensional.
- `complexIntertwiner_apply_unitary`: `(T x)(k) = (T (τ(k) x))(1)` for `k ∈ U(n)`. This is the
  intertwining property of `T` at `k`, followed by evaluation of the right translate at `1`.
- `complexValueAtOne_injective`: if `S` and `T` have the same values at `1`, then by the previous
  item `S x − T x` vanishes on `U(n)`. It lies in the principal series, so it vanishes everywhere by
  the Library's `ComplexDuality.eq_zero_of_mem_principalSeries_of_eqOn` (module
  `ComplexDuality.GramWeight`, via the Iwasawa decomposition). Hence `S = T`.
- An injective linear map into a finite-dimensional space has a finite-dimensional source
  (`Module.Finite.of_injective`).

### 2. The integration pairing

Let `χ χ' : ℕ → ℂˣ → ℂ`.

- `integralPairing_principalSeriesRep`: `⟨ρ(k) f, ρ'(k) h⟩ = ⟨f, h⟩` for every `k ∈ U(n)`, where
  `ρ` and `ρ'` are the right translations `principalSeriesRep`. This is the Library's
  `integralPairing_rightTranslation`, which rests on the right invariance of Haar measure.
- `integralPairing_principalSeriesLie`: if `χ i z · χ' i z = 1` for all `i` and `z`, then
  `⟨R(X) f, h⟩ + ⟨f, R(X) h⟩ = 0` for every complex matrix `X`. Here `R(X)` is the right
  derivative `principalSeriesLie ℂ n _ (1 ⊗ X)`. This is the Library's
  `integral_rightDerivative_mul_add_eq_zero` (module `ComplexDuality.LieInvariance`) applied to
  the measure `unitaryHaar n`.
- `exists_integralPairing_ne_zero_left`: if `χ i z · χ' i z = 1` and
  `|χ i z|² = |z|^{2 sᵢ}`, then every nonzero `h` has some `f` with `⟨f, h⟩ ≠ 0`. This is the
  Library's `exists_integral_mul_ne_zero` (module `ComplexDuality.GramWeight`).
- `exists_integralPairing_ne_zero_right`: if `χ i z · χ' i z = 1` and
  `|χ' i z|² = |z|^{2 sᵢ}`, then every nonzero `f` has some `h` with `⟨f, h⟩ ≠ 0`. It applies
  `exists_integral_mul_ne_zero` with `χ` and `χ'` exchanged. The integrand `f(k) h(k)` is
  symmetric, so the two integrals are equal.

The norm hypotheses hold for every position character
(`exists_normSq_complexPositionCharacter`, module `ComplexDuality.GramWeight`).

### 3. Finite vectors of the dual

`isFiniteVector_dual_of_equivariant`: let `L : W → Dual V` be a linear map with
`L(σ(k) w) = ρ^∨(k) (L w)` for every `k`, where `ρ^∨ = ρ.dual` is the contragredient action
(`ρ^∨(k) ℓ = ℓ ∘ ρ(k⁻¹)`, module `KFiniteDual`). Then `L` maps finite vectors of `σ` to finite
vectors of `ρ^∨`. The orbit span of `L w` lies in the image under `L` of the orbit span of `w`, and
that image is finite-dimensional.

### 4. Intertwining maps

`map_complexStandardRep` and `map_complexStandardLie` restate the two clauses of
`IsComplexStandardIntertwining` as equations `A (complexStandardRep n ds k f) = ρ k (A f)` and
`A (complexStandardLie n ds (1 ⊗ X) f) = π (1 ⊗ X) (A f)`. `isComplexStandardIntertwining_of` is
the converse. It uses the Library's `rightTranslation_mem_kFiniteFunctions_complexStandardModule`
and `rightDerivative_mem_kFiniteFunctions_complexStandardModule` (module
`PrincipalSeriesStability`) for the membership parts of the predicate.

### 5. The transpose for arbitrary lists (`exists_transpose`)

`exists_transpose n d c d' c'` concerns lists `d c d' c'` whose position characters are pointwise
inverse: `χ_{d'} i z · χ_d i z = 1` and `χ_{c'} i z · χ_c i z = 1`. It turns every nonzero
intertwining map `T : X(d) → X(c)` into a nonzero intertwining map `T' : X(c') → X(d')`. Write
`⟨·, ·⟩_c = integralPairing n χ_{c'} χ_c` on `X(c') × X(c)` and
`⟨·, ·⟩_d = integralPairing n χ_{d'} χ_d` on `X(d') × X(d)`.

1. **Two maps into the dual of `X(d)`.** Define `Q_d : X(d') → Dual X(d)` by `g ↦ ⟨g, ·⟩_d` and
   `Λ : X(c') → Dual X(d)` by `f ↦ (h ↦ ⟨f, T h⟩_c)` (`Λ = Q_c.compl₂ T`). Both satisfy the
   equivariance hypothesis of step 3 for the right translations and the dual action on
   `Dual X(d)`. For `Q_d` this is the `U(n)`-invariance of the pairing applied to `ρ_d(k⁻¹) h`.
   For `Λ` the same argument applies after `T ρ_d(k) = ρ_c(k) T`.
2. **Representability.** By `isComplexGKModule_complexStandardModule` (module
   `PrincipalSeriesGKModule`), every vector of `X(d)` is `U(n)`-finite with continuous
   coefficients. So `X(d)` is semisimple over the group algebra (`KFiniteDual.isSemisimpleModule`).
   By step 1 and `KFiniteDual.finiteDimensional_block`, every block of `X(d)` is
   finite-dimensional. The range `W'` of `Q_d` is a subrepresentation of `Dual X(d)` because
   `Q_d` is equivariant. It consists of finite vectors by step 3, since every vector of `X(d')`
   is finite. It separates the points of `X(d)` by `exists_integralPairing_ne_zero_left`. Every
   `Λ f` is a finite vector by step 3, since every vector of `X(c')` is finite. So
   `KFiniteDual.mem_of_separating` gives `Λ f ∈ range Q_d` for every `f`.
3. **Injectivity.** `Q_d` is injective by `exists_integralPairing_ne_zero_right`.
4. **Definition of `T'`.** `T' = (LinearEquiv.ofInjective Q_d)⁻¹ ∘ (Λ` with codomain restricted to
   `range Q_d)`. It is linear and satisfies `⟨T' f, h⟩_d = ⟨f, T h⟩_c` for all `f` and `h`. Since
   `Q_d` is injective, two elements of `X(d')` are equal once their pairings with every `h` agree.
5. **`T' ≠ 0`.** Choose `h` with `T h ≠ 0`, then `f` with `⟨f, T h⟩_c ≠ 0`
   (`exists_integralPairing_ne_zero_left` for `c`). Then `⟨T' f, h⟩_d ≠ 0`.
6. **`U(n)`-equivariance.** For `k ∈ U(n)`, write each `h ∈ X(d)` as `ρ_d(k) h₀`. Then
   `⟨T' (ρ_{c'}(k) f), ρ_d(k) h₀⟩_d = ⟨ρ_{c'}(k) f, ρ_c(k) T h₀⟩_c = ⟨f, T h₀⟩_c =
   ⟨T' f, h₀⟩_d = ⟨ρ_{d'}(k) T' f, ρ_d(k) h₀⟩_d`, using the intertwining property of `T` and the
   invariance of both pairings. So `T' ρ_{c'}(k) = ρ_{d'}(k) T'`.
7. **`𝔤𝔩_n(ℂ)`-equivariance.** For a complex matrix `X`, the infinitesimal invariance of both
   pairings gives `⟨R(X) f, T h⟩_c = −⟨f, R(X) T h⟩_c = −⟨f, T R(X) h⟩_c` and
   `⟨R(X) T' f, h⟩_d = −⟨T' f, R(X) h⟩_d = −⟨f, T R(X) h⟩_c`. So
   `⟨T' (R(X) f), h⟩_d = ⟨R(X) T' f, h⟩_d` for every `h`, and `T' R(X) = R(X) T'`
   (`linear_combination`).
8. `isComplexStandardIntertwining_of` turns steps 6 and 7 into
   `IsComplexStandardIntertwining n (complexStandardRep n d') (complexStandardLie n d') c' T'`.

### 6. The final theorem

For `e : Fin n → ComplexCharacterData`, the Library's `complexPositionCharacter_map_inv_mul`
(module `ComplexLanglandsQuotientReduction`) together with `List.map_ofFn` gives
`χ_{e⁻¹} i z · χ_e i z = 1` for `e⁻¹ = List.ofFn fun j => complexCharacterDataInv (e j)`.
`complexStandardHomTranspose` applies `exists_transpose` with `d = List.ofFn d`,
`c = List.ofFn c`, `d' = List.ofFn d⁻¹` and `c' = List.ofFn c⁻¹`.

## Prerequisites demanded by the task

- *Finite-dimensionality of the `U(n)`-isotypic components of the principal series*: step 1
  proves admissibility, and `KFiniteDual.finiteDimensional_block` turns it into
  finite-dimensionality of every block (step 5.2).
- *Identification of the `U(n)`-finite dual of `X(ds)` with `X(ds⁻¹)` through the pairing*: step
  5.3 proves that `g ↦ ⟨g, ·⟩` is injective. Step 5.2 applies `KFiniteDual.mem_of_separating` to
  put the `U(n)`-finite functionals `Λ f` in its range. The same argument covers every
  `U(n)`-finite functional on `X(d)`, but the module does not state that identification as a
  separate theorem. Nothing is assumed as a hypothesis.

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
