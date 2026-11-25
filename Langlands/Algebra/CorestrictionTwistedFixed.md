# The tensor descent of a twisted-fixed matrix form

This module computes the corestriction (tensor descent) of a central simple
algebra given in matrix form. It is the algebra side of this development's
proof of the transfer law for the Tits obstruction (Tits, *Représentations
linéaires irréductibles d'un groupe réductif sur un corps quelconque*,
J. reine angew. Math. 247 (1971), Proposition 5.1, printed p. 207 / PDF
p. 12). The corestriction is the published tensor descent `corAlg`/`corCSAOf`
of `Langlands/Algebra/BrauerCorestriction`, which follows Tits's
§5.3 (printed p. 208 / PDF p. 13).

**Main result.** Let `A` be a central simple `E`-algebra, realized inside
`M_n(K)` as a form fixed by twisting matrices `Q h` for `h ∈ Gal(K/E)`.
Then the tensor descent of `A` from `E` to `k` is isomorphic to the
`k`-algebra fixed by the induced twisting matrices `C τ`
(`Algebra/KroneckerInduction`), for `τ ∈ Gal(K/k)`. The two therefore have
the same Brauer class. Tits proves Proposition 5.1 cohomologically. This
matrix formulation, and its proof by a dimension count, are this
development's own.

Everything is in the namespace `Langlands.Algebra.CorestrictionTwistedFixed`.

## Setting

- `k`, `E`, `N`, `K` are fields in one universe with `k`-algebra structures,
  `E → K` and `N → K`, and scalar towers `k → E → K` and `k → N → K`.
- `N/k` is normal, and finite Galois where the descent is used. `K/k` is
  Galois, possibly infinite, where dimensions are counted. `E/k` is finite.
- `A` is an `E`-algebra, with an `E`-algebra map `j : A → M_n(K)` (`n` a
  nonempty finite type).
- The embeddings `E →ₐ[k] N` are indexed by `Fin m` through an equivalence
  `e`. Each embedding `σ` has a chosen extension `ε σ ∈ Gal(K/k)`:
  `hε : ε σ (x) = σ (x)` for `x ∈ E`, with `E` and `N` viewed inside `K`.
- `Q : Gal(K/E) → M_n(K)` with `hj : Q h · j a = h(j a) · Q h` for all
  `h` and `a`. That is, `j(A)` lies in the `E`-algebra fixed by `Q`.

The Library's notation (`Langlands/Algebra/BrauerCorestriction/Construction`)
is used throughout: `Twist σ` is `N` viewed as an `E`-algebra through `σ`,
`Conj A σ = Twist σ ⊗_E A` is the conjugate `A^σ`, and
`ConjTensor k E N A = ⨂_N σ, A^σ`. `actMap A g` is the action of
`g ∈ Gal(N/k)`, which moves the factor at `σ` to the factor at `g σ`, and
`galPerm g` is the permutation `σ ↦ g ∘ σ`. `corAlg k E N A` is the fixed
`k`-subalgebra.

## Declarations

### Entrywise automorphisms and the Library's Kronecker product

- `map_mul_algEquiv`, `map_add_algEquiv`, `map_smul_algEquiv`,
  `piKronecker_map_algEquiv`: entrywise application of a `K`-automorphism
  `τ`, given as an `AlgEquiv`, commutes with products, sums, scalar multiples
  (with `c` replaced by `τ c`) and Kronecker products. These are the
  ring-homomorphism lemmas of Mathlib and `KroneckerInduction`, applied to
  the coercion of `τ`.
- `kroneckerMultilinear_eq_piKronecker`: the published Kronecker product
  `Langlands.BrauerCorestriction.kroneckerMultilinear F D m` of a family of
  `Fin m`-indexed matrices over a field `F` is `piKronecker`. This holds by
  definition. `piKronecker` (`Algebra/KroneckerInduction`) generalizes it to
  arbitrary index types and commutative coefficient rings.

### The factor maps (section `Factor`)

- `twistVal σ : Twist σ →+* N`: the identity of `N`, which makes the
  coercion from the twisted copy explicit (`twistVal_smul`: `r • x` goes to
  `σ r · x`; `twistVal_algebraMap`).
- `factorAddHom j σ s hs`, `factor j σ s hs : A^σ →ₐ[N] M_n(K)`: for an
  extension `s ∈ Gal(K/k)` of `σ`, the map `x ⊗ a ↦ x · s(j a)`
  (`factor_tmul`). It is defined on the tensor product by
  `TensorProduct.liftAddHom`. The map is balanced:
  `(r • x) ⊗ a ↦ σ(r) x · s(j a) = x · s(j (r a))`, because `s` extends
  `σ`. Multiplicativity is checked on pure tensors by induction, and
  `N`-linearity is the `algebraMap` computation.
- `factor_conjMap` (**factorwise Galois intertwining**): let `τ ∈ Gal(K/k)`
  restrict to `g` on `N`, with `g ∘ σ = σ'`. Let `s` and `s'` extend `σ` and
  `σ'`, and let `h₀ ∈ Gal(K/E)` satisfy `τ s = s' h₀`. If
  `Q h₀ · j a = h₀(j a) · Q h₀` for all `a`, then for `y ∈ A^σ`

  `s'(Q h₀) · factor σ' (conjMap g y) = τ(factor σ y) · s'(Q h₀)`.

  On `x ⊗ a`: the scalar part becomes `τ(x)` (`restrictNormal_commutes`).
  The matrix part follows by applying `s'` to the twisting equation for `h₀`
  and using `s' ∘ h₀ = τ ∘ s`.

### The matrix realization (section `Corestriction`)

- `corMatrixMultilinear`: the `N`-multilinear map
  `(y_i)_{i : Fin m} ↦ piKronecker (i ↦ factor_{e⁻¹ i} (y_i))`
  (`corMatrixMultilinear_apply`).
- `reindexAlgHom`: reindexing `⨂_σ A^σ` along `e` as an `N`-algebra map
  (Library `PiTensorSemilinear.reindex_one`, `reindex_mul`).
- `corMatrixHom : ⨂_σ A^σ →ₐ[N] M_{Fin m → n}(K)`: the realization. It is
  `PiTensorProduct.liftAlgHom` of `corMatrixMultilinear`, which is
  multiplicative by `piKronecker_mul` and `piKronecker_one`, composed with
  `reindexAlgHom`. On pure tensors,
  `corMatrixHom (⨂_σ z_σ) = piKronecker (i ↦ factor_{e⁻¹ i} (z_{e⁻¹ i}))`
  (`corMatrixHom_tprod`).
- `stabCorrection ε hε τ σ ∈ Gal(K/E)`: the correction
  `ε(gσ)⁻¹ · τ · ε(σ)`, where `g = τ|_N`. It fixes `E` because both
  `τ ε(σ)` and `ε(gσ)` restrict to `g ∘ σ` on `E`.
  `stabCorrection_restrictScalars`: `τ · ε σ = ε (g σ) · stabCorrection τ σ`.
- `inductionData e ε hε : InductionData k E K (Fin m)`: the lifts
  `ε (e⁻¹ i)`, the permutation `e ∘ galPerm (τ|_N) ∘ e⁻¹`, and the
  stabilizer corrections. `inductionData_perm_symm_apply` computes the
  inverse permutation.
- `inducedMatrix_mul_corMatrixHom` (**Galois intertwining of the
  realization**): for `τ ∈ Gal(K/k)`, `C τ = inducedMatrix (inductionData …) Q τ`
  and every `v ∈ ⨂_σ A^σ`,

  `C τ · corMatrixHom (actMap (τ|_N) v) = τ(corMatrixHom v) · C τ`.

  Both sides are additive in `v`, so it suffices to treat `r • ⨂_σ z_σ`.
  `actMap_tprod` computes the action on pure tensors. The scalar becomes
  `τ(r)` on both sides. For the Kronecker products, `piKronecker_intertwine`
  applies with the factorwise identities given by `factor_conjMap`.
- `corMatrixHom_mem_twistedFixed`: if `v ∈ corAlg k E N A`, then
  `corMatrixHom v` lies in `twistedFixed C`
  (`Algebra/GaloisTwistedMatrix`). Here `actMap (τ|_N) v = v`
  (`mem_corAlg`).

### Dimension (section `Dimension`)

Here `E/k` is finite, `A` is central simple and finite-dimensional over `E`,
`n` is nonempty, `N/k` is finite Galois and `K/k` is Galois.

- `corAlgHom : corAlg k E N A →ₐ[k] M_{Fin m → n}(K)`: the restriction of
  `corMatrixHom` to the descended algebra (`corAlgHom_apply`).
- `corAlgHom_range_le`: its range lies in `twistedFixed C`.
- `corAlgHom_injective`: the descended algebra is simple
  (`isSimpleRing_corAlg`), and the matrix algebra is nontrivial.
- `finrank_corAlg_eq_card`: if `dim_E A = |n|²`, then
  `dim_k corAlg = (|n|^m)²`. This is `finrank_corAlg_eq_pow` together with
  `m = #(E →ₐ[k] N)`.
- `span_corAlgHom_range`: if every `Q h` is invertible and
  `dim_E A = |n|²`, the range spans `M_{Fin m → n}(K)` over `K`. Take a
  `k`-basis of the range. It lies in `twistedFixed C` with invertible `C τ`
  (`isUnit_inducedMatrix`), so it stays `K`-linearly independent
  (`linearIndependent_of_le_twistedFixed`). Its size is the range's dimension,
  `(|n|^m)²` by injectivity, which is the `K`-dimension of the matrix algebra.
- `span_twistedFixed_inducedMatrix`: hence `twistedFixed C` spans the matrix
  algebra too.
- `corAlgHom_range_eq`: the range is all of `twistedFixed C`. Both have
  `k`-dimension `(|n|^m)²`: the range by injectivity, and `twistedFixed C`
  by `GaloisTwistedMatrix.finrank_eq`, using the previous lemma.
- `corAlgEquivTwistedFixed : corAlg k E N A ≃ₐ[k] twistedFixed C`: the
  isomorphism `AlgEquiv.ofInjective` followed by the equality of
  subalgebras.

### Brauer class (section `Brauer`)

- `classOf_corCSAOf_eq`: for a central simple `E`-algebra `A` (`CSA E`) with
  the data above, invertible `Q h` and `dim_E A = |n|²`, the Brauer class of
  the tensor descent `corCSAOf k E N A` is the class of
  `toCSA C (twistedFixed C)`. It follows from `corAlgEquivTwistedFixed` by
  `Brauer.classOf_eq_of_algEquiv`.

## Scope

- No hypothesis on the characteristic or on the size of `k` is used. Tits's
  infiniteness assumption in §5.3 does not appear.
- `N` need not contain a normal closure of `E/k`. The identification of
  `corCSAOf k E N A` with the corestriction `cor` of the Brauer class of `A`,
  when `N` has `[E : k]` embeddings of `E`, is the published
  `cor_mk_eq_of_closure`; it is not restated here.
- This module makes no statement about representations or Tits algebras. The
  transfer law itself is not proved here.
