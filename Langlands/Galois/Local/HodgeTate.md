# Hodge-Tate decompositions of `ℓ`-adic representations of local Galois groups

Author: Worker 34. This module constructs the completed algebraic closure
`C_F` of a finite extension `F` of `ℚ_p`, the continuous action of
`Gal(F̄/F)` on it and the cyclotomic twists. It then defines what it means for
a continuous representation of `Gal(F̄/F)` with coefficients in a
`ℚ_p`-algebra `Λ` to have a Hodge-Tate decomposition with prescribed twists
and multiplicities. It is the Hodge-Tate input of Taylor's multiplicity
removal (`Langlands/Galois/TaylorMultiplicityRemovalStatement`).

## Source

M. Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper
half spaces; elaboration of Carayol's program*, Invent. Math. 129 (1997),
75-119, §3, printed p.103. Registered original `harris-1997-drinfeld-cohomology`,
SHA256 `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.
In the sketch of Taylor's argument (checked against the page image), `C_v` is
"the completion of the algebraic closure of `𝒦_v`", and Faltings' Hodge-Tate
theorem gives, "as `Γ_v`-modules",

`W_λ ⊗_{ℚ_ℓ} C_v ≅ ⊕_{i=1}^{n} L_λ^m ⊗_{ℚ_ℓ} C_v(1 - i)`,

where "`C_v(1 - i)` is the `Γ_v`-module corresponding to the `(1 - i)`th power
of the cyclotomic character" and `Γ_v` is a decomposition group at `v`. Harris (1999), *Galois properties of
cohomological automorphic forms on GL(n)*, printed pp.313-314 (registered
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`), uses the
same input for general coefficient systems, whose twists are distinct but not
consecutive; the definition therefore allows arbitrary twists `k i`.

## Definitions

Throughout, `p` is a prime and `F` a field with a `ℚ_p`-algebra structure,
finite-dimensional over `ℚ_p` where stated. All names are in
`Langlands.GaloisRepresentation.HodgeTate`.

- `Closure p F`: Mathlib's algebraic closure `AlgebraicClosure F`, with its
  field and algebra structures, made a normed field by the spectral norm over
  `ℚ_p` (`spectralNorm.normedField`), the unique norm extending the `p`-adic
  norm. This follows Mathlib's construction of `PadicAlgCl p`.
- `Closure.galois σ`: an element `σ` of `Field.absoluteGaloisGroup F`
  (Mathlib's `Gal(F̄/F)` for the same algebraic closure) as an automorphism of
  `Closure p F`.
- `Completed p F`: the completion `C_F` of `Closure p F`, as
  `PadicComplex p` is the completion of `PadicAlgCl p`. It is a normed field
  and a `ℚ_p`-algebra.
- `galoisRingHom p σ : C_F →+* C_F`: the continuous extension of `σ`
  (`UniformSpace.Completion.mapRingHom`), which exists because `σ` is an
  isometry. `galoisLinear p σ` is the same map as a `ℚ_p`-linear map.
- `cyclotomic p σ : C_F`: the image in `C_F` of Mathlib's `p`-adic cyclotomic
  character `cyclotomicCharacter (Closure p F) p` evaluated at `σ`.
- `HasHodgeTateDecomposition p F Λ A n m k`, for a field `Λ` with a topology
  and a `ℚ_p`-algebra structure, a continuous representation
  `A : Objects F Λ` on the finite-dimensional `Λ`-space `V`, natural numbers
  `n` and `m`, and twists `k : Fin n → ℤ`. With `V` regarded as a
  `ℚ_p`-vector space through `ℚ_p → Λ`, it asserts a `C_F`-linear isomorphism

  `Φ : (Fin n → Fin m → C_F ⊗_{ℚ_p} Λ) ≃ C_F ⊗_{ℚ_p} V`

  such that
  - `Φ` commutes with the action of every `a ∈ Λ` on the second tensor
    factors (`1 ⊗ a` on both sides), and
  - for every `σ ∈ Gal(F̄/F)`, `Φ` carries the action
    `x ↦ χ(σ)^{k i} · (σ ⊗ 1)(x)` on the summands of index `i` to the action
    `σ ⊗ ρ(σ)` on `C_F ⊗_{ℚ_p} V`.

  The source of `Φ` is `⊕_{i<n} ((C_F ⊗_{ℚ_p} Λ)(k i))^m`, where
  `C_F(j)` is `C_F` with `σ` acting by `χ(σ)^j σ`. Taylor's decomposition is
  the case `k i = -i` (the twists `C_v(1 - i)` for `i = 1, …, n`).

## Proved properties

- `Closure.norm_galois`, `Closure.isometry_galois`: every element of
  `Gal(F̄/F)` preserves the spectral norm (Mathlib's
  `spectralNorm_eq_of_equiv`), so it is an isometry.
- `galoisRingHom_coe`: the extension agrees with `σ` on `F̄`.
- `galoisRingHom_mul`, `galoisRingHom_one`: the extensions form an action of
  `Gal(F̄/F)` on `C_F`; `continuous_galoisRingHom`: each is continuous.
- `galoisLinear` is `ℚ_p`-linear because `σ` fixes `F ⊇ ℚ_p`.
- `Closure.galois_apply_of_pow_eq_one`: `σ` raises every `p^n`-th root of
  unity of `F̄` to the power `χ(σ) mod p^n`, so `cyclotomic` is the genuine
  `p`-adic cyclotomic character (Mathlib's `cyclotomicCharacter.spec`, with
  the instances `Closure.isAlgClosed`, `Closure.charZero` and
  `Closure.hasEnoughRootsOfUnity`).
- `cyclotomic_mul`, `cyclotomic_ne_zero`: the character is multiplicative
  with nonzero values.

## Conventions

- `C_F(j)` is the `j`th power of the cyclotomic character, as in Harris's
  `C_v(1 - i)`. With this convention a summand `C_F(k i)` contributes the
  Hodge-Tate weight `-k i` in the convention "`(V ⊗ C_F(j))^{Gal} ≠ 0`"; no
  other weight convention is used here.
- The decomposition is required to be `Λ`-linear. The definition allows any
  field `Λ` with a topology and a `ℚ_p`-algebra structure, and it asserts no
  splitting of `C_F ⊗_{ℚ_p} Λ`. When `Λ` is a finite extension of `ℚ_p`, which
  is the case of the completions `L_λ` used by
  `Langlands/Galois/TaylorMultiplicityRemovalStatement`, `C_F ⊗_{ℚ_p} Λ` is a
  product of copies of `C_F` indexed by the `ℚ_p`-embeddings `Λ → C_F`, and
  `Λ`-linearity says that every embedding sees each twist exactly `m` times.
  (For infinite `Λ`, such as an algebraic closure of `ℚ_p`, this product
  description fails, and the definition is not used for such `Λ` here.) This is
  what Taylor's argument uses: the summands `L_λ^m ⊗_{ℚ_ℓ} C_v(1 - i)` are
  `L_λ`-stable, and the Sen operator acting by `1 - i` on them is
  `L_λ`-linear. A decomposition of `ℚ_ℓ`-representations only would not give
  his weight-space dimensions.
- The definition asserts an isomorphism; it does not choose one, and it is not
  required to be unique.

## Scope

No Hodge-Tate theorem is proved or asserted here. In particular, Faltings'
theorem that the étale cohomology of the relevant Shimura varieties with
coefficient systems of geometric origin is Hodge-Tate is not stated in this
module. The Sen operator and the Zariski closure of the image, which Taylor's
argument uses, are not formalized.
