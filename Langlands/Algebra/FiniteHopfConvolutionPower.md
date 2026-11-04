# Points of a finite commutative cocommutative Hopf algebra are killed by its rank

Author: Worker 1384.

This module proves a purely algebraic torsion statement. Let `k` be a field and `H` a
commutative Hopf algebra over `k` that is cocommutative (`Coalgebra.IsCocomm k H`) and
finite-dimensional (`Module.Finite k H`). Let `C` be a commutative `k`-algebra. Then

    FiniteHopfConvolutionPower.pow_finrank_eq_one C x : x ^ Module.finrank k H = 1

for every `x : WithConv (H →ₐ[k] C)`. Here powers and `1` are taken in Mathlib's
convolution monoid of `k`-algebra maps `H → C`, and `1` is the point `a ↦ ε(a) • 1`. In
geometric terms: if `G = Spec H` is a finite commutative group scheme of order
`n = dim_k H` over `k`, then every point of `G` with values in any commutative `k`-algebra
satisfies `x ^ n = 1`. The theorem `convPow_finrank_eq_one` is the same statement for the
underlying linear map `toConv x.toLinearMap` in the convolution ring `WithConv (H →ₗ[k] C)`.

## Provenance

The statement is the commutative case of Milne, *Algebraic Groups* (2017), Proposition 11.32
(§11.g, printed p. 221, PDF p. 237; source ID `milne-2017-algebraic-groups`). That
proposition says that if `G` is a finite group scheme of order `n` over a field `k`, then
for every `k`-algebra `R`, the order of every element of `G(R)` divides `n`. The order of
`Spec H` is `dim_k H`. Milne's proof, which follows Tate (1997), reduces to connected groups
and uses the regular representation in `GL_n`; it also covers noncommutative groups.

The proof implemented here does not follow Milne. It is a norm argument in convolution
rings, and it needs commutativity. Milne's notes after Corollary 11.33 (same page) attribute
the commutative statement over arbitrary bases to Deligne and cite Tate and Oort 1970,
p. 4. That text was not consulted, so this document does not claim the argument below is
theirs. Every step below is proved in the module.

The module is internal infrastructure for the proof of
`Langlands.GroupScheme.CentralIsogenyMaximalSplitTorusLiftStatement`. Its group-scheme form
is `Langlands.GroupScheme.CentralIsogeny.KernelTorsion`.

## Convolution rings and precomposition

Write `R = WithConv (H →ₗ[k] C)` and `R' = WithConv (H ⊗[k] H →ₗ[k] C)`, both with
Mathlib's convolution product. Both are commutative rings, because `H` and `H ⊗ H` are
cocommutative and `C` is commutative.

- `precomp h` is precomposition with a coalgebra morphism `h : M →ₗc[k] N`, as a ring
  morphism `WithConv (N →ₗ C) →+* WithConv (M →ₗ C)`. It preserves the unit because `h`
  preserves the counit. It preserves products by Mathlib's
  `LinearMap.convMul_comp_coalgHom_distrib`. This part only needs `M` and `N` to be
  coalgebras over a commutative ring.
- `sndCoalgHom k H : a ⊗ b ↦ ε(a) b` and `fstCoalgHom k H : a ⊗ b ↦ ε(b) a` are the
  coalgebra morphisms `H ⊗ H → H` built from the counit and the unitors.
- `sndAlgebra` makes `R'` an `R`-algebra through `precomp (sndCoalgHom k H)`. The module
  uses it as a local instance.

## The shear

- `shearCoalgHom k H` is the coalgebra morphism `a ⊗ b ↦ ∑ a b₍₁₎ ⊗ b₍₂₎`, built as
  `(μ ⊗ id) ∘ assoc⁻¹ ∘ (id ⊗ Δ)`. This needs cocommutativity, since only then is `Δ` a
  coalgebra morphism (`Coalgebra.comulCoalgHom`).
- `shearAlgHom k H` is the algebra morphism `a ⊗ b ↦ (a ⊗ 1) Δ(b)`, the tensor-product
  lift of `includeLeft` and `Bialgebra.comulAlgHom`. `shearCoalgHom_toLinearMap` shows the
  two shears have the same underlying linear map. Induction on `Δ(b)` reduces this to pure
  tensors.
- `sndCoalgHom_shear`: `snd ∘ shear = snd`. `fstCoalgHom_shear`: `fst(shear(a ⊗ b)) = a b`.
  Both reduce to the counit axioms `(ε ⊗ id) Δ = id` and `(id ⊗ ε) Δ = id`.
- `shearInvAlgHom k H` is the inverse shear `a ⊗ b ↦ (a ⊗ 1) ∑ S(b₍₁₎) ⊗ b₍₂₎`. It is not
  written with the antipode. Its restriction to the second factor is the convolution
  product `includeLeft⁻¹ * includeRight` in Mathlib's convolution group of algebra-map
  points `H → H ⊗ H`, and that group exists because the target `H ⊗ H` is a bialgebra.
  `postcomp F` is postcomposition with an algebra morphism `F`, as a monoid morphism of
  convolution monoids of points. `postcomp_inv` says it commutes with inverses for
  endomorphisms of `H ⊗ H`.
- `shearAlgHom_comp_shearInvAlgHom` and `shearInvAlgHom_comp_shearAlgHom`: the two maps are
  mutually inverse. Both are checked on the two tensor inclusions. On `includeRight` the
  check is a group identity among points `H → H ⊗ H`. It uses the TauCeti lemma
  `TauCeti.Bialgebra.comulPoint_eq_include_mul`: `Δ` as a point is
  `includeLeft * includeRight`.
- `shearRingEquiv C` is precomposition with the shear, as a ring automorphism of `R'`. Its
  inverse is precomposition with `shearInvAlgHom`. `shearAlgEquiv C` upgrades it to an
  `R`-algebra automorphism, by `sndCoalgHom_shear`.

## Freeness of `R'` over `R`

`coordEquiv C e` is an `R`-linear equivalence `R' ≃ₗ[R] (ι → R)` for a basis `e` of `H`
indexed by a finite type `ι`. It sends `φ` to the family of maps `b ↦ φ(e i ⊗ b)`. The
inverse is the tensor lift of the basis construction. `R`-linearity is
`precomp_snd_mul_apply_tmul`: `(ψ ∘ snd * φ)(a ⊗ b) = (ψ * φ(a ⊗ –))(b)`. Its proof uses
Mathlib's `Coalgebra.Repr` sums for `Δ(a)` and `Δ(b)` and the counit identity
`∑ ε(a₍₁₎) a₍₂₎ = a`. Taking `e = Module.finBasis k H` makes `R'` free over `R` of rank
`n = Module.finrank k H`.

## The norm argument (`convPow_finrank_eq_one`)

Let `x : H →ₐ[k] C`, `X = toConv x.toLinearMap ∈ R`, and `z = precomp fst X ∈ R'`, that is
`z(a ⊗ b) = ε(b) x(a)`.

1. `X` is a unit of `R`. Its inverse is `x ∘ S`, because `x ∘ (id * S) = x ∘ (η ε)` by
   `LinearMap.id_mul_antipode` and `LinearMap.algHom_comp_convMul_distrib`. Hence `z`, the
   image of `X` under a ring morphism, is a unit of `R'`.
2. Using the TauCeti convolution-tensor product `mulTensor`, `precomp snd X = mulTensor 1 X`
   and `z = mulTensor X 1`. So by `mulTensor_convMul`,
   `algebraMap R R' X * z = mulTensor X X`, the map `a ⊗ b ↦ x(a) x(b)`.
3. By `fstCoalgHom_shear` and multiplicativity of `x`, the shear automorphism sends `z` to
   `a ⊗ b ↦ x(a b) = x(a) x(b)`. That is, `shearAlgEquiv C z = algebraMap R R' X * z`.
4. Take the `R`-algebra norm `N = Algebra.norm R` of `R'`, computed in the basis obtained
   from `coordEquiv`. It is invariant under the algebra automorphism
   (`Algebra.norm_eq_of_algEquiv`), and `N(algebraMap X) = X ^ n`
   (`Algebra.norm_algebraMap_of_basis`). Hence `N(z) = X ^ n * N(z)`.
5. `N(z)` is a unit because `z` is, so `X ^ n = 1`.

`pow_finrank_eq_one` moves this to the convolution monoid of algebra-map points, by
injectivity of `AlgHom.toLinearMap` and Mathlib's `AlgHom.toLinearMap_convPow`.
