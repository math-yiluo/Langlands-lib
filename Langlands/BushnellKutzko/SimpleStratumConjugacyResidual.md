# The residual polynomial of a normalizing unit of degree zero

This is an internal step in the proof of the case `t = n − 1` of BK93 (2.6.1). Source:
Bushnell–Kutzko (1993), registered as `bushnell-kutzko-1993-admissible-dual-gln`,
printed pp. 83–84 (PDF pp. 95–96). The source compares the polynomials `φ_{α_i}` of the
two strata (p. 58). It then uses the normal forms (2.5.8) and (2.5.11). The Lean proof
instead uses the action on the layers `L_i/L_{i+1}` and the residual polynomial
constructed here. The notation is that of `SimpleStratumConjugacyUnits`.

## Results

- `aeval_symbolEq`: if `x ≡ y (mod 𝔓)` with `x, y ∈ 𝔄`, then `Q(x) ≡ Q(y) (mod 𝔓)` for
  every `Q ∈ 𝔬_F[X]`.
- `residueLayerHom_injective`: a unit of `𝔄` acts injectively on every layer.
- `residueLayerHom_aeval_eq_zero_or_injective`: if `z ∈ 𝔄` lies in a subalgebra `R`
  whose nonzero elements normalize the chain, then for every `Q ∈ 𝔬_F[X]` the reduction
  of `Q` evaluated at the layer action of `z` is zero or injective. This follows from
  `mem_one_or_shifts_zero`.
- `residueLayerHom_aeval`: this reduction is the layer action of `Q(z)`.
- `exists_residual_polynomial_of_normalizing`: let `z` be a unit of `𝔄` lying in such
  an `R`. There is a monic `Q ∈ 𝔬_F[X]` with unit constant coefficient and irreducible
  reduction such that `Q(z) ∈ 𝔓`.
- `aeval_mem_one_of_conj`: let `z₂ ∈ R ∩ 𝔄`, `Z ≡ z₂` and `g⁻¹ Z g ≡ z₁ (mod 𝔓)` for some
  `g`, and suppose `Q(z₁) ∈ 𝔓`. Then `Q(z₂) ∈ 𝔓`.

## Proofs

For the residual polynomial, let `ȳ` be the action of `z` on `L_0/L_1`. By the
dichotomy every element of `k_F[ȳ]` is zero or injective, so this algebra is a domain.
The minimal polynomial `p` of `ȳ` over `k_F` is therefore irreducible, and its constant
coefficient is nonzero because `ȳ ≠ 0`. A monic lift `Q` of `p` of the same degree
(`lifts_and_natDegree_eq_and_monic`) has unit constant coefficient. The layer action of
`Q(z)` on `L_0/L_1` is `p(ȳ) = 0`. So `Q(z)` is not a unit of `𝔄`, and the trichotomy
puts it in `𝔓`.

For the transfer, suppose `Q(z₂) ∉ 𝔓`. Then `Q(z₂)` is a unit of `𝔄`. Since
`Q(Z) ≡ Q(z₂)`, `Q(Z)` is a unit `W` of `𝔄`. But
`g⁻¹ W g = Q(g⁻¹ Z g) ≡ Q(z₁) ≡ 0 (mod 𝔓)`, which contradicts `conj_not_mem_one`.
