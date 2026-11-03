# Truncated polynomial sections of formally smooth augmented algebras

Module `Langlands.GroupScheme.Rational.TorusUnipotence.TruncatedSection`, namespace
`Langlands.GroupScheme.TorusUnipotence`.

Let `k` be a field, `A` a commutative `k`-algebra with augmentation `ε : A →ₐ[k] k`, and
`I = ker ε`. Fix elements `z : σ → A` with `ε (z s) = 0` (`hz`) whose classes form a basis
`b : Basis σ k (I / I²)`, i.e. `cotangentMap ε (z s) = b s` (`hzb`). Write
`T_N = MvPolynomial σ k ⧸ (idealOfVars σ k) ^ N` for the truncated polynomial ring.

The module proves the following. If `A` is formally smooth over `k`, then evaluation at the `z s`
induces an isomorphism `T_N ≅ A ⧸ I ^ N`. The inverse gives an algebra map `τ : A → T_N` that is
characterized by polynomial approximation. For a graded `A`, `τ` sends homogeneous elements to
classes of weighted-homogeneous polynomials. This is the "formal coordinates at the identity"
input of `BigCell`.

## Definitions

* `truncVarIdeal σ k N`: the image of `idealOfVars σ k` in `T_N`.
* `truncEval z hz N : T_N →ₐ[k] A ⧸ I ^ N`: the map induced by evaluation `aeval z`, defined with
  `Ideal.Quotient.liftₐ`. `truncEval_mk` computes it on classes of polynomials (`rfl`).

## Statements

*Approximation.*

* `augmentation_aeval`: `ε (aeval z p) = constantCoeff p`.
* `exists_sub_aeval_mem_sq`: every `x ∈ I` agrees modulo `I²` with `aeval z q` for a linear
  polynomial `q`.
* `exists_sub_aeval_mem_pow_succ`: every `x ∈ I ^ m` agrees modulo `I ^ (m + 1)` with some
  `aeval z q`.
* `exists_sub_aeval_mem_pow z b hz hzb x n`: every `x ∈ A` agrees modulo `I ^ n` with some
  `aeval z p`.
* `map_eq_zero_of_mem_pow`: an algebra map `Ψ : A → T_N` with `Ψ (I) ⊆ truncVarIdeal` kills
  `I ^ N`.
* `idealOfVars_pow_le_comap`: `aeval z` sends `(idealOfVars) ^ N` into `I ^ N`.
* `mem_pow_of_map_eq_zero` (kernel criterion). Let `Ψ : A → T_N` satisfy
  `Ψ (z s) ≡ X s` modulo `truncVarIdeal ^ 2` and `Ψ (I) ⊆ truncVarIdeal`. Then `Ψ a = 0`
  implies `a ∈ I ^ N`.

*Lifting.*

* `exists_lift_of_cotangent`. Let `A` be formally smooth, `J` a nilpotent ideal of a `k`-algebra
  `B`, and `L : I / I² → B ⧸ J²` a linear map with values in the image of `J`. Then there is an
  algebra map `ψ : A → B` with `ψ a ≡ ε a + L (cotangentMap ε a)` modulo `J²`.
* `truncVarIdeal_pow`: `truncVarIdeal ^ N = ⊥`.
* `exists_truncated_lift`. If `A` is formally smooth, there is `ψ : A → T_N` with
  `ψ (z s) ≡ X s` modulo `truncVarIdeal ^ 2` and `ψ (I) ⊆ truncVarIdeal`.
* `quotientMap_aeval_surjective`, `quotientMap_aeval_injective`: `truncEval z hz N` is
  surjective, and injective if `A` is formally smooth.
* `exists_truncated_section`. If `A` is formally smooth, there is `τ : A →ₐ[k] T_N` such that
  `τ x = [p]` whenever `x - aeval z p ∈ I ^ N`.

*Grading.* Let `𝒜 : ι → Submodule k A` be a grading by an additive commutative monoid with
decidable equality, let `ε` vanish in nonzero degrees (`hε`), and let `z s ∈ 𝒜 (w s)`.

* `aeval_mem_of_isWeightedHomogeneous`: `aeval z` sends `w`-weighted-homogeneous polynomials of
  degree `d` into `𝒜 d`.
* `decompose_aeval`: the degree-`d` component of `aeval z p` is
  `aeval z (weightedHomogeneousComponent w d p)`.
* `augIdeal_isHomogeneous`, `augIdeal_pow_isHomogeneous`: `I` and its powers are homogeneous
  ideals.
* `exists_isWeightedHomogeneous_of_section`. Let `N ≠ 0`, let `τ` be as in
  `exists_truncated_section`, and let `a ∈ 𝒜 d`. Then `τ a = [p]` for some `p` that is
  weighted-homogeneous of degree `d` with `constantCoeff p = ε a`.

## Proof

*Approximation.* `exists_sub_aeval_mem_sq` expands the class of `x` in the basis `b`. Its
coordinates give a linear combination of the `z s` with the same class, so the difference lies
in `I²` (`cotangentMap_eq_zero_iff`). `exists_sub_aeval_mem_pow_succ` inducts on `m`, using
`Submodule.mul_induction_on` for `I ^ (m + 1) = I ^ m · I`. For a product `a c`, multiply the
approximations: `a c - q₁(z) q₂(z) = (a - q₁(z)) c + q₁(z) (c - q₂(z))`. The base case uses the
constant `ε x`. Summing the successive corrections gives `exists_sub_aeval_mem_pow`.

*Kernel criterion.* `Ψ` sends `I ^ N` into `truncVarIdeal ^ N = 0`. Given `Ψ a = 0`, choose `p`
with `a - aeval z p ∈ I ^ N`. Then `(Ψ ∘ aeval z) p = 0`. `Ψ ∘ aeval z` sends `X s` to
`X s` modulo `truncVarIdeal ^ 2`, so `Truncation.mem_pow_of_eq_zero` gives
`p ∈ (idealOfVars) ^ N`. Hence `aeval z p ∈ I ^ N` and `a ∈ I ^ N`.

*Lifting.* The map `a ↦ ε a + L (cotangentMap ε a)` is linear, sends `1` to `1`, and is
multiplicative. Multiplicativity follows from the Leibniz rule `cotangentMap_mul` and
`L t · L t' = 0`, since `J · J ⊆ J²`. So it is an algebra map `A → B ⧸ J²`, and
`Algebra.FormallySmooth.lift` lifts it through the nilpotent ideal `J²`. For
`exists_truncated_lift`, take `B = T_N`, `J = truncVarIdeal` (nilpotent by `truncVarIdeal_pow`)
and `L = b.constr (s ↦ [X s])`.

*Isomorphism.* Surjectivity follows from `exists_sub_aeval_mem_pow`. For injectivity, let
`aeval z p ∈ I ^ N`. With `ψ` from `exists_truncated_lift`, the composite `ψ ∘ aeval z` kills `p`
(`map_eq_zero_of_mem_pow`) and is the identity on the variables to first order, so
`p ∈ (idealOfVars) ^ N` by `Truncation.mem_pow_of_eq_zero`. The section `τ` is the inverse of
`AlgEquiv.ofBijective (truncEval z hz N)` composed with the quotient map `A → A ⧸ I ^ N`.

*Grading.* Evaluation of a monomial of `w`-weight `d` is a product of homogeneous elements and
lies in `𝒜 d` (`SetLike.prod_pow_mem_graded`). `decompose_aeval` follows by induction over
monomials (`MvPolynomial.induction_on'`). `I` is homogeneous because `ε` only sees the degree-zero
component (`augmentation_decompose_zero`), and products of homogeneous ideals are homogeneous.
For `exists_isWeightedHomogeneous_of_section`, take the degree-`d` component of
`a - aeval z p ∈ I ^ N`. It is `a - aeval z p_d`, where `p_d` is the weighted-homogeneous
component, and it still lies in `I ^ N`. So `τ a = [p_d]`. Applying `ε` (`N ≠ 0`, so
`I ^ N ⊆ I`) gives `constantCoeff p_d = ε a`.

## Provenance

This is the algebraic form of the standard fact that the completion of a smooth `k`-algebra at a
rational point is a power series ring. It is proved here as an internal lemma for the proof of
`Langlands.GroupScheme.RelativeRoot.TorusActionUnipotenceStatement`. No source states it in
this form.
