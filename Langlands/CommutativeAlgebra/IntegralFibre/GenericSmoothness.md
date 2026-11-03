# Generic smoothness of geometrically integral fibres

This module proves one step of the proof of
`Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement` (Stacks Project, Tag 05FT).
For a flat finitely presented `R`-algebra `S` whose fibres are geometrically integral, every
prime of `R` is the image of a point of the smooth locus of `S`: the generic point of the fibre.
The geometric hypothesis enters in the algebraic form "`K ⊗[R] S` is a domain for every field
`K` over `R`", which `Langlands.CommutativeAlgebra.isDomain_tensor_of_geometricallyIntegral`
derives from the scheme-theoretic one.

## Statements

All names are in the namespace `Langlands.CommutativeAlgebra`.

- `linearIndependent_pow_of_isReduced_tensor`: let `k` be a field of prime characteristic `p` and
  `T` a commutative `k`-algebra such that `AlgebraicClosure k ⊗[k] T` is reduced. If a finite
  family `t : ι → T` is `k`-linearly independent, then so is `fun i ↦ t i ^ p`.
- `formallySmooth_of_isFractionRing`: let `k` be a field, `T` a domain of finite type over `k`
  such that `AlgebraicClosure k ⊗[k] T` is reduced, and `L` a fraction field of `T`, with `k`,
  `T` and `L` forming a scalar tower. Then `L` is formally smooth over `k`.
- `isSmoothAt_of_formallySmooth_localization_fiber`: let `S` be a flat finitely presented
  `R`-algebra, `p` a prime of `R` and `Q` a prime of the fibre `p.Fiber S = κ(p) ⊗[R] S`. If
  `Localization.AtPrime Q` is formally smooth over `κ(p)`, then `S` is smooth over `R` at the
  prime `Q.comap includeRight` of `S` below `Q` (`Algebra.IsSmoothAt`).
- `exists_mem_smoothLocus_comap_eq`: let `R` and `S` be commutative rings in one universe `u`
  and `S` a flat finitely presented `R`-algebra such that `K ⊗[R] S` is a domain for every field
  `K : Type u` with an `R`-algebra structure. Then for every `p : PrimeSpectrum R` there is
  `q ∈ Algebra.smoothLocus R S` with `PrimeSpectrum.comap (algebraMap R S) q = p`.

## Proofs

`linearIndependent_pow_of_isReduced_tensor`. Write `K = AlgebraicClosure k` and let
`∑ j, g j • t j ^ p = 0` with `g j ∈ k`. Choose `b j ∈ K` with `b j ^ p = g j`
(`IsAlgClosed.exists_pow_nat_eq`) and put `x = ∑ j, b j ⊗ₜ t j`. The ring `K ⊗[k] T` has
characteristic `p` (or is zero), so `sum_pow_char` gives
`x ^ p = ∑ j, (g j • 1) ⊗ₜ t j ^ p = 1 ⊗ₜ ∑ j, g j • t j ^ p = 0`, and reducedness gives
`x = 0`. Since `K` is flat over `k`, the family `1 ⊗ₜ t j` is `K`-linearly independent
(`Module.Flat.linearIndependent_one_tmul`), so every `b j` is zero, hence every `g j` is zero.

`formallySmooth_of_isFractionRing`. `L` is essentially of finite type over `k`, as a
localization of the finite type algebra `T`. In characteristic zero `k` is perfect and Mathlib's
instance `Algebra.FormallySmooth.of_perfectField` applies. In characteristic `p` the proof checks
the hypothesis of `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType`:
for every finite `k`-linearly independent set `s ⊆ L`, the `p`-th powers of its elements are
`k`-linearly independent. Clear denominators with
`IsLocalization.exist_integer_multiples_of_finset`: there are a nonzero `d ∈ T` and `t a ∈ T`
with `t a = d * a` in `L` for `a ∈ s`. Multiplication by `d` is injective on `L` and `T → L` is
injective, so the `t a` are linearly independent in `T`. By the previous lemma the `t a ^ p` are
linearly independent, and `t a ^ p = d ^ p * a ^ p` together with injectivity of multiplication
by `d ^ p` shows that the `a ^ p` are linearly independent. The resulting separating
transcendence basis gives formal smoothness by
`Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable`.

`isSmoothAt_of_formallySmooth_localization_fiber`. The proof follows Mathlib's
`Algebra.IsSmoothAt.of_formallySmooth_fiber` line by line, with one change: Mathlib assumes the
whole fibre `p.Fiber S` is formally smooth over `κ(p)`, while here only its localization at `Q`
is. Let `q = Q.comap includeRight`, `Rp = R_p`, `Sp` the localization of `S` at the image of
`R \ p` and `Sq = S_q`. As in Mathlib, `Sq` is an `Rp`-algebra and a localization of `Sp`, and
`Sp` is finitely presented over `Rp`. The fibre of `Rp → Sq` is identified with the localized
fibre by the chain of `Rp`-algebra isomorphisms
`Localization.AtPrime Q ≃ Sq ⧸ p Sq` (`Ideal.Fiber.localizationAlgEquivQuotient`),
`Sq ⧸ p Sq = Sq ⧸ m_Rp Sq` (`Localization.AtPrime.map_eq_maximalIdeal`),
`Sq ⧸ m_Rp Sq ≃ Sq ⊗[Rp] κ(Rp)` (`Algebra.TensorProduct.quotIdealMapEquivTensorQuot`) and
`Algebra.TensorProduct.comm`. Because `Rp → κ(Rp)` is surjective, the composite is also
`κ(Rp)`-linear (`AlgEquiv.extendScalarsOfSurjective`), so `κ(Rp) ⊗[Rp] Sq` is formally smooth
over `κ(Rp)`. `Algebra.FormallySmooth.of_formallySmooth_residueField_tensor` (flatness of `S`
over `R` is used here) makes `Sq` formally smooth over `Rp`, and composing with the localization
`R → Rp` gives `Algebra.IsSmoothAt R q`. The proof is compiled with
`backward.isDefEq.respectTransparency` disabled, as Mathlib does for the analogous isomorphism
in `Mathlib/RingTheory/LocalRing/ResidueField/Fiber.lean`.

`exists_mem_smoothLocus_comap_eq`. Let `k = κ(p)` and `T = p.Fiber S = k ⊗[R] S`. The
hypothesis with `K = k` makes `T` a domain, so `Q = ⊥` is a prime of `T` and
`Localization.AtPrime Q` is a fraction field of `T` (`Ideal.primeCompl_bot`). The hypothesis
with `K = AlgebraicClosure k` makes `AlgebraicClosure k ⊗[R] S` a domain, and
`Algebra.TensorProduct.cancelBaseChange` identifies it with `AlgebraicClosure k ⊗[k] T`, which
is therefore reduced. `formallySmooth_of_isFractionRing` makes `Localization.AtPrime Q` formally
smooth over `k`, and `isSmoothAt_of_formallySmooth_localization_fiber` puts
`q = Q.comap includeRight` in the smooth locus. Every prime of the fibre lies over `p`
(a Mathlib instance), so `q` lies over `p`, which is the equation
`PrimeSpectrum.comap (algebraMap R S) q = p`.

## Provenance

The first lemma is the implication (4) ⇒ (2) of Stacks Project, Lemma 10.44.2 (Tag 030W),
with geometric reducedness tested only against the algebraic closure; the second combines it with
Mathlib's separably-generated criterion, which Mathlib attributes to the same tag. The third is a
variant of Stacks Project, Lemma 10.137.16 (Tag 00TF), which assumes smoothness of the fibre at
the prime only; its Lean proof adapts Mathlib's `Algebra.IsSmoothAt.of_formallySmooth_fiber`.
The final statement is the generic smoothness step of Worker 281's route to Tag 05FT: Worker 281
proposed the statement and the route through separability, and Worker 928 wrote the Lean proof.
The module is internal to the project.
