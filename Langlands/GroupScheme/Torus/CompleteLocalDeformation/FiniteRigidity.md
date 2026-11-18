# Rigidity of bialgebra maps over finite algebras over a noetherian local ring

This module is an internal helper for the proof of
`Langlands.GroupScheme.MultiplicativeTypeCompleteLocalDeformationStatement`. Its route is
our own. In Conrad's notes (Appendix B, B.3.2) homomorphisms out of a split group are
determined by their special fibres. This module gives that uniqueness in Hopf-algebra form
over any finite algebra over a noetherian local ring. Such an algebra need not be local, so
the result also applies to `C ⊗_A C` for a finite cover `A → C`, which is where descent needs
it. It deduces the result from the rigidity theorem `eq_of_coeff_sub_mem` of the module
`Langlands.GroupScheme.Torus.CompleteLocalDeformation.Rigidity`. Its other inputs are Krull's
intersection theorem from Mathlib and two lemmas on scalar extensions.

## Cocommutativity modulo an ideal

Every rigidity result here assumes that the source bialgebra is cocommutative modulo an
ideal `I`, written `comul b - comm (comul b) ∈ I • ⊤`. Here `comm` swaps the two factors
of `B ⊗ B`. The following lemmas supply this hypothesis.

- `isCocomm_of_coalgEquiv`: a coalgebra that is equivalent, by a coalgebra equivalence, to
  a cocommutative coalgebra is cocommutative (Mathlib's class `Coalgebra.IsCocomm`).
- `comul_one_tmul_baseChange`: for an `R`-bialgebra `C` and an `R`-algebra `S`, the
  comultiplication of `S ⊗[R] C` sends `1 ⊗ x` to the image of `1 ⊗ comul x` under Mathlib's
  `TensorProduct.AlgebraTensorModule.distribBaseChange`.
- `distribBaseChange_one_tmul_comm`: `distribBaseChange` turns the swap of `C ⊗ C` into the
  swap of `(S ⊗ C) ⊗[S] (S ⊗ C)`.
- `comul_sub_comm_mem_baseChange`: if `C` is cocommutative modulo `J • ⊤`, then `S ⊗[R] C`
  is cocommutative modulo `J.map (algebraMap R S) • ⊤`. The proof reduces to the generators
  `1 ⊗ c`, where the two lemmas above apply.
- `comul_sub_comm_mem_of_isCocomm`: if the reduction `(R ⧸ J) ⊗[R] C` is cocommutative,
  then `C` is cocommutative modulo `J • ⊤`. The proof uses `one_tmul_eq_zero_iff` and
  `comul_one_tmul` from the module `Lifting`.
- `comul_sub_comm_mem_of_bialgEquiv`: the same conclusion when the reduction is isomorphic as
  a bialgebra to a group algebra `(R ⧸ J)[N]` of an additive commutative monoid. Group
  algebras are cocommutative by Mathlib's instance `AddMonoidAlgebra.instIsCocomm`.

## Separation

- `eq_zero_of_mem_pow_of_le_jacobson`: in a noetherian ring, an element of every power of
  an ideal contained in the Jacobson radical is zero. This is Mathlib's
  `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson` applied to the ring as a module over itself.
- `eq_zero_of_mem_map_maximalIdeal_pow`: let `A` be a noetherian local ring with maximal
  ideal `𝔪` and `K` an `A`-algebra that is finite as an `A`-module. An element of `K` lying in
  every power of `𝔪 K = 𝔪.map (algebraMap A K)` is zero. The proof applies Mathlib's
  `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing` to the finite `A`-module `K`. Neither `K` nor
  `A` need be complete, and `K` need not be local.

## Rigidity

Throughout, `K` is a commutative ring, `N` an additive commutative group, `B` a commutative
`K`-bialgebra and `π π' : B →ₐc[K] K[N]` are bialgebra maps.

- `eq_of_sub_mem_smul_top`: if `K` is `I`-adically separated, `B` is cocommutative modulo
  `I`, and `π b - π' b ∈ I • ⊤` for every `b`, then `π = π'`. This is `eq_of_coeff_sub_mem`
  with the hypothesis on coefficients obtained by applying the coefficient forms `lcoeff n`.
- `eq_of_sub_mem_of_le_jacobson`: the same conclusion when `K` is noetherian and `I` lies in
  the Jacobson radical of `K`.
- `eq_of_sub_mem_map_maximalIdeal`: the same conclusion with `I = 𝔪 K`, when `K` is a
  finite algebra over a noetherian local ring `A` with maximal ideal `𝔪`.
- `eq_of_sub_mem_map_maximalIdeal_baseChange`: the case `B = K ⊗[A] C` for an
  `A`-bialgebra `C` that is cocommutative modulo `𝔪 • ⊤`. Bialgebra maps
  `K ⊗[A] C → K[N]` that agree modulo `𝔪 K` are equal.

## Use in the deformation proof

Let `A` be the complete local noetherian base and `C` the coordinate ring of `G`. Since the
special fibre of `G` is commutative, `C` is cocommutative modulo `𝔪`. Now let `K` be a finite
`A`-algebra over which `H` is diagonalizable, for example a finite étale splitting algebra or
its tensor square. Homomorphisms `H_K → G_K` then correspond to bialgebra maps
`K ⊗[A] C → K[M]`. By `eq_of_sub_mem_map_maximalIdeal_baseChange`, two such homomorphisms
with the same reduction modulo `𝔪 K` are equal. This gives uniqueness of lifts over the
splitting algebra, and the agreement of the two pullbacks to its tensor square, which descent
requires.
