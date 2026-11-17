# Lifting split bialgebras through nilpotent thickenings

Worker 748.

This module is an internal helper for the proof of
`Langlands.GroupScheme.MultiplicativeTypeCompleteLocalDeformationStatement` (Conrad,
*Reductive group schemes*, Appendix B, B.3.2). The proof uses it for the following step: over
an Artinian quotient of the base, a flat deformation of a split diagonalizable group is again
split. The route is our own. Group-like elements are lifted with idempotents of the
convolution ring of linear forms, not with deformation theory.

It imports the helper modules `CompleteLocalDeformation.Rigidity` (for `ValuesIn` and the
convolution lemmas) and `CompleteLocalDeformation.OpenClosed` (for `map_mem_smul_top` and
`form_mem_of_mem_smul_top`). It also imports the published modules
`Langlands.Algebra.NilpotentModuleFiniteness` (for
`Langlands.Algebra.eq_top_of_sup_smul_eq_top_of_nilpotent`) and, transitively,
`Langlands.Algebra.GroupAlgebraCoaction` (for `conv`, `ract`, `ract_ract`,
`lTensor_ract_comul`, `counit_ract`). From Mathlib it uses the convolution ring
`WithConv (C →ₗ[R] A)`, idempotent lifting along nil ideals
(`exists_isIdempotentElem_eq_of_ker_isNilpotent`), flatness, and the bialgebra structure on
`AddMonoidAlgebra`.

Throughout, `R` is a commutative ring, `J` an ideal of `R`, `IsNilpotent J` says `J ^ n = 0`
for some `n`, and "modulo `J`" for an element `x` of an `R`-module `M` means
`x ∈ J • (⊤ : Submodule R M)`.

## Module lemmas

These hold for an `R`-module `C`.

- `finsupp_mem_smul_top J k hk`: a finitely supported `k : ι →₀ R` with all values in `J` lies
  in `J • ⊤`.
- `mem_smul_ker_of_flat J Φ hΦ hk hkJ`: if `C` is flat, `Φ : F → C` is surjective, `Φ k = 0`
  and `k ∈ J • ⊤`, then `k ∈ J • ker Φ`. The proof tensors the exact sequence
  `ker Φ → F → C → 0` with `R ⧸ J`.
- `le_of_le_sup_smul_of_isNilpotent J hJ N V h`: Nakayama's lemma for a nilpotent ideal and
  arbitrary submodules, `V ≤ N ⊔ J • V → V ≤ N`.
- `linearIndependent_of_flat_of_isNilpotent J hJ y hspan hind`: if `C` is flat and
  `J` nilpotent, and the family `y : ι → C` spans `C` modulo `J` (`hspan`) and is linearly
  independent modulo `J` (`hind`: a combination `∑ c i • y i` that is `0` modulo `J` has all
  `c i ∈ J`), then `y` is linearly independent and spans `C`. The span follows from
  Nakayama. For independence, the kernel `K` of `Finsupp.linearCombination R y` satisfies
  `K ≤ J • K` by `hind` and `mem_smul_ker_of_flat`, so `K = 0` by Nakayama.
- `one_tmul_eq_zero_iff J x`: `1 ⊗ x = 0` in `(R ⧸ J) ⊗ M` if and only if `x ∈ J • ⊤`.
- `exists_one_tmul_eq J t`: every element of `(R ⧸ J) ⊗ M` is `1 ⊗ x` for some `x`.
- `one_tmul_smul J r x`: `1 ⊗ (r • x) = (r mod J) • (1 ⊗ x)`.

## Convolution lemmas

Here `C` is an `R`-coalgebra.

- `ofConv_mul f g`: the product of `WithConv (C →ₗ[R] R)` is the convolution `conv` of
  `GroupAlgebraCoaction`.
- `convReduce J`: the ring map `WithConv (C →ₗ[R] R) →+* WithConv (C →ₗ[R] R ⧸ J)` that
  composes a linear form with the quotient map (a definition). `convReduce_apply` evaluates
  it, and `convReduce_eq_zero_iff` says that its kernel consists of the forms with values in
  `J` (`ValuesIn J`).
- `isNilpotent_of_valuesIn J hJ f hf`: a form with values in a nilpotent ideal is nilpotent
  in the convolution ring, since `f ^ k` has values in `J ^ k`.
- `valuesIn_of_span J hsp f h`: a linear form with values in `J` on a spanning family has all
  its values in `J`.
- `exists_conv_idempotent_lift J hJ χ₀ h`: if `conv χ₀ χ₀ - χ₀` has values in the nilpotent
  ideal `J`, there is a `χ` with `conv χ χ = χ` and `χ - χ₀` with values in `J`. The proof
  applies Mathlib's idempotent lifting to `convReduce J`, whose kernel is nil by the two
  previous lemmas.

## Lifting group-like elements

Here `C` is an `R`-coalgebra, `J` is nilpotent, `y : N → C` spans `C`, and each `y c` is
group-like modulo `J`: `comul (y c) - y c ⊗ y c ∈ J • ⊤`.

- `ract_eq_smul_of_idempotent J hJ hsp hy a hχχ hχy`: let `χ` be a convolution idempotent
  with `χ (y c) ≡ (if c = a then 1 else 0)` modulo `J` for all `c`. Then
  `ract χ (y a) ≡ y a` modulo `J`, and every value `ract χ x` is a scalar multiple of
  `ract χ (y a)`. The map `ract χ` is idempotent (`ract_ract`). It sends `y c` into `J • ⊤`
  for `c ≠ a`, so its range lies in `span {ract χ (y a)} ⊔ J • range` and Nakayama applies.
- `isGroupLikeElem_smul_of_ract χ y₀ hPV hui`: if every `ract χ x` is a multiple of
  `g' = ract χ y₀` and `ui * counit g' = 1`, then `ui • g'` is group-like. Indeed
  `comul g' = (id ⊗ ract χ) (comul y₀)` (`lTensor_ract_comul`) has the form `w ⊗ g'`, and the
  counit axiom gives `w = ui • g'`.
- `eq_of_isGroupLikeElem_of_ract J hJ hχχ hg hχ1 hPV hh hhy`: let `χ` be a convolution
  idempotent with `χ y₀ ≡ 1` modulo `J`, and suppose every `ract χ x` is a multiple of a
  group-like `g`. Then every group-like `h ≡ y₀` modulo `J` equals `g`. On a group-like `h`
  the value `χ h` is an idempotent of `R` that is `≡ 1` modulo the nilpotent `J`, so
  `χ h = 1`. Hence `ract χ h = h = r • g`, and the counit gives `r = 1`.
- `exists_isGroupLikeElem_sub_mem J hJ hli hsp hy a`: if moreover `y` is linearly
  independent (so `y` is a basis), then `y a` is congruent modulo `J` to a group-like element
  `g`, and every group-like element congruent to `y a` modulo `J` equals `g`. The coordinate
  form `χ₀` of `y a` is a convolution idempotent modulo `J`. It is lifted to `χ` by
  `exists_conv_idempotent_lift`. Then `g = ui • ract χ (y a)`, where `ui` is the inverse of
  `counit (ract χ (y a)) = χ (y a) ≡ 1`.

## Bialgebra results

Here `C` is a commutative `R`-bialgebra.

- `mul_mem_smul_top J hx z`: `J • ⊤` is closed under multiplication by elements of `C`.
- `exists_bialgEquiv_of_isNilpotent J hJ y hspan hind hcomul hmul`: let `C` be flat, `J`
  nilpotent and `N` an additive commutative monoid. Let `y : N → C` span `C` modulo `J`, be
  linearly independent modulo `J` (as above), be group-like modulo `J`, and be
  multiplicative modulo `J` (`y a * y b - y (a + b) ∈ J • ⊤`). Then there is a bialgebra
  isomorphism `θ : C ≃ₐc[R] AddMonoidAlgebra R N` with
  `θ (y a) - single a 1 ∈ J • ⊤` for all `a`. The lifts `g a` from
  `exists_isGroupLikeElem_sub_mem` again form a basis (by
  `linearIndependent_of_flat_of_isNilpotent`). They are multiplicative by the uniqueness
  clause, since `g a * g b` is group-like and `≡ y (a + b)`, and `g 0 = 1`. So
  `AddMonoidAlgebra.lift` gives an algebra map `R[N] → C` with `single a 1 ↦ g a`. It is a
  bialgebra map (`BialgHom.ofAlgHom`) and bijective, and `θ` is its inverse.
- `comul_one_tmul J x`: the comultiplication of `(R ⧸ J) ⊗ C` on `1 ⊗ x` is the image of
  `1 ⊗ comul x` under `TensorProduct.AlgebraTensorModule.distribBaseChange`.
- `exists_bialgEquiv_of_baseChange J hJ e`: let `C` be flat, `J` nilpotent and `N` an
  additive commutative monoid. Given a bialgebra isomorphism
  `e : (R ⧸ J) ⊗[R] C ≃ₐc[R ⧸ J] AddMonoidAlgebra (R ⧸ J) N`, there is a bialgebra
  isomorphism `C ≃ₐc[R] AddMonoidAlgebra R N` (the conclusion is
  `Nonempty (C ≃ₐc[R] AddMonoidAlgebra R N)`). Choose `y a` with `1 ⊗ y a = e⁻¹ (single a 1)`
  and check the four hypotheses of `exists_bialgEquiv_of_isNilpotent` through `e` and
  `one_tmul_eq_zero_iff`.

All results use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
