# Degree-zero rigidity from big-cell injectivity

Module `Langlands.GroupScheme.Rational.TorusUnipotence.Rigidity`, namespace
`Langlands.GroupScheme.TorusUnipotence`.

This module turns the injectivity of `bigCellMap` (from `BigCellStatement`) into the top-weight
rigidity condition used by `TopWeight`. Suppose a degree-zero element `a` has the property that
every functional vanishing in degrees `≤ 0`, applied to the second tensor factor of `Δ a`, gives
`0`. Then `a` is a scalar.

## Statements

*Separation of tensors.* Let `V`, `W` be vector spaces over a field `k`.

* `equivFinsuppOfBasisRight_apply 𝒷 t i`: the `i`-th coordinate of `t ∈ V ⊗ W` with respect to
  a basis `𝒷` of `W` (`TensorProduct.equivFinsuppOfBasisRight`) is
  `rid ((𝒷.coord i).lTensor V t)`.
* `eq_zero_of_forall_lTensor`: if `rid (m.lTensor V t) = 0` for every functional
  `m : Module.Dual k W`, then `t = 0`.

*Positive projection.* For a decomposition `𝒜 : ℤ → Submodule k A`:

* `posProj 𝒜 : A →ₗ[k] A`: the projection onto the sum of the components of positive degree.
* `posProj_of_mem`: for `b ∈ 𝒜 d`, `posProj 𝒜 b = b` if `0 < d` and `0` otherwise.

*Rigidity.* Let `A` be a commutative `k`-algebra with a `ℤ`-grading `𝒜` (`GradedAlgebra 𝒜`) and
an augmentation `ε : A →ₐ[k] k`.

* `sub_algebraMap_mem_graded_zero`: for `a ∈ 𝒜 0`, `a - ε a` lies in `𝒜 0` and in `ker ε`.
* `mk_plusIdeal_of_mem_zero`, `mk_minusIdeal_of_mem_zero`: on `𝒜 0`, both quotient maps
  `A → A ⧸ plusIdeal 𝒜 ε` and `A → A ⧸ minusIdeal 𝒜 ε` agree with `ε`.
* `mk_plusIdeal_sub_posProj hε x`. If `ε` vanishes in nonzero degrees, then
  `[x - posProj 𝒜 x] = ε x` in `A ⧸ plusIdeal 𝒜 ε`.
* `map_quotient_lTensor_sub_posProj hε t`. Under the same hypothesis, applying the two quotient
  maps to `(id - posProj 𝒜).lTensor A t` gives `[rid ((id ⊗ ε) t)] ⊗ 1`.
* `eq_algebraMap_of_lTensor_eq_zero hinj hε hr ha hm`. Assume `bigCellMap 𝒜 ε Δ` is injective,
  `ε` vanishes in nonzero degrees, and `Δ` satisfies the right counit law `hr`. Let `a ∈ 𝒜 0`
  satisfy `rid (m.lTensor A (Δ a)) = 0` for every functional `m` vanishing on `𝒜 d` for all
  `d ≤ 0` (`hm`). Then `a = algebraMap k A (ε a)`.

## Proof

*Separation.* Choose a basis of `W` (`Module.Free.chooseBasis`). The coordinates of `t` are the
contractions with the coordinate functionals; this is checked on pure tensors. They all vanish,
so `t = 0` by injectivity of `equivFinsuppOfBasisRight`.

*Quotients.* For `a ∈ 𝒜 0`, `a - ε a` is a generator of both ideals, so `[a] = ε a`. For
`mk_plusIdeal_sub_posProj`, induct over homogeneous components. In negative degree `d`,
`x - posProj x = x` is a generator of `plusIdeal` and `ε x = 0`. In degree `0`, use the previous
fact. In positive degree, `x - posProj x = 0` and `ε x = 0`. The tensor version follows on pure
tensors `x ⊗ y`: the second factor becomes `ε y · 1`, which moves to the first factor.

*Rigidity.* For every functional `m`, the functional `m ∘ posProj` vanishes in degrees `≤ 0`, so
`hm` gives `rid ((m ∘ posProj).lTensor A (Δ a)) = 0`. By separation,
`posProj.lTensor A (Δ a) = 0`, hence `(id - posProj).lTensor A (Δ a) = Δ a`. Then
`map_quotient_lTensor_sub_posProj` and the right counit law give
`bigCellMap a = [a] ⊗ 1`. Since `a ∈ 𝒜 0`, `[a] = ε a` in `A ⧸ minusIdeal`, so
`bigCellMap a = ε a · (1 ⊗ 1) = bigCellMap (algebraMap k A (ε a))`. Injectivity gives
`a = algebraMap k A (ε a)`.

## Provenance

This is the algebraic form of the following geometric argument. A function on `H` that is
invariant under `U⁺` and of weight zero is constant on the big cell `U⁻ × U⁺`. Since the big cell
is schematically dense, it is constant on `H`. The open cell is modelled on the dynamic
method of Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed., §2.1. The statement is an internal
lemma for the proof of `Langlands.GroupScheme.RelativeRoot.TorusActionUnipotenceStatement`. No
source states it in this form.
