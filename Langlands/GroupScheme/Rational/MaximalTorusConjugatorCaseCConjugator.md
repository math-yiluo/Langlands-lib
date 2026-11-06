# A centralizer conjugator from a conjugation of Lie elements

Author: Worker 1420.

This internal, derived module supplies the step of Case C that turns a conjugation of Lie
elements into the predicate `HasCentralizerConjugator` of module
`MaximalTorusConjugatorCaseCAssembly`. It also contains the transport lemmas this step needs:
they move subgroup-functor and centralizer membership between a group `G` over `k` and its
base change. No literature statement is formalized. Every result is a direct consequence of
the published base-change comparisons of `Lie/BaseChange` and `SubgroupBaseChange`.

Throughout, `G_E` denotes `(GroupScheme.baseChange (algebraBaseMap k E)).obj G` for a
`k`-algebra `E`. A local instance records that `G_E` is affine over `E` when `G` is affine
over `k`, by the pullback of `G.X.hom`. For an `E`-algebra `A` that is also a `k`-algebra
with `IsScalarTower k E A`, the published `Lie.affineBaseChangeEquiv k E G A` identifies
points of `G_E` over `Spec_E A` with points of `G` over `Spec_k A`. The published
`Lie.kernelBaseChangeEquiv k E G E` identifies the Lie kernels.

## Transport lemmas

- `SubgroupFunctor.mem_baseChange_affine_iff`: for a subgroup functor `F` of `G` and a point
  `g` of `G_E` over `Spec_E A`, `g` lies in the base change of `F` (on the affine test
  scheme `Spec_E A`) if and only if `Lie.affineBaseChangeEquiv k E G A g` lies in `F` (on
  `Spec_k A`). The published `SubgroupFunctor.mem_baseChange` states that the base change
  of `F` contains `g` if and only if `F` contains the corresponding point over the
  restricted test scheme. The two test schemes are identified by the published isomorphism
  `Lie.affineBaseTestIso k E A`, and `F` is stable under composition with its hom and inv
  (`F.comp_mem`).
- `Lie.mem_elementCentralizer_baseChange_affine_iff`: for a Lie element `Y` of `G_E` over
  `E` and a point `g` of `G_E` over `Spec_E A`, `g` lies in the centralizer
  `Lie.elementCentralizer G_E Y` (on `Spec_E A`) if and only if the adjoint action of
  `Lie.affineBaseChangeEquiv k E G A g` in `G` fixes the image of
  `Lie.kernelBaseChangeEquiv k E G E Y` under the coefficient change
  `IsScalarTower.toAlgHom k E A`. The proof applies the published
  `Lie.mem_elementCentralizer_adjoint_iff`, injectivity of
  `Lie.kernelBaseChangeLinearEquiv k E G A`, and its compatibilities with the adjoint action
  (`Lie.kernelBaseChangeLinearEquiv_adjoint`) and with coefficient change
  (`Lie.kernelBaseChangeLinearEquiv_naturality`).
- `lieKernelMapLinear_comp`: coefficient change on Lie vectors along `g.comp f` is coefficient
  change along `f` followed by coefficient change along `g` (from the published
  `lieKernelMap_comp`).

## The torus fixes a Lie element: definition

`RangeFixesLieElement j₀ Z` (a `Prop`-valued definition) takes a homomorphism `j₀ : T₀ → G`
of group schemes over `k` and a Lie element `Z` of `G` over a `k`-algebra `Ω`. It says: for
every `k`-algebra `A`, every `k`-algebra map `ε : Ω → A` and every point `s` of `G` over `A`
in the all-test range `SubgroupFunctor.range j₀`, the adjoint action of `s` in `G` fixes
`lieKernelMapLinear G ε Z`, the image of `Z` under `ε`. Informally, `T₀` fixes `Z` under the
adjoint action, tested on all `Ω`-algebras.

## From a centralizing torus over a field to all test algebras

`rangeFixesLieElement_of_range_le` takes a field `Ω` over `k`, a homomorphism
`j₀ : T₀ → G` and a Lie element `Z` of `G` over `Ω`. Suppose the all-test range of the base
change of `j₀` to `Ω` lies in `Lie.elementCentralizer G_Ω ((Lie.kernelBaseChangeEquiv k Ω G Ω).symm Z)`.
This is the conclusion of the published Lie-centralizer statements
`SemisimpleMaximalTorusLieCentralizerStatement` and `CharZeroTorusLieCentralizerStatement`
for `G_Ω`. Then `RangeFixesLieElement j₀ Z` holds.

Proof: fix `A`, `ε` and `s` as in the definition. give `A` the `Ω`-algebra structure of `ε`. By `SubgroupFunctor.mem_baseChange_affine_iff`
and the published `SubgroupFunctor.range_baseChangeHom`, the point of `G_Ω` corresponding to
`s` lies in the range of the base-changed homomorphism. The hypothesis puts it in the
centralizer, and `Lie.mem_elementCentralizer_baseChange_affine_iff` rewrites this as the
claimed equation, since `IsScalarTower.toAlgHom k Ω A = ε`.

## The conjugator

`hasCentralizerConjugator_of_adjoint_eq` assumes:

- `K` and `Ω` are fields over `k`, with `Ω` algebraically closed, and `ψ : K → Ω` is a
  `k`-algebra map;
- `Y` is a Lie element of `G` over `K`, `Z` a Lie element of `G` over `Ω`, and `g` a point
  of `G` over `Ω`;
- `hgZ`: the adjoint action of `g` sends `Z` to the image of `Y` under `ψ`;
- `hZ : RangeFixesLieElement j₀ Z` (the output of the previous lemma);
- `hg`: the underlying map of `g` has dense range.

It concludes `HasCentralizerConjugator G j₀ ((Lie.kernelBaseChangeEquiv k K G K).symm Y)`.
Mathematically: `g` conjugates the centralizer of `Z` onto the centralizer of `Y`, and `T₀`
centralizes `Z`, so `g T₀ g⁻¹` centralizes `Y`.

Proof: give `Ω` the `K`-algebra structure of `ψ`. The witness is the point
`c = (Lie.affineBaseChangeEquiv k K G Ω).symm g` of `G_K` over `Spec_K Ω`. The point of `G`
corresponding to `c` under the published `baseChangePointsEquiv` is `g`, so it has dense range.
For the conjugation condition, centralizer membership is tested on affine `K`-algebras `A`
(`Lie.mem_elementCentralizer`). A test map `a` from `Spec_K A` to the scheme `V` is composed
with `y : V → Spec_K Ω`. Full faithfulness of `algSpec` turns the composite into a `K`-algebra
map `ε' : Ω → A`; let `ε` be its restriction to `k`. The pulled-back conjugate becomes
`c_A t_A c_A⁻¹`, where `c_A` is the image of `c` under `ε'`. By
`Lie.mem_elementCentralizer_baseChange_affine_iff` and the published
`Lie.affineBaseChangeEquiv_naturality`, membership is an equation in `G` over `A`:

- the image of `Y` over `A` is the image of `Y` along `ε ∘ ψ`, which by `hgZ` and the
  published `adjoint_naturality` is `Ad(g_A)` applied to the image `Z_A` of `Z` under `ε`;
- the point of `G` corresponding to `t_A` lies in the range of `j₀` (by
  `SubgroupFunctor.mem_baseChange_affine_iff`), so it fixes `Z_A` by `hZ`;
- hence `Ad(g_A s g_A⁻¹) (Ad(g_A) Z_A) = Ad(g_A) (Ad(s) Z_A) = Ad(g_A) Z_A`, using that the
  adjoint action is a homomorphism.

## Intended use

In Case C, `K` is the function field of the Lie algebra of `G` and `Y` is a prime power of
the generic Lie element; in characteristic zero, `Y` is the generic element itself. The point
`g` and the element `Z` come from the published generic-conjugation result
`Lie.exists_adjoint_eq_genericLieElement_of_denseRange`, after extension to an algebraic
closure. Hypothesis `hZ` comes from the Lie-centralizer statements through
`rangeFixesLieElement_of_range_le`. That assembly is not part of this module.
