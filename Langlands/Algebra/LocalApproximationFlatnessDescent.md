# Flatness descent along local approximation systems (Stacks 00R6)

This module proves the published proposition
`Langlands.Algebra.LocalApproximationFlatnessDescentStatement` (Stacks Project
Lemma 10.128.3, tag **00R6**), unchanged and at all seven independent
universes, as the theorem

```lean
theorem Langlands.Algebra.localApproximationFlatnessDescent :
    LocalApproximationFlatnessDescentStatement.{uI, uA, uB, uN, uR, uS, uM}
```

The proposition says the following. Let `R → S` be a local homomorphism of
local rings with `EssFinitePresentation R S`, and let `M` be a finitely
presented `S`-module. Let `D, E` be a local algebra/module system over a
directed nonempty index type, indexed by `ι`, with `E.IsApproximation`. If
`M` is flat over `R` through `algebraMap R S`, then some index `i` has
`E.obj i` flat over `D.base i`, where `E.obj i` is a `D.base i`-module
through `algebraMap (D.base i) (D.alg i)`. Besides the structure fields of
`D` and `E`, the proof below uses only `E.IsApproximation` and the flatness
of `M`. It does not use the essential finite presentation of `S` or the
finite presentation of `M`.

The theorem is the one-line application
`descent_of_idealLocalFlatnessCriterion idealLocalFlatnessCriterion`. Here
`Langlands.Algebra.idealLocalFlatnessCriterion` is the published proof of the
ideal local flatness criterion (Stacks Lemma 10.99.10, tag **00ML**), imported
from module `Langlands.Algebra.IdealLocalFlatnessCriterion`. The rest of this
page describes the assembly lemmas in namespace
`Langlands.Algebra.LocalApproximationFlatnessDescentProof`.

## The assembly

The module proves `Langlands.Algebra.LocalApproximationFlatnessDescentProof.descent_of`
and its corollary `descent_of_idealLocalFlatnessCriterion` in the same namespace.
`descent_of` derives the published proposition
`Langlands.Algebra.LocalApproximationFlatnessDescentStatement` (Stacks Project
Lemma 10.128.3, tag **00R6**) from two other statements, which it takes as
hypotheses:

- `h00ML : IdealLocalFlatnessCriterionStatement`, the ideal form of the
  Noetherian local flatness criterion (Stacks Lemma 10.99.10, tag **00ML**);
- `hred : TensorKernelTransitionReductionStatement`, the reduction step of
  Stacks Lemma 10.99.14 (tag **00MO**). It turns the hypotheses of 00MO, with
  the Tor transition written through ideal tensor kernels, into the two
  hypotheses of 00ML.

The reduction statement is proved by
`Langlands.Algebra.tensorKernelTransitionReduction` (module
`Langlands.Algebra.TensorKernelTransitionReduction`, imported here). So
`descent_of_idealLocalFlatnessCriterion` derives the 00R6 proposition from
`IdealLocalFlatnessCriterionStatement` alone, as
`descent_of h00ML tensorKernelTransitionReduction`. The exact-target
theorem `localApproximationFlatnessDescent` applies it to the published proof
`idealLocalFlatnessCriterion` of 00ML. The universes are chosen
so that both statements are used only at the levels of `D.base`, `D.alg` and
`E.obj`.

The route follows the source proof of 00R6. Flatness of the colimit kills the
finitely many generating relations of a stage-`i` module at a later stage `j`.
So the Tor transition of 00MO vanishes for `i ≤ j`, and 00MO gives flatness
at stage `j`. Tor is replaced by explicit relations and ideal tensors
throughout.

## Generic lemmas on directed systems (section `Directed`)

Here `P` is a `DirectedModuleSystem` of rings `P.base i` and modules
`P.obj i`.

- `baseMap_baseMap` and `map_map` restate the composition laws of the
  transition maps.
- `exists_isTrivialRelation_of_flat`: let `P` be a colimit presentation of a
  flat `R`-module `M` (`P.IsColimit`). If `∑ k, a k • x k = 0` at stage `i`,
  then the transported relation is trivial (`Module.IsTrivialRelation`) at
  some stage `j ≥ i`. Proof: the image relation in `M` is trivial by the
  equational criterion for flatness
  (`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`). This gives
  coefficients `c` and elements `y` with `x k = ∑ c k l • y l` and
  `∑ a k * c k l = 0` in the colimit. The colimit maps are surjective, so
  `finite_lift` (from `Langlands.Algebra.DirectedModuleFlatnessAscent`) lifts
  `c` and `y` to a common stage `j₀`. There the two families of defects map
  to zero in the colimits. By injectivity of the comparison maps and
  `Ring.DirectLimit.of.zero_exact` / `AddCommGroup.DirectLimit.of.zero_exact`,
  each defect vanishes at some later stage. A common upper bound `j` of these
  finitely many stages is the required stage.
- `exists_forall_isTrivialRelation_of_flat`: the same for finitely many
  relations with common coefficients `a`, at one common stage. Each relation
  becomes trivial at its own stage. A common upper bound works because
  transition maps preserve trivial relations (`map_trivial_relation`).

## Finitely generated relations (section `Noetherian`)

For `g : Fin r → A` and an `A`-module `N` that is also a `B`-module (scalar
tower `A → B → N`), `relations B N g` is the `B`-submodule of
`x : Fin r → N` with `∑ k, g k • x k = 0`. The scalar tower makes this a
`B`-submodule.

`exists_relations_induction`: if `B` is Noetherian and `N` is a finite
`B`-module, then there are finitely many relations `z 1, …, z L` such that
every property closed under `0`, `+` and `B`-scalars that holds on all
`z l` holds on every relation. Proof: `relations B N g` is a submodule of
the finite module `Fin r → N`, so it is finitely generated. Then use
`Submodule.span_induction` on a finite generating family.

## The Tor transition from generators (section `Transition`)

Here `R → R'`, `R → S → S'` and `R' → S'` form a commutative square of
scalar towers, and `M → M'` is a map with modules as in the reduction
statement.

- `map_smul_base`: an `S`-linear map `f : M → M'` satisfies
  `f (a • m) = algebraMap R R' a • f m` for `a : R`.
- `transition_of_generators`: let `g` generate `I` and let `f` be additive
  and semilinear over `R → R'`. Suppose that for every relation
  `∑ g k • y k = 0` in `M` the element `∑ ⟨g k⟩ ⊗ f (y k)` of
  `I R' ⊗[R'] M'` is zero. Then the same holds for every finite family
  `a : Fin n → I` with `∑ a k • m k = 0`. This is exactly the elementwise
  transition hypothesis of the reduction statement. Proof: write
  `a k = ∑ c k l * g l`. Then `y l = ∑ c k l • m k` is a relation for `g`,
  and expanding `∑ ⟨a k⟩ ⊗ f (m k)` by bilinearity gives
  `∑ ⟨g l⟩ ⊗ f (y l)`.

The imported `IdealTensorRelation.sum_tmul_eq_zero_of_isTrivialRelation`
(from [IdealTensorRelation](IdealTensorRelation.md)) says: if the elements `g k` of an ideal
`J` satisfy a trivial relation with `x`, then `∑ g k ⊗ x k = 0` in
`J ⊗[B] X`. This is `TensorProduct.sum_tmul_eq_zero_of_vanishesTrivially`
with the coefficients kept in `J`.

## Proof of `descent_of`

Let `D, E` be a local approximation system (`hE : IsApproximation`) of a
flat target module `M` (`hM`). As in the statement, `M` is an `R`-module
through `R → S`, and each `E.obj i` is a `D.base i`-module through
`D.base i → D.alg i`.

1. *Noetherian stages.* `D.base i` is essentially of finite type over `ℤ`,
   and `D.alg i` is essentially of finite type over `D.base i`. So both are
   Noetherian (`Algebra.EssFiniteType.isNoetherianRing`). Also,
   `E.obj i` is a finite `D.alg i`-module.
2. *Generators and relations at a stage `i`.* Fix any stage `i`. Choose
   generators `g` of the maximal ideal `I` of `D.base i`. By
   `exists_relations_induction`, choose finitely many relations `z l` among
   them in `E.obj i` that generate all relations over `D.alg i`.
3. *Killing the relations.* The direct system `E` presents the flat module
   `M` as a colimit: `E.IsColimit`, the first component of `hE`, makes the
   comparison maps from the colimits of `D.base` and of `E.obj` bijective. By
   `exists_forall_isTrivialRelation_of_flat`, all transported relations
   `z l` are trivial at some stage `j ≥ i`.
4. *The square of the transition.* Algebra structures from `D.baseMap`,
   `D.algMap` and their composite make
   `D.base i → D.alg i → D.alg j` and `D.base i → D.base j → D.alg j`
   scalar towers (`D.map_comm`). `E.obj j` becomes a `D.alg i`-module
   through `D.algMap`. The transition `E.map i j` becomes a
   `D.alg i`-linear map `f`.
5. *Vanishing of the Tor transition.* The property "the element
   `∑ ⟨g k⟩ ⊗ f (y k)` of `I D.base j ⊗ E.obj j` is zero" is closed under
   `0` and sums. It is closed under `D.alg i`-scalars because multiplication
   by `D.algMap b` is `D.base j`-linear on `E.obj j`. It holds on each `z l`
   by step 3 and `IdealTensorRelation.sum_tmul_eq_zero_of_isTrivialRelation`. So it holds on all
   relations among `g`. `transition_of_generators` then gives the
   elementwise transition hypothesis of the reduction statement.
6. *Localization and base change.* `IsPrimeLocalization` gives a prime `p`
   of `D.alg i ⊗[D.base i] D.base j` with `D.alg j` the localization at
   `p.primeCompl` through `D.ringBaseChangeMap`. This map agrees with the
   `productMap` of the reduction statement (`hprod`, checked on pure
   tensors). Bijectivity of `E.moduleBaseChangeMap` makes `f` a base change
   along `D.alg i → D.alg j` (`IsBaseChange.of_equiv`).
7. *Flatness modulo `I`.* `D.base i ⧸ I` is a field, so
   `(D.base i ⧸ I) ⊗ E.obj i` is free, hence flat.
8. *The reduction.* `hred` applies, with `R = D.base i`, `R' = D.base j`,
   `S = D.alg i`, `S' = D.alg j`, `M = E.obj i`, `M' = E.obj j`, `I` the
   maximal ideal and `W = p.primeCompl`. It gives injectivity of
   `I' ⊗ E.obj j → D.base j ⊗ E.obj j` for `I' = I D.base j`, and flatness
   of `(D.base j ⧸ I') ⊗ E.obj j` over `D.base j ⧸ I'`.
9. *The criterion 00ML.* `D.base j → D.alg j` is a local homomorphism of
   Noetherian local rings (`D.structure_local`). `I'` is proper because
   `D.base i → D.base j` is local (`D.baseMap_local`), so `I'` lies in the
   maximal ideal. `E.obj j` is a finite `D.alg j`-module. By `h00ML`,
   `E.obj j` is flat over `D.base j`, which is the conclusion at index `j`.

The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
