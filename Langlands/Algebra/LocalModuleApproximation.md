# Constructions of local module approximation systems

This module collects the constructions used to obtain a module approximation
system (Stacks 00QX) from a ring approximation system (Stacks 00QV). It
restricts systems to tails, transports cocones along equivalences, builds
finite free systems and matrix maps between them, and verifies the
approximation clauses for the published cokernel system. All of these
constructions use the published structures `LocalAlgebraSystem`,
`LocalModuleSystem`, `LocalModuleSystem.CompatibleMap` and
`CompatibleMap.cokernelSystem` unchanged.

## Source and provenance

The motivating source is the proof of Stacks Project Lemma 10.127.13 (tag
[00QX](https://stacks.math.columbia.edu/tag/00QX)), in the registered
original `stacks-algebra-flatness-criteria-2026-10-22` (content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`, file
`00QL.html`). The proof chooses a presentation
`S^{⊕s} → S^{⊕t} → M → 0` with matrix `A`. It lifts `A` to a matrix
`A_{λ₂}` over some `S_{λ₂}` and sets
`M_λ = Coker(S_λ^{⊕s} → S_λ^{⊕t})` for `λ ≥ λ₂`, given by the images
`A_λ` of `A_{λ₂}`. It ends with "We leave it to the reader to see that this
works."

The declarations here are an internal construction that carries out this
step. They form no separately numbered source result. The restriction to
`λ ≥ λ₂` is `LocalAlgebraSystem.tail`. The free modules `S_λ^{⊕t}` are
`freeSystem`. The maps `A_λ` are `matrixMap`, and `M_λ` is the published
`cokernelSystem`. The checks left to the reader are
`cokernelSystem_moduleBaseChangeMap_bijective`, `cokernelSystem_finite`
and `cokernelSystem_isApproximation`. Two facts are standard Mathlib
results: the tensor isomorphism for finite free modules
(`TensorProduct.piScalarRight`) and the five lemma for right exact rows
(`LinearMap.bijective_of_surjective_of_bijective_of_right_exact`). No
unpublished code by other workers is used.

The bijectivity of the cokernel's additive colimit comparison is **not**
proved here. It is a separately allocated colimit-preservation result for
`cokernelSystem` (successor of task d10d3f4e). Accordingly,
`cokernelSystem_isApproximation` takes that bijectivity as an explicit
hypothesis `hC`.

## Lifting elements to components

In `Langlands.Algebra.LocalAlgebraSystem`, with `D` a local algebra system:

- `exists_algι_eq` and `exists_baseι_eq`: if the ring colimit comparison
  `D.algebraColimitMap` (resp. `D.baseColimitMap`) is surjective, then every
  element of `S` (resp. `R`) is `D.algι i x` (resp. `D.baseι i x`) for some
  `i` and some component element `x`.
- `exists_algι_eq_fun`: a family of elements of `S` indexed by a finite type
  lifts to a single component.
- `exists_algMap_eq_zero` and `exists_baseMap_eq_zero`: if the comparison is
  injective, then a component element mapping to `0` is already killed by
  some transition map.
- `exists_algMap_eq_zero_fun`: the same for a finite family, with one common
  transition.

The proofs use `Ring.DirectLimit.exists_of` and
`Ring.DirectLimit.of.zero_exact` together with the published formulas
`algebraColimitMap_of` and `baseColimitMap_of`.

## Tails

For `i₀ : ι`, the subtype `{j : ι // i₀ ≤ j}` with the induced preorder is
nonempty (`tailIndex_nonempty`) and directed (`tailIndex_isDirectedOrder`).

`ringDirectLimit_lift_tail_bijective` says: if the lift
`Ring.DirectLimit.lift A f T g hg` of a directed system of commutative rings
with a compatible cocone to `T` is bijective, then so is the lift of the
restricted system over `{j // i₀ ≤ j}` with the restricted cocone.
Injectivity uses `of.zero_exact` and `of_f`; surjectivity pushes a
representative at `i` to an upper bound of `i` and `i₀`.

`LocalAlgebraSystem.tail D i₀` is the system over `{j // i₀ ≤ j}` whose
base and algebra components, transition maps, structure maps and cocone
maps are exactly those of `D` at the underlying indices. The theorem
`tail_isApproximation` shows that it satisfies the four clauses of
`LocalAlgebraSystem.IsApproximation` whenever `D` does. The two colimit
clauses come from `ringDirectLimit_lift_tail_bijective`; the essential finite
type and prime-localization clauses are restrictions of those of `D`.

## Transport of cocones

`LocalAlgebraSystem.mapAlgEquiv D e`, for `D` a system over `R → S'` and an
`R`-algebra equivalence `e : S' ≃ₐ[R] S`, has the same diagram as `D`. Its
algebra cocone maps are `e ∘ D.algι i`; locality of these maps follows from
locality of `D.algι i` by applying `e.symm`. The theorem
`mapAlgEquiv_isApproximation` shows that the four approximation clauses are
preserved. The new algebra colimit comparison is `e` composed with the old
one, so it is bijective.

`LocalModuleSystem.mapLinearEquiv E e`, for `e : M ≃ₗ[S] M'`, has the same
modules and transitions as `E`, and cocone maps `e ∘ E.ιM i`. The theorem
`mapLinearEquiv_isApproximation` shows that all six clauses of
`LocalModuleSystem.IsApproximation` are preserved.

## Colimit criterion for module systems

In `Langlands.Algebra.LocalModuleSystem`:

- `exists_ιM_eq`: if `E.moduleColimitMap` is surjective, every element of
  `M` is `E.ιM i x` for some component element.
- `exists_map_eq_zero`: if `E.moduleColimitMap` is injective, a component
  element mapping to `0` in `M` is killed by some transition.
- `moduleColimitMap_bijective_of`: conversely, `E.moduleColimitMap` is
  bijective if every element of `M` comes from a component and every
  component element mapping to `0` in `M` is killed by some transition.

These use `AddCommGroup.DirectLimit.induction_on`, `of.zero_exact`, `of_f`
and the published formula `moduleColimitMap_of`.

## Finite free systems and matrix maps

`LocalAlgebraSystem.freeSystem D κ`, for a type `κ`, is the module system
with components `κ → D.alg i`, coordinatewise transitions `D.algMap`, and
coordinatewise cocone maps `D.algι` into the target `κ → S`. Its component
level is `max uE uB`, where `κ : Type uE`.

For finite `κ`:

- `freeSystem_moduleColimitMap_bijective`: bijectivity of
  `D.algebraColimitMap` gives bijectivity of the additive colimit
  comparison. The proof applies the criterion above, using the finite-family
  lifting lemmas.
- `freeSystem_moduleBaseChangeMap_bijective`: every tensor transition is
  bijective. Following the published `moduleBaseChangeMap`, the transition
  has the scalar-first domain: it is the map
  `D.alg j ⊗[D.alg i] (κ → D.alg i) → (κ → D.alg j)` sending `s ⊗ v` to
  `k ↦ s * D.algMap i j h (v k)`. Mathlib's equivalence
  `TensorProduct.piScalarRight (D.alg i) (D.alg j) (D.alg j) κ` has the same
  domain and sends `s ⊗ v` to `k ↦ D.algMap i j h (v k) * s`. The two maps
  therefore agree on pure tensors by commutativity of `D.alg j`, and hence
  agree pointwise by induction on tensors. No exchange of tensor factors is
  involved. (Stacks writes the module-first tensor
  `(κ → D.alg i) ⊗[D.alg i] D.alg j`. That map is the scalar-first map
  composed with `TensorProduct.comm`, and this unit does not use it.)
- `freeSystem_isApproximation`: if `D.IsApproximation`, all six module
  clauses hold. The components are finite free modules.

`LocalAlgebraSystem.matrixMap D A hA B hB` takes component matrices
`A i : Matrix ν κ (D.alg i)`. These must be compatible with the transitions
(`hA`: `(A i).map (D.algMap i j h) = A j`) and must map to the matrix
`B : Matrix ν κ S` (`hB`: `(A i).map (D.algι i) = B`). It is the
`CompatibleMap (D.freeSystem κ) (D.freeSystem ν) B.mulVecLin` with
components `(A i).mulVecLin`. The two compatibility equations come from
`RingHom.map_mulVec`.

## Cokernel systems

In `Langlands.Algebra.LocalModuleSystem.CompatibleMap`, with
`φ : CompatibleMap E F f`:

- `cokernelSystem_moduleBaseChangeMap_bijective`: if the tensor transition
  of `E` from `i` to `j` is surjective and that of `F` is bijective, then
  the tensor transition of `φ.cokernelSystem` is bijective. The proof
  applies the five lemma for right exact rows. The top row is the base
  change to `D.alg j` of `E.obj i → F.obj i → F.obj i ⧸ range`, which is
  right exact by `lTensor_exact`. The bottom row is
  `E.obj j → F.obj j → F.obj j ⧸ range`. The vertical maps are the three
  tensor transitions. The two squares commute on pure tensors by
  `φ.map_comm` and the published quotient formula `cokernelSystem_map_mk`.
- `cokernelSystem_finite`: the components are finite over `D.alg i` when
  those of `F` are, as quotients of finite modules.
- `cokernelSystem_isApproximation (hφ) (hC)`: if `φ.IsApproximation` (both
  `E` and `F` satisfy all six clauses) and the additive colimit comparison
  of `φ.cokernelSystem` is bijective (`hC`), then `φ.cokernelSystem`
  satisfies all six clauses. The ring clauses come from `F`; the tensor
  clause and finiteness come from the two lemmas above.

## Matrix presentations

`exists_matrix_presentation S M`: for a finitely presented `S`-module `M`,
there are `n m : ℕ` and `A : Matrix (Fin n) (Fin m) S` with an `S`-linear
equivalence `(Fin n → S) ⧸ range A.mulVecLin ≃ₗ[S] M`. It combines
`Module.FinitePresentation.exists_fin` with a finite generating map of the
kernel, converted to a matrix by `LinearMap.toMatrix'`. In the Stacks
notation, `n = t` and `m = s`.

## Scope

No result here assumes or concludes 00QV or 00QX. The universe variables are
independent: `uI` for the index, `uA, uB` for component rings, `uE, uF` for
component module families or free index types, and `uR, uS, uS', uM, uN`
for ambient carriers.
