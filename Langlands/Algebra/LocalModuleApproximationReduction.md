# Stacks 00QX from Stacks 00QV (reduction)

This module reduces the module-system statement
`Langlands.Algebra.LocalModuleApproximationExistenceStatement` (Stacks
Project Lemma 10.127.13, tag
[00QX](https://stacks.math.columbia.edu/tag/00QX)) to the ring-system
statement `Langlands.Algebra.LocalAlgebraApproximationExistenceStatement`
(Stacks Lemma 10.127.11, tag 00QV). It does not prove 00QV, and it does not
assume 00QX: the reduction takes 00QV as an explicit hypothesis. To do this, it
defines the Stacks module system `M_λ = Coker(A_λ)` attached to a presentation
matrix whose entries lift to one component.

It imports the published statement of 00QX and the module
`Langlands.Algebra.LocalCompatibleMapApproximation`. That module brings in the
00QV statement and the published construction module
`Langlands.Algebra.LocalModuleApproximation`. From it, this module uses
`LocalModuleSystem.CompatibleMap.cokernelSystem_isApproximation_of_isApproximation`:
the cokernel system of a compatible map of approximation systems is an
approximation system. That lemma packages the colimit lemma
`cokernelSystem_moduleColimitMap_bijective` (colimits of cokernels are
cokernels of colimits).

## Presentation system

The definitions work over a directed nonempty index `ι` and a ring system
`D : LocalAlgebraSystem ι R S`, with index types `κ` (a `Fintype`) and `ν`.
They take a matrix `B : Matrix ν κ S`, an index `i₀ : ι`, a matrix
`a : Matrix ν κ (D.alg i₀)` and a proof `ha : a.map (D.algι i₀) = B`, which
says that `a` lifts `B` to the component `i₀`.

- `LocalAlgebraSystem.presentationMap D B i₀ a ha` is a compatible map
  from `(D.tail i₀).freeSystem κ` to `(D.tail i₀).freeSystem ν` over
  `B.mulVecLin`. It is `(D.tail i₀).matrixMap` applied to the component
  matrices `a.map (D.algMap i₀ j.1 j.2)` for `j` in the tail
  `{j : ι // i₀ ≤ j}`. That is, the lifted matrix is transported to each later
  component. These matrices are compatible with the transitions, by
  `DirectedSystem.map_map'` for the transitions of `D`. They map to `B` under
  the cocone, by rewriting with `ha` and applying `D.algι_compat`.
- `LocalAlgebraSystem.presentationSystem D B i₀ a ha` is the module system
  `(D.presentationMap B i₀ a ha).cokernelSystem` over the tail `D.tail i₀`, for
  the `S`-module `(ν → S) ⧸ LinearMap.range B.mulVecLin`. Its component at `j`
  is the cokernel of the matrix map `(κ → D.alg j.1) → (ν → D.alg j.1)`. This
  is the Stacks system `M_λ = Coker(A_λ)` for `λ ≥ λ₂`.
- `LocalAlgebraSystem.presentationSystem_isApproximation` assumes `Finite ν`
  and `hD : D.IsApproximation`. It shows that
  `(D.presentationSystem B i₀ a ha).IsApproximation`. The tail is an
  approximation system (`tail_isApproximation`), so both finite free systems
  are approximation systems (`freeSystem_isApproximation`). Hence the
  presentation map satisfies `IsApproximation`, and
  `cokernelSystem_isApproximation_of_isApproximation` gives the claim.

## Conditional reduction

`localModuleApproximationExistence_of_localAlgebraApproximationExistence`
has the type

```lean
LocalAlgebraApproximationExistenceStatement.{uR, max uS uM} →
  LocalModuleApproximationExistenceStatement.{uR, uS, uM}
```

So 00QV at the universes `uR` and `max uS uM` implies 00QX at the independent
universes `uR`, `uS`, `uM`. Take a local map `R → S` with `S` essentially
finitely presented over `R`, and a finitely presented `S`-module `M`. The proof
follows the Stacks argument.

1. **Universe transport.** The hypothesis is applied to `R → ULift.{uM} S`.
   This ring is local (by `IsLocalRing.of_surjective'` along the inverse of
   `ULift.ringEquiv`). Its structure map is local, because a unit's image in `S`
   under `ULift.algEquiv` is a unit. It is essentially finitely presented: the
   given presentation is composed with `ULift.algEquiv.symm`. The resulting
   index and components lie in `max uR (max uS uM)`, which is the universe
   required by 00QX. The cocone is transported back to `S` along
   `ULift.algEquiv` (`mapAlgEquiv`, preserved by `mapAlgEquiv_isApproximation`).
   This gives an approximation system `D₁` for `R → S`.
2. **Matrix presentation.** `exists_matrix_presentation` gives a matrix
   `A : Matrix (Fin n) (Fin m) S` and an `S`-linear equivalence
   `eA : (Fin n → S) ⧸ range A.mulVecLin ≃ₗ[S] M`.
3. **Lifting the matrix.** The algebra colimit map of `D₁` is surjective, so
   the finitely many entries of `A` lift to one component `i₀`
   (`exists_algι_eq_fun`, applied to the entries indexed by `Fin n × Fin m`).
   Reassembled with `Matrix.of`, they form a matrix over `D₁.alg i₀` whose image
   under `D₁.algι i₀` is `A`.
4. **Cokernel.** By `presentationSystem_isApproximation`, the presentation
   system of this lift is an approximation system over `D₁.tail i₀` for
   `(Fin n → S) ⧸ range A.mulVecLin`. Its cocone is transported along `eA` to
   `M` (`mapLinearEquiv`, preserved by `mapLinearEquiv_isApproximation`).

The witnesses are the index `{j : ι // i₀ ≤ j}`, the ring system `D₁.tail i₀`,
and the module system `(D₁.presentationSystem A i₀ _ _).mapLinearEquiv eA`.
Instances for the preorder, nonemptiness and directedness of the tail are found
by type class inference.

## Provenance

The reduction is the Stacks proof of Lemma 10.127.13 (00QX): lift the
presentation matrix to some `S_λ₂`, take `M_λ = Coker(A_λ)` for `λ ≥ λ₂`, and
"leave it to the reader to see that this works". `presentationSystem` is the
system `M_λ` of that proof. The universe transport through `ULift` is internal
packaging. It is needed because the published 00QV statement places its
witnesses in the maximum of two universes, while 00QX needs the maximum of
three.
