# Induction on equivariant quasi-étale sites is full

Author: Worker 933.

This module proves that the induction functor
`quasiEtaleSiteInduction hH hC hQ X : Qét(X(H)) ⥤ Qét(X_{G/H}(G))` (module
`InducedEquivariantSite`) is full. The proof assumes the statement
`OpenPartitionCoproductStatement` as a hypothesis. Fullness is one of the three
parts of the equivalence in Berkovich's Example 1.2.1(i). The module is a helper
for the proof of `InducedSpace.QuasiEtaleSiteEquivalenceStatement` (module
`InducedSiteEquivalenceStatement`). Faithfulness is in module
`InducedSiteFaithful`. Essential surjectivity is not treated here. Namespace:
`Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace`.

## Declarations

Let `G : Type z` be a group and `H` a subgroup. Let `A`, `B`, `Y` be `H`-objects
of `LocalizedCategory` (Lean type `Action (LocalizedCategory …) H`). Write
`Ind = inductionFunctor H` (module `InducedSpaceAdjunction`), so that
`Ind A = A_{G/H}`. `pointCoset H A p` (module `InducedSpacePoints`) is the coset
indexing the copy of `A` that contains the point `p` of `A_{G/H}`. Points are
elements of the underlying topological space `localizedSpaceFunctor.obj`.

- `pointCoset_space_apply_of_comp_eq H pA pB ψ hψ p`: let `pA : A ⟶ Y` and
  `pB : B ⟶ Y` be `H`-morphisms, and let `ψ : Ind A ⟶ Ind B` be a `G`-morphism
  with `ψ ≫ Ind pB = Ind pA`. Then `ψ` preserves the coset of every point `p`:
  `pointCoset H B (ψ p) = pointCoset H A p`.

The next two statements take a hypothesis
`hP : OpenPartitionCoproductStatement.{u, v, z}` (module
`OpenPartitionCoproductStatement`). This statement says: an analytic space whose
underlying space is the disjoint union of open subsets `U_j` is the coproduct of
the open domains `U_j`. The results hold for every such `hP`. The statement
itself is not proved here.

- `exists_inductionFunctor_map_eq H hP pA pB ψ hψ`: with `pA`, `pB`, `ψ`, `hψ`
  as above, there is an `H`-morphism `f : A ⟶ B` with `f ≫ pB = pA` and
  `Ind f = ψ`.

Now let `G` be a topological group, `hH : IsOpen (H : Set G)`, and `hC`, `hQ`
proofs of `InducedSpace.ContinuityStatement` and
`InducedSpace.MorphismPropertyStatement`. Let `X` be an `H`-space.

- `full_quasiEtaleSiteInduction hP hH hC hQ X`: the functor
  `quasiEtaleSiteInduction hH hC hQ X` is full. This is a theorem, not an
  instance, because it needs the explicit hypothesis `hP`.

## Proof

`pointCoset_space_apply_of_comp_eq`. Library lemma
`pointCoset_inductionFunctor_map` (module `InducedSpacePoints`) says that an
induced morphism `Ind g` preserves cosets. So
`pointCoset H B (ψ p) = pointCoset H Y ((Ind pB) (ψ p))
= pointCoset H Y ((Ind pA) p) = pointCoset H A p`, using `ψ ≫ Ind pB = Ind pA`
in the middle step.

`exists_inductionFunctor_map_eq`. Let `r = baseRep H`. The underlying morphism
of the unit `A → A_{G/H}` is `unitHom H A = ρ_A(r⁻¹) ≫ copy H A H` (module
`InducedAnalyticSpace`).

1. Let `t = unitHom H A ≫ ψ.hom : A → B_{G/H}`. Every point of `A` goes by
   `unitHom H A` into the copy `H` (`pointCoset_unitHom`), and `ψ` preserves
   cosets by the first lemma. So `t` lands in the copy of `B` indexed by `H`.
   Lemma `foldHom_copy_of_pointCoset` (module `InducedSiteFold`, uses `hP`)
   gives `t ≫ foldHom H B ≫ copy H B H = t`.
2. Let `fh = t ≫ foldHom H B ≫ ρ_B(r) : A → B`. Then `fh ≫ unitHom H B = t`,
   because `ρ_B(r) ≫ ρ_B(r⁻¹) = 𝟙` and step 1.
3. `fh` is `H`-equivariant. The morphism `unitHom H B` is a monomorphism
   (`mono_unitHom`), so it suffices to compare both sides after composing with
   it. Lemma `unitHom_comm` says `ρ(h) ≫ unitHom = unitHom ≫ actionMap h` for
   `A` and for `B`, where `actionMap` is the action of `h ∈ G` on the induced
   space. Together with step 2 and the equivariance of `ψ` (`ψ.comm h`), both
   `ρ_A(h) ≫ fh ≫ unitHom H B` and `fh ≫ ρ_B(h) ≫ unitHom H B` equal
   `unitHom H A ≫ ψ.hom ≫ actionMap H B h`.
   This gives an `H`-morphism `f : A ⟶ B` with `f.hom = fh`.
4. `Ind f = ψ`. Library `homEquiv H` (the universal property of `A_{G/H}`,
   composition with the unit) is injective. By `inductionFunctor_map`,
   `Ind f = lift H (f ≫ unit H B)`, and by `unit_comp_lift` its image under
   `homEquiv H` is `f ≫ unit H B`. The image of `ψ` is `unit H A ≫ ψ`. Their
   underlying morphisms are `fh ≫ unitHom H B` and `unitHom H A ≫ ψ.hom`,
   which are both `t` by step 2.
5. `f ≫ pB = pA`. We have `Ind (f ≫ pB) = Ind f ≫ Ind pB = ψ ≫ Ind pB = Ind pA`.
   Induction is injective on morphisms (`inductionFunctor_map_injective`,
   module `InducedSiteFaithful`).

`full_quasiEtaleSiteInduction`. An object `U` of `Qét(X(H))` is an `H`-space
with a quasi-étale `H`-morphism `U.hom : U → X`
(`EquivariantQuasiEtaleSite X` is Mathlib's `MorphismProperty.Over` with all
morphisms allowed). Let `φ : Ind U ⟶ Ind V` be a morphism of `Qét(X_{G/H}(G))`.
Its underlying morphism `φ.left.hom` satisfies
`φ.left.hom ≫ Ind V.hom.hom = Ind U.hom.hom` (`MorphismProperty.Over.w`).
Apply `exists_inductionFunctor_map_eq` with `Y = X`. The resulting `f`, viewed
as a morphism of `H`-spaces (`ObjectProperty.homMk`) over `X`
(`MorphismProperty.Over.homMk`), maps to `φ`. Equality of morphisms over
`X_{G/H}` is checked on the underlying morphisms
(`MorphismProperty.Over.Hom.ext`, `ObjectProperty.hom_ext`).

## Original source and provenance

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`.
§1.1.2 (printed p.2) builds `X_{G/H}` as the disjoint union of copies of `X`
indexed by `G/H`. §1.2, Example 1.2.1(i) (printed p.3) states without proof that
induction gives an isomorphism of sites. Fullness is part of that statement. The
argument here is derived for this formalization and is not in the source: a
`G`-morphism over the induced base preserves cosets, so it maps the copy `H`
into the copy `H` and can be read back through the fold morphism. The coproduct
property of an open partition is the separate statement
`OpenPartitionCoproductStatement`, taken here as a hypothesis.
