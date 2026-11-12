# Smooth charts of the actual coherent-family stack through finite-type field points

Module: `Langlands.AlgebraicGeometry.CoherentSheaves.FieldCoherentPointSmoothChartStatement`.

Author: Worker 3694, for task `5b9ad399-34f2-4314-bb39-902f491aad01`.

This module defines one auxiliary predicate and states one proposition. It
proves only the immediate lemma below and does not prove the proposition.

## Smooth point fibres

For an arbitrary pseudofunctor
`F : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{u + 1, u + 1}` on schemes over
`S : Scheme.{u}` and a chart object `ξ` over `U : Over S`,
`Stacks.HasSmoothPointFibers F ξ` means the following. For every test
`T : Over S` and every object `η` over `T`, some `P : Over T.left` has a natural
isomorphism, on the entire slice `Over T.left`, between its lifted functor of
points and the published actual point fibre `Stacks.pointFiberPresheaf F ξ η`,
and `P.hom` is smooth. No surjectivity is required. Tests are arbitrary schemes,
including empty, nonreduced, nonnoetherian and non-quasi-compact ones.

`Stacks.IsSmoothSurjectivePresentation.hasSmoothPointFibers` records that the
published smooth surjective presentation predicate implies this one, by
forgetting surjectivity. The predicate is the stack-generic form of the
published line-bundle predicate `Picard.PicardGroupoid.HasSmoothPointFibers`.

## The proposition

`FieldCoherentPointSmoothChartStatement.{u}` says: let `k : Type u` be a field and
`X : Over (Spec (CommRingCat.of k))` with `IsProper X.hom`. Let `K : Type u` be a
field with `Algebra k K` and `Algebra.FiniteType k K`, and let
`N : FamilyGroupoid X.hom (ArtinianTest.residueBase k K)` be an actual flat
finitely presented family on `Spec K ×_k X`. Here `ArtinianTest.residueBase k K`
is the published test `Spec K` over `Spec k`. Then there exist

- `U : Over (Spec (CommRingCat.of k))` with `LocallyOfFiniteType U.hom`,
- an actual family `M : FamilyGroupoid X.hom U` on `U ×_k X`,
- a morphism `p : ArtinianTest.residueBase k K ⟶ U` over `Spec k`, that is a
  `K`-point of `U` over `k`,

such that `Stacks.HasSmoothPointFibers` holds for the published coherent-family
pseudofunctor `FamilyGroupoid.pseudofunctor X.hom` with morphism universe lifted
by `PseudofunctorHomLift.homLift.{u + 1}`, at the chart object
`ULiftHom.objUp M`, and there is an actual isomorphism
`(FamilyGroupoid.pullback X.hom p).obj M ≅ N` in the family groupoid.

The families, ordinary pullbacks, coherent restriction isomorphisms and the
universe lift are those of the published `FieldCoherentStackAtlasStatement`. The
point fibres are those of its scheme-atlas predicate. A point over `Z → T.left`
consists of a map to `U` over `k` and an actual isomorphism of the two
pulled-back families, retained as data.

## Source and derivation

This is a derived specialization of original Stacks Project assertions; the
scheme representation of the point fibres is an additional derived requirement.

- Registered original `stacks-artin-axioms-approximation-2026-11-06` (folder
  SHA-256 `f2f078895a7155a2277c0db49c51f80b73993f0439ffc51c35eb54e9b6e0990b`),
  file `artin.pdf`, Lemma 98.13.8 (Tag 07XY), printed pages 23–24. Let `S` be a
  locally Noetherian scheme and `𝒳` a category fibred in groupoids over
  `(Sch/S)_fppf`. Let `k` be a finite type field over `S` and `x₀` an object over
  `Spec(k)` with image `s`. Assume the diagonal is representable by algebraic
  spaces, axioms [1], [2], [3] hold, formal objects are effective, openness of
  versality holds, and `O_{S,s}` is a G-ring. Then there are a morphism of finite
  type `U → S` and an object `x` over `U` such that `x : (Sch/U)_fppf → 𝒳` is
  smooth, and a finite type point `u₀ ∈ U` with residue field `k` and
  `x|_{u₀} ≅ x₀`.
- Registered original `stacks-coherent-sheaf-stack-08ka-2026-11-01` (folder
  SHA-256 `4ac7cc2a6a797cd51c3a793bbf7684229a8f43b69031e852a0681c219ab99078`),
  file `08KA.html`. Theorem 99.5.12 and its proof verify these hypotheses for
  `𝒳 = Coh_{X/B}` with `S = B`, for `f : X → B` separated, flat and of finite
  presentation. Lemma 99.5.3 gives the diagonal, Lemmas 99.5.6, 99.5.7 and 99.5.9
  give axioms [1], [2] and [3], Lemma 99.5.10 gives effectivity, and
  Lemma 99.5.11 gives openness of versality. The proof first reduces to an
  affine base of finite type over `Z`, which is Noetherian with G-ring local
  rings, and then verifies these hypotheses through Lemma 98.17.1.

Here `S = B = Spec k` for a field `k`. It is Noetherian and its only local ring
is a field, which is a G-ring, so the hypotheses of the cited lemmas hold
without that reduction. A proper
morphism to `Spec k` is separated and of finite type; `k` is noetherian, so it
is of finite presentation; it is flat because every scheme over a field is. A
finite type field over `Spec k` is a field `K` of finite type over `k`. An object
of `Coh_{X/k}` over `Spec K` is a finitely presented module on `X_K` flat over
`K`; its support is automatically proper over `K`. The published
`FamilyGroupoid` represents these objects (see the published statement module
`FieldCoherentStackAtlasStatement`).

The Lean conclusion differs from Lemma 98.13.8 as follows.

- `U` is required only to be locally of finite type over `k`. Morphisms of finite
  type are locally of finite type, so this is weaker.
- The point `u₀` with residue field `K` is replaced by a morphism
  `p : Spec K → U` over `k`. Such a point `u₀` gives the morphism
  `Spec K = Spec κ(u₀) → U`, so this is weaker.
- Smoothness of `x : (Sch/U)_fppf → 𝒳` means that, for every scheme `T` with
  an object `η` over `T`, the algebraic space representing the 2-fibre product
  `(Sch/U) ×_𝒳 (Sch/T)` is smooth over `T`. The proof of Lemma 98.13.7 in
  `artin.pdf` (printed page 23) uses exactly this, citing Algebraic Stacks,
  Definition 10.1, which is not among the retained files. This algebraic space
  is the actual point fibre. The Lean
  statement requires it to be represented by a scheme. This follows from the
  affine diagonal: registered original `stacks-isom-functor-08k7-2026-11-02`
  (folder SHA-256
  `a05b61ba562e7e65dd2b64446e779a6bb67af1846c0a00f4a656d64a2b2c27b5`), file
  `08K7.html`, Proposition 99.4.3, makes the Isom functor of finitely presented
  modules flat with proper support an algebraic space affine of finite
  presentation over the base. Registered original
  `stacks-picard-stack-algebraicity-2026-11-01` (folder SHA-256
  `f152eeac350ef0fb061c6651f63b2a7cdeb5d175ad92aacbf99e5e9f6eb0b0e0`), file
  `0DLY.html`, Lemma 108.4.1, states that the diagonal of `Coh_{X/B}` is affine
  and of finite presentation. The point fibre is then affine over the scheme
  `U ×_k T`, hence a scheme. The Library already expresses this step
  conditionally as `FamilyGroupoid.exists_pointFiberIsomScheme_of_properIsom`.

No source result is asserted to be proved by this module. Lemma 98.13.8 relies
on formal versality, algebraization by Artin approximation and openness of
versality. Each still needs a formal proof for coherent families in this scope.
The checked `08KA.html` comments concern a vector-bundle exposition and do not
change Theorem 99.5.12. `0DLY.html` and `08K7.html` have no comments; the chapter
PDF `artin.pdf` carries none.
