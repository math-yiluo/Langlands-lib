# Representable diagonal from a kernel pair locally of finite type

Authors: Worker 1001.

Internal infrastructure for the proof of
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAlgebraicSpaceQuotientStatement`
(Stacks Project Theorem 65.10.5, Tag [02WW](https://stacks.math.columbia.edu/tag/02WW),
retained as `stacks-etale-equivalence-relations-2026-11-01`). The source first reduces to
an affine `U` and then proves Lemma 65.10.4 (Tag [0265](https://stacks.math.columbia.edu/tag/0265),
retained as `stacks-etale-quotient-effective-fppf-descent-2026-11-01`). Its third step shows
that the diagonal of `F = U/R` is representable. For `T ⟶ F × F` it descends
`T ×_{F × F} F` along an étale covering of `T`. After that base change the fibre product
becomes a base change of the monomorphism `j = (t, s) : R ⟶ U ×_S U`, which is separated and
locally quasi-finite. The descent step uses effective fppf descent of separated, locally
quasi-finite morphisms (Tag [02W8](https://stacks.math.columbia.edu/tag/02W8)).

This module carries out the same step for any fppf sheaf with a locally surjective map from a
scheme whose kernel pair is represented. For two sections `x y` over `V`, the fibre product
`V ×_{(x, y), F × F} F` is the equalizer locus of `x` and `y`. It is descended along the fppf
covering sieve of `V` on which both sections lift to `U`. The descent theorem enters as an
explicit hypothesis `hD`, the published sheaf-form statement
`Langlands.AlgebraicGeometry.FppfSeparatedLocallyQuasiFiniteDescentStatement`. All
declarations are in the namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.KernelPair`.

## Equalizer loci

- `eqLocus x y`, for sections `x y` of a presheaf `F` over `V : Over S`, is the subfunctor
  of `(schemeYoneda S).obj V` of points `g : T ⟶ V` with `F.map g.op x = F.map g.op y`.
  `mem_eqLocus_iff` unfolds membership.
- `isSheaf_schemeYoneda V`: the points of `V` form an fppf sheaf of types (from the
  Library's `schemeSheaf`).
- `isSheaf_eqLocus Q x y`: for an fppf sheaf `Q`, the equalizer locus is an fppf sheaf,
  since `Q` is separated (`Subfunctor.isSheaf_iff`). `eqLocusSheaf Q x y` is the
  corresponding `FppfSheaf S`.

## Auxiliary lemmas

- `map_comp_eq_map_comp_of_app_eq α β e`: if maps `α`, `β` from represented presheaves
  to a presheaf `F` take the points `f : T ⟶ U` and `f' : T ⟶ U'` to the same section,
  then `(schemeYoneda S).map f ≫ α = (schemeYoneda S).map f' ≫ β`. It is proved by
  naturality. `map_comp_eq_of_app_eq` is the case `α = β`.
- `mono_left_of_map_mono f`: if `(schemeYoneda S).map f` is a monomorphism, so is the
  underlying morphism of schemes `f.left`.

## Main results

Fix an fppf sheaf `Q`, a map `a : (schemeYoneda S).obj U ⟶ Q.obj` that is fppf locally
surjective, and `t s : R ⟶ U` with
`h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a`, that is, the kernel
pair of `a` is represented by `(t, s)`.

- `mono_prodLift_of_isPullback a h`: `prod.lift t s : R ⟶ U ⨯ U` (product in `Over S`) is
  a monomorphism. This uses the Library's `EtaleEquivalenceRelation.hom_ext_of_isPullback`.
- `exists_isPullback_eqLocus a h ht x y g τ₁ τ₂ hτ₁ hτ₂`: suppose `t.left` is locally of
  finite type and `x y` are sections of `Q` over `V`. Let `g : T ⟶ V` be a morphism along
  which `x` and `y` lift to points `τ₁ τ₂ : T ⟶ U`. Then there are `X' : Over S`,
  `x' : X' ⟶ T` and `a'` such that `a'` and `(schemeYoneda S).map x'` form a pullback of
  the inclusion `(eqLocus x y).ι` along `(schemeYoneda S).map g`. Moreover `x'.left` is
  separated, locally quasi-finite and locally of finite type. Here `X'` is the pullback in
  `Over S` of `prod.lift τ₁ τ₂ : T ⟶ U ⨯ U` along `prod.lift t s`. The map `x'` is a base
  change of a monomorphism, hence a monomorphism of schemes. So it is separated and
  universally injective, and locally quasi-finite by Mathlib's instances. It is locally of
  finite type as a base change of `(prod.lift t s).left`, which is locally of finite type
  because its composite with the first projection is `t.left`
  (`locallyOfFiniteType_of_comp`). The pullback property is checked objectwise with
  `Types.isPullback_iff`. A point `w : T' ⟶ T` with `w ≫ g` in the equalizer locus
  satisfies `a (w ≫ τ₁) = a (w ≫ τ₂)`. Hence `(w ≫ τ₁, w ≫ τ₂)` lifts to `R`
  (`EtaleEquivalenceRelation.exists_lift_of_isPullback`), which gives the point of `X'`.
- `hasRepresentableDiagonal_of_isPullback hD a h ht`: under `hD` and with `t.left` locally
  of finite type, `Q.obj` has representable diagonal. The proof applies the Library's
  `hasRepresentableDiagonal_of_representsEqualizer`. For sections `x y` over `V`, let `J` be
  the intersection of the image sieves of `x` and `y` under `a`. It is an fppf covering
  sieve because `a` is locally surjective. `hD`, applied to the sheaf `eqLocusSheaf Q x y`,
  the inclusion into `(schemeYoneda S).obj V`, and `J` with the local representations of
  `exists_isPullback_eqLocus`, gives `X` with `ι : X ⟶ V` and an isomorphism
  `(schemeYoneda S).obj X ≅ eqLocus x y` over `V`. So `ι` represents the equalizer of `x`
  and `y` (`RepresentsEqualizer`). It is a monomorphism of schemes because the inclusion
  of a subfunctor is a monomorphism (`mono_left_of_map_mono`).
