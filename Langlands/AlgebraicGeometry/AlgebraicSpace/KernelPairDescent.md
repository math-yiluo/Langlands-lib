# Descent of maps along locally surjective maps from schemes

Author: Worker 5067.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.KernelPairDescent`, namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.KernelPairDescent`. It imports
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation` and Mathlib's
`Mathlib.CategoryTheory.Sites.LocallyInjective`.

This is a helper module for `ReducedClosedSubspaceProof`. It has no statement or definition of
its own, only lemmas. Throughout:

- `S : Scheme.{u}`, and `V R : Over S` are schemes over `S`;
- `schemeYoneda S` sends a scheme over `S` to its functor of points, written `h_V`;
- `F`, `G` are presheaves or fppf sheaves on `Over S` (`FppfSheaf S`, values in `F.obj`);
- `a : h_V ⟶ F` is a map and `t s : R ⟶ V` are morphisms;
- `IsPullback (h_t) (h_s) a a` says that `R` with `t, s` represents the kernel pair
  `h_V ×_F h_V` of `a`.

## Results

- `exists_section_of_isPullback h x y hxy`: if `t, s` represent the kernel pair of `a`, then two
  sections `x y` of `h_V` over a test object `T` with `a x = a y` come from a section `r` of
  `h_R` with `t r = x` and `s r = y`. Proof: evaluate the pullback square at `T`, where
  pullbacks of types are computed pointwise (`Types.exists_of_isPullback`).
- `app_eq_of_isPullback h b hb x y hxy`: if moreover `b : h_V ⟶ G` satisfies
  `h_t ≫ b = h_s ≫ b`, then `a x = a y` implies `b x = b y`. Proof: take `r` as above and
  apply the equation `h_t ≫ b = h_s ≫ b` to `r`.
- `exists_desc a ha h b hb`: descent. Let `F` and `G` be fppf sheaves and let
  `a : h_V ⟶ F` be locally surjective for the fppf topology. If `t, s` represent the kernel
  pair of `a` and `h_t ≫ b = h_s ≫ b`, then there is `c : F ⟶ G` with `a ≫ c = b`.
  Proof: as a map of sheaves `h_V ⟶ F` (the sheaf `(schemeSheaf S).obj V`), `a` is locally
  surjective, hence an epimorphism. Sheaf categories are regular, so `a` is an effective
  epimorphism (`IsRegularEpiCategory.regularEpiOfEpi`). Then `EffectiveEpi.desc` gives `c`.
  Its hypothesis says that `g₁ ≫ a = g₂ ≫ a` implies `g₁ ≫ b = g₂ ≫ b` for maps `g₁ g₂` from
  any sheaf into `h_V`. This is checked on sections with `app_eq_of_isPullback`.
- `hom_ext_of_isLocallySurjective a ha h`: two maps `c c' : F ⟶ G` of fppf sheaves with
  `a ≫ c = a ≫ c'` are equal when `a` is locally surjective. Proof: cancel the epimorphism
  `a` in the category of sheaves.
- `injective_of_isPullback a ha h c hc T`: let `a` be locally surjective, with `t, s`
  representing the kernel pairs of both `a` and `a ≫ c`. Then `c : F ⟶ G` is injective on
  sections over every `T`. Proof: `c` is locally injective as a map of sheaves. Two sections
  `x y` of `F` with `c x = c y` are, on the intersection of their image sieves under `a`,
  restrictions of sections `x' y'` of `h_V`. These satisfy `(a ≫ c) x' = (a ≫ c) y'`, so
  `app_eq_of_isPullback` for the kernel pair of `a ≫ c` (with the map `a`) gives
  `a x' = a y'`. A locally injective map of sheaves is injective on sections
  (`Sheaf.isLocallyInjective_iff_injective`).

## Provenance

Internal. These are standard facts: a locally surjective map of sheaves is an effective
epimorphism, so maps out of its target are the maps out of its source that are constant on
its kernel pair. The Lean proofs use Mathlib's API for regular categories and locally
injective maps of sheaves; no literature source is cited.
