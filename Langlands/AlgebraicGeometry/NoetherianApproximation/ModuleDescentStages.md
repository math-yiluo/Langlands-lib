# Descending sections to a finitely generated subalgebra

Module `Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentStages`, namespace
`Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentStages`, universe `u`. Author:
Worker 1038. Internal helper for [`ModuleDescentProof`](ModuleDescentProof.md); it imports only
Mathlib.

## Setting

`A₀ → A` is an algebra of commutative rings in `Type u`, `f₀ : X₀ ⟶ Spec A₀`, and
`a : X ⟶ X₀`, `f : X ⟶ Spec A` are arbitrary morphisms. For a subalgebra `T` of `A`,

- `stage f₀ T` is Mathlib's chosen fibre product
  `pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ T)))`, with projections
  `stageFst f₀ T` and `stageSnd f₀ T`;
- `IsLift f₀ a f T c` says that `c : X ⟶ stage f₀ T` satisfies `c ≫ stageFst f₀ T = a` and
  `c ≫ stageSnd f₀ T = f ≫ Spec.map (CommRingCat.ofHom (algebraMap T A))`.

`Descends f₀ a f W x`, for an open `W` of `X₀` and `x : Γ(X, a ⁻¹ᵁ W)`, says: there is a finite
set `C ⊆ A` such that for every subalgebra `T ⊇ C` and every `c` with `IsLift f₀ a f T c` there is
`y : Γ(stage f₀ T, stageFst f₀ T ⁻¹ᵁ W)` whose image under `c.app`, transported along any
equality `a ⁻¹ᵁ W = c ⁻¹ᵁ (stageFst f₀ T ⁻¹ᵁ W)` by `eqToHom`, is `x`.

## Results

- `Descends.add`, `Descends.mul`: descending sections are closed under addition and
  multiplication (take the union of the finite sets).
- `descends_appLE`: the image of a section of `X₀` over `W` under `a.appLE` descends with
  `C = ∅`, through `(stageFst f₀ T).app W`; after substituting `a = c ≫ stageFst f₀ T` this is
  Mathlib's `Scheme.Hom.comp_appLE`.
- `descends_appLE_snd`: the image of a global function `b` on `Spec A` under `f.appLE` descends
  with `C = {(ΓSpecIso A).hom b}`, through `stageSnd f₀ T`. The proof combines
  `appLE_comp_appLE`, the substitution lemma `appLE_congr_hom`, `comp_appLE` and
  `Scheme.ΓSpecIso_inv_naturality`.
- `descends`: if `IsPullback a f f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))` and `W` is
  affine, every `x : Γ(X, a ⁻¹ᵁ W)` descends. Mathlib's `isIso_pushoutSection_of_isAffineOpen`
  and `isIso_pushoutSection_iff` make the square of rings of sections over `⊤`, `⊤`, `W` and
  `a ⁻¹ᵁ W` a pushout; `CommRingCat.isPushout_iff_isPushout` turns it into an
  `Algebra.IsPushout`, whose base-change property gives an induction
  (`IsBaseChange.inductionOn`) over images of global functions of `Spec A`, products with
  images of sections of `X₀`, and sums.
- `exists_finset_forall_descends`: the same for a finite family of affine opens and sections,
  with one finite set for the whole family (union over the family).

## Provenance

Internal. This is the elementary fact behind the colimit description of sections in Stacks
Project, Limits of Schemes, Lemma 01ZR (`limits.tex`, commit `a04446e5`, registered as
`stacks-limits-of-schemes-a04446e5`): sections of the base change over the preimage of an affine
open come from a finite stage because the ring of sections is a tensor product.
