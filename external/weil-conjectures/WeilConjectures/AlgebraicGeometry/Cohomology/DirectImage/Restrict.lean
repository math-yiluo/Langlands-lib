/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.Flasque
public import WeilConjectures.AlgebraicGeometry.Modules.RestrictPushforward
public import WeilConjectures.AlgebraicGeometry.Cohomology.Restriction
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp

/-!
# Higher direct images and restriction to an open subscheme of the base

Let `f : X ⟶ T` be a morphism of schemes and `g : T' ⟶ T` an open immersion, with base change
`f' : X' ⟶ T'` and `g' : X' ⟶ X`. Then `R^q f'_* (ℱ|_{X'}) ≅ (R^q f_* ℱ)|_{T'}`.

* Restriction to an open subscheme sends injective modules to flasque ones, and flasque modules
  are acyclic for the pushforward
  (`AlgebraicGeometry.Scheme.Modules.rightAcyclic_pushforward_of_isFlasque`).
* Pushforward commutes with restriction to opens of the base
  (`AlgebraicGeometry.Scheme.Modules.pushforwardRestrictIso`).

Hence restriction to `X'` is an exact functor sending injectives to `f'_*`-acyclic objects, and
`R^q (f'_* ∘ (-)|_{X'}) = R^q f'_* ∘ (-)|_{X'}`, while `R^q ((-)|_{T'} ∘ f_*) = (-)|_{T'} ∘ R^q f_*`
since restriction is exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}

/-- A morphism of `𝒪_X`-modules which is surjective on sections over every open is an
epimorphism. -/
lemma epi_of_forall_surjective_app {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ U, Function.Surjective (φ.app U)) : Epi φ where
  left_cancellation a b hab := by
    refine hom_ext _ _ fun U ↦ ?_
    ext x
    obtain ⟨y, rfl⟩ := h U x
    have := congrArg (fun ψ ↦ ψ.app U y) hab
    simpa using this

variable [HasInjectiveResolutions X.Modules]

section BaseChange

variable {T' X' : Scheme.{u}} {f : X ⟶ T} {g : T' ⟶ T} {g' : X' ⟶ X} {f' : X' ⟶ T'}

omit [HasInjectiveResolutions X.Modules] in
/-- In a cartesian square whose bottom arrow `g` is an open immersion, the top arrow `g'` is an
open immersion. -/
lemma isOpenImmersion_of_isPullback [IsOpenImmersion g] (sq : IsPullback g' f' f g) :
    IsOpenImmersion g' := by
  rw [← sq.isoPullback_hom_fst]
  infer_instance

variable [IsOpenImmersion g] [IsOpenImmersion g'] (sq : IsPullback g' f' f g)

omit [HasInjectiveResolutions X.Modules] in
/-- A restriction map of a presheaf between equal opens is an isomorphism. -/
lemma isIso_presheaf_map_of_eq {Y : Scheme.{u}} (M : Y.Modules) {W W' : Y.Opens}
    (i : W' ⟶ W) (h : W = W') : IsIso (M.presheaf.map i.op) := by
  subst h
  rw [Subsingleton.elim i (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  infer_instance

/-- **The higher direct images commute with restriction to an open subscheme of the base**: in a
cartesian square whose bottom arrow `g` is an open immersion,
`R^q f'_* (g'^* ℱ) ≅ (R^q f_* ℱ)|_{T'}`.
Restriction to `X'` is exact and sends injective modules to flasque, hence `f'_*`-acyclic, ones,
restriction to `T'` is exact, and `f'_* ((-)|_{X'}) ≅ (f_* -)|_{T'}`. -/
noncomputable def higherDirectImagePullbackIsoRestrict (ℱ : X.Modules)
    [HasInjectiveResolutions X'.Modules] (q : ℕ) :
    (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ) ≅
      ((higherDirectImage f q).obj ℱ).restrict g :=
  (higherDirectImage f' q).mapIso ((restrictFunctorIsoPullback g').app ℱ).symm ≪≫
    (Functor.compRightDerivedObjIso (restrictFunctor g') (pushforward f')
      (fun I _ ↦ rightAcyclic_pushforward_of_isFlasque f' _
        (isFlasque_restrict g' _ (isFlasque_of_injective I))) q ℱ).symm ≪≫
    Functor.rightDerivedObjIsoOfIso (pushforwardRestrictIso sq).symm q ℱ ≪≫
    Functor.rightDerivedCompObjIso (pushforward f) (restrictFunctor g) q ℱ

end BaseChange

end AlgebraicGeometry.Scheme.Modules
