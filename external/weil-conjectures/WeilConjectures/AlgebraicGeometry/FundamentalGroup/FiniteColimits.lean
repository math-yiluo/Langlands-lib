/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.CategoryTheory.Limits.CoequalizerOfMonoidQuotient

/-!
# Finite limits and finite colimits of finite étale schemes

Let `Y` be a scheme. The category `FÉt(Y)` of finite étale `Y`-schemes has finite limits and
finite colimits, and for every morphism `f : Y' ⟶ Y` the base change functor
`FÉt(Y) ⥤ FÉt(Y')` preserves them (blueprint `lem-fet-finite-limits`).

Finite limits, finite coproducts and quotients by finite monoids are constructed in
`WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisCategory`. A coequalizer of
`a, b : P ⟶ Q` is the quotient of `Q ⨿ P` by the action of the three element monoid
`CategoryTheory.Limits.CoequalizerMonoid` through `[inl, a ≫ inl]` and `[inl, b ≫ inl]`
(`CategoryTheory.Limits.hasCoequalizers_of_hasColimitsOfShape_singleObj`).

Exactness of base change is checked on geometric fibres: the geometric fibre functors preserve
finite limits and finite colimits, the geometric fibre of a base change is a geometric fibre of
the original scheme (`AlgebraicGeometry.Scheme.FiniteEtale.pullbackFiberIso`), and a morphism of
finite étale `Y'`-schemes inducing bijections on the geometric fibres at all points of `Y'` is an
isomorphism (`AlgebraicGeometry.Scheme.FiniteEtale.isIso_of_forall_isIso_fiber_map`).

## Main statements

- `AlgebraicGeometry.Scheme.FiniteEtale.instHasFiniteColimits`: `FÉt(Y)` has finite colimits.
- `AlgebraicGeometry.Scheme.FiniteEtale.preservesFiniteLimits_pullback`,
  `AlgebraicGeometry.Scheme.FiniteEtale.preservesFiniteColimits_pullback`: base change is exact.
- `AlgebraicGeometry.Scheme.FiniteEtale.finite_limits_colimits`: the blueprint statement.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {Y : Scheme.{u}}

/-! ### Finite colimits -/

instance : HasCoequalizers Y.FiniteEtale :=
  have := hasColimitsOfShape_singleObj Y CoequalizerMonoid.{u}
  hasCoequalizers_of_hasColimitsOfShape_singleObj.{u} _

instance : HasFiniteColimits Y.FiniteEtale :=
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

section Fiber

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

instance : PreservesColimitsOfShape WalkingParallelPair (fiber s) :=
  have := hasColimitsOfShape_singleObj Y CoequalizerMonoid.{u}
  preservesCoequalizers_of_preservesColimitsOfShape_singleObj.{u} (fiber s)

/-- The geometric fibre functors preserve finite colimits. -/
instance : PreservesFiniteColimits (fiber s) :=
  preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts (fiber s)

end Fiber

/-! ### Geometric fibres detect isomorphisms -/

/-- A geometric point of `Y` at `y`, given by an algebraic closure of the residue field. -/
noncomputable def geometricPoint (y : Y) :
    Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) _)) ≫ Y.fromSpecResidueField y

@[simp]
lemma geometricPoint_apply (y : Y) (z : Spec (.of (AlgebraicClosure (Y.residueField y)))) :
    geometricPoint y z = y := by
  rw [geometricPoint, Scheme.Hom.comp_apply]
  exact Y.fromSpecResidueField_apply y _

/-- A morphism of finite étale `Y`-schemes which is surjective on the geometric fibres at all
points of `Y` is surjective: a point outside its image lies in the open and closed complement of
the image, whose geometric fibre at that point is nonempty. -/
lemma surjective_of_forall_surjective_fiber {P Q : Y.FiniteEtale} (f : P ⟶ Q)
    (h : ∀ y : Y, Function.Surjective ((fiber (geometricPoint y)).map f)) :
    Function.Surjective f.hom.left := by
  have hV : IsClosed (Set.range f.hom.left) := f.hom.left.isClosedMap.isClosed_range
  let W : Q.obj.left.Opens := ⟨(Set.range f.hom.left)ᶜ, hV.isOpen_compl⟩
  have hW : IsClosed (W : Set Q.obj.left) :=
    isClosed_compl_iff.mpr f.hom.left.isOpenMap.isOpen_range
  intro q
  by_contra hq
  let y := Q.obj.hom q
  let s := geometricPoint y
  have : IsFinite (ofIsClopen Q W hW).obj.hom := (ofIsClopen Q W hW).property
  have : AlgebraicGeometry.Etale (ofIsClopen Q W hW).obj.hom := (ofIsClopen Q W hW).obj.prop
  obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (.of (AlgebraicClosure (Y.residueField y)))))
  obtain ⟨t, ht⟩ := (ofIsClopen Q W hW).obj.hom.exists_lift_of_isSepClosed s
    ⟨z, (⟨q, hq⟩ : (W : Set Q.obj.left)), by
      change (W.ι ≫ Q.obj.hom) ⟨q, hq⟩ = geometricPoint y z
      rw [geometricPoint_apply, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      rfl⟩
  let x : (fiber s).obj (ofIsClopen Q W hW) := Over.homMk t ht
  obtain ⟨p, hp⟩ := h y ((fiber s).map (ofIsClopenι Q W hW) x)
  have := congr_arg (fun e : (fiber s).obj Q ↦ (e.left : Spec _ ⟶ Q.obj.left) z) hp
  simp only [fiber_map_left, Scheme.Hom.comp_apply] at this
  let w : (W : Set Q.obj.left) := t z
  exact w.2 ⟨_, this⟩

/-- A monomorphism of finite étale `Y`-schemes which is surjective on the geometric fibres at
all points of `Y` is an isomorphism: it is a surjective open immersion. -/
lemma isIso_of_mono_of_forall_surjective_fiber {P Q : Y.FiniteEtale} (i : P ⟶ Q) [Mono i]
    (h : ∀ y : Y, Function.Surjective ((fiber (geometricPoint y)).map i)) : IsIso i := by
  have : IsOpenImmersion i.hom.left := IsOpenImmersion.of_flat_of_mono _
  have : IsIso ((forgetScheme Y).map i) :=
    (isIso_iff_isOpenImmersion_and_surjective i.hom.left).mpr
      ⟨inferInstance, ⟨surjective_of_forall_surjective_fiber i h⟩⟩
  exact isIso_of_reflects_iso i (forgetScheme Y)

/-- **The geometric fibres detect isomorphisms**: a morphism of finite étale `Y`-schemes
inducing bijections on the geometric fibres at all points of `Y` is an isomorphism. -/
lemma isIso_of_forall_isIso_fiber_map {P Q : Y.FiniteEtale} (f : P ⟶ Q)
    (h : ∀ y : Y, IsIso ((fiber (geometricPoint y)).map f)) : IsIso f := by
  have hbij (y : Y) : Function.Bijective ((fiber (geometricPoint y)).map f) :=
    have := h y
    ConcreteCategory.bijective_of_isIso _
  -- `f` is a monomorphism: the diagonal `P ⟶ P ×_Q P` is surjective on fibres
  let δ : P ⟶ Limits.pullback f f := pullback.lift (𝟙 P) (𝟙 P) rfl
  have : IsSplitMono δ := IsSplitMono.mk' ⟨pullback.fst f f, by simp [δ]⟩
  have hδ (y : Y) : Function.Surjective ((fiber (geometricPoint y)).map δ) := by
    intro e
    let s := geometricPoint y
    let hD := isLimitOfPreserves (fiber s ⋙ FintypeCat.incl) (pullbackIsPullback f f)
    have hfs : (fiber s).map f ((fiber s).map (pullback.fst f f) e) =
        (fiber s).map f ((fiber s).map (pullback.snd f f) e) := by
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp, pullback.condition]
    have hab := (hbij y).1 hfs
    set a := (fiber s).map (pullback.fst f f) e
    have hfst : (fiber s).map (pullback.fst f f) ((fiber s).map δ a) = a := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, pullback.lift_fst,
        CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
    have hsnd : (fiber s).map (pullback.snd f f) ((fiber s).map δ a) = a := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, pullback.lift_snd,
        CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
    refine ⟨a, (Concrete.isLimit_ext _ hD _ _ ?_).symm⟩
    rintro (_ | _ | _)
    · change (fiber s).map (pullback.fst f f ≫ f) e =
        (fiber s).map (pullback.fst f f ≫ f) ((fiber s).map δ a)
      rw [Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hfst]
    · change (fiber s).map (pullback.fst f f) e =
        (fiber s).map (pullback.fst f f) ((fiber s).map δ a)
      exact hfst.symm
    · change (fiber s).map (pullback.snd f f) e =
        (fiber s).map (pullback.snd f f) ((fiber s).map δ a)
      rw [hsnd]
      exact hab.symm
  have : IsIso δ := isIso_of_mono_of_forall_surjective_fiber δ hδ
  have hfs : pullback.fst f f = pullback.snd f f := by
    rw [← cancel_epi δ, pullback.lift_fst, pullback.lift_snd]
  have : Mono f := ⟨fun g h hgh ↦ by
    rw [← pullback.lift_fst g h hgh, hfs, pullback.lift_snd]⟩
  exact isIso_of_mono_of_forall_surjective_fiber f fun y ↦ (hbij y).2

/-! ### Exactness of base change -/

variable {Y' : Scheme.{u}} (f : Y' ⟶ Y)

/-- Base change preserves finite colimits. -/
instance preservesFiniteColimits_pullback : PreservesFiniteColimits (pullback f) where
  preservesFiniteColimits J _ _ := ⟨fun {K} ↦ by
    let G := pullback f
    let c := colimit.cocone K
    let φ := (colimit.isColimit (K ⋙ G)).desc (G.mapCocone c)
    have : IsIso φ := by
      refine isIso_of_forall_isIso_fiber_map φ fun y ↦ ?_
      let s := geometricPoint y
      let P' := isColimitOfPreserves (fiber s) (colimit.isColimit (K ⋙ G))
      let Q' : IsColimit ((fiber s).mapCocone (G.mapCocone c)) :=
        IsColimit.mapCoconeEquiv (pullbackFiberIso f s).symm
          (isColimitOfPreserves (fiber (s ≫ f)) (colimit.isColimit K))
      have : (fiber s).map φ = (P'.coconePointUniqueUpToIso Q').hom := by
        refine P'.hom_ext fun j ↦ ?_
        rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
        change (fiber s).map ((colimit.cocone (K ⋙ G)).ι.app j) ≫ (fiber s).map φ = _
        rw [← Functor.map_comp, IsColimit.fac]
        rfl
      rw [this]
      infer_instance
    exact preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
      (IsColimit.ofPointIso (colimit.isColimit (K ⋙ G)))⟩

/-- Base change preserves finite limits. -/
instance preservesFiniteLimits_pullback : PreservesFiniteLimits (pullback f) where
  preservesFiniteLimits J _ _ := ⟨fun {K} ↦ by
    let G := pullback f
    let c := limit.cone K
    let φ := (limit.isLimit (K ⋙ G)).lift (G.mapCone c)
    have : IsIso φ := by
      refine isIso_of_forall_isIso_fiber_map φ fun y ↦ ?_
      let s := geometricPoint y
      let P' := isLimitOfPreserves (fiber s) (limit.isLimit (K ⋙ G))
      let Q' : IsLimit ((fiber s).mapCone (G.mapCone c)) :=
        IsLimit.mapConeEquiv (pullbackFiberIso f s).symm
          (isLimitOfPreserves (fiber (s ≫ f)) (limit.isLimit K))
      have : (fiber s).map φ = (Q'.conePointUniqueUpToIso P').hom := by
        refine P'.hom_ext fun j ↦ ?_
        rw [IsLimit.conePointUniqueUpToIso_hom_comp]
        change (fiber s).map φ ≫ (fiber s).map ((limit.cone (K ⋙ G)).π.app j) = _
        rw [← Functor.map_comp, IsLimit.fac]
        rfl
      rw [this]
      infer_instance
    exact preservesLimit_of_preserves_limit_cone (limit.isLimit K)
      (IsLimit.ofPointIso (limit.isLimit (K ⋙ G)))⟩

/-- **Finite limits and finite colimits of finite étale schemes.** Let `Y` be a scheme. The
category `FÉt(Y)` of finite étale `Y`-schemes has finite limits and finite colimits, and for
every morphism `f : Y' ⟶ Y` the base change functor `FÉt(Y) ⥤ FÉt(Y')` is exact, i.e. preserves
finite limits and finite colimits.
(blueprint: `lem-fet-finite-limits`) -/
theorem finite_limits_colimits (Y : Scheme.{u}) :
    HasFiniteLimits Y.FiniteEtale ∧ HasFiniteColimits Y.FiniteEtale ∧
      ∀ {Y' : Scheme.{u}} (f : Y' ⟶ Y),
        PreservesFiniteLimits (pullback f) ∧ PreservesFiniteColimits (pullback f) :=
  ⟨inferInstance, inferInstance, fun _ ↦ ⟨inferInstance, inferInstance⟩⟩

end AlgebraicGeometry.Scheme.FiniteEtale
