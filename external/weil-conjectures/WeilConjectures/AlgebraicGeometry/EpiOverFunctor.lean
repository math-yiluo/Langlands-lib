/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

private theorem ulift_isLocallyInjective {C : Type v} [Category.{v} C] (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q) [Presheaf.IsLocallyInjective J f] :
    Presheaf.IsLocallyInjective J (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{v}) := by
  constructor
  intro X x y h
  have hh := Presheaf.equalizerSieve_mem J f x.down y.down (congrArg ULift.down h)
  apply J.superset_covering _ hh
  intro W g hg
  exact ULift.ext hg

private theorem ulift_isLocallySurjective {C : Type v} [Category.{v} C] (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q) [Presheaf.IsLocallySurjective J f] :
    Presheaf.IsLocallySurjective J (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{v}) := by
  constructor
  intro X x
  apply J.superset_covering _ (Presheaf.imageSieve_mem J f x.down)
  intro W g hg
  obtain ⟨y, hy⟩ := hg
  exact ⟨ULift.up y, ULift.ext hy⟩

private theorem hasSheafify_large {C : Type v} [Category.{v} C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{max u v} := by
  let : PreservesFilteredColimitsOfSize.{v, v} (forget AddCommGrpCat.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink _
  infer_instance

-- Enlarge the site model too, so Mathlib's concrete sheafification instances apply.
private theorem wEqualsLocallyBijective_large
    {C : Type v} [Category.{v} C] (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective AddCommGrpCat.{max u v} := by
  let : EssentiallySmall.{max u v} C := essentiallySmallSelf.{u} C
  let : PreservesFilteredColimitsOfSize.{max u v, max u v}
      (forget AddCommGrpCat.{max u v}) := preservesFilteredColimitsOfSize_shrink _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{max u v})

-- Compare the two locally bijective units on C/U and evaluate at its terminal object.
private theorem small_largeSheafify_obj {C : Type v} [Category.{v} C] (J : GrothendieckTopology C)
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (U : C) :
    Small.{u} ((sheafify J (P ⋙ AddCommGrpCat.uliftFunctor.{v})).obj (Opposite.op U)) := by
  let := wEqualsLocallyBijective_large.{u, v} (J.over U)
  let L := AddCommGrpCat.uliftFunctor.{v, u}
  let F := (presheafToSheaf J AddCommGrpCat.{max u v}).obj (P ⋙ L)
  let P₀ := (Over.forget U).op ⋙ P
  let S := (presheafToSheaf (J.over U) AddCommGrpCat.{u}).obj P₀
  let T := (sheafCompose (J.over U) L).obj S
  let η := Functor.whiskerRight (toSheafify (J.over U) P₀) L
  have : Presheaf.IsLocallyInjective (J.over U) η := ulift_isLocallyInjective _ _
  have : Presheaf.IsLocallySurjective (J.over U) η := ulift_isLocallySurjective _ _
  let β := Functor.whiskerLeft (Over.forget U).op (toSheafify J (P ⋙ L))
  have : Presheaf.IsLocallyInjective (J.over U) β :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) _
  have : Presheaf.IsLocallySurjective (J.over U) β :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) _
  let F₀ := ((Over.forget U).sheafPushforwardContinuous AddCommGrpCat (J.over U) J).obj F
  let χ : F₀ ⟶ T := ⟨((((J.over U).W_of_isLocallyBijective β).homEquiv T.obj T.property).symm η)⟩
  have hfac : β ≫ χ.hom = η := by
    exact (((J.over U).W_of_isLocallyBijective β).homEquiv T.obj T.property).apply_symm_apply η
  have : Presheaf.IsLocallyInjective (J.over U) χ.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac _ η hfac
  have : Presheaf.IsLocallySurjective (J.over U) χ.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ hfac
  have : IsIso χ := (Sheaf.isLocallyBijective_iff_isIso χ).mp ⟨‹_›, ‹_›⟩
  have : IsIso χ.hom := (sheafToPresheaf _ _).map_isIso χ
  let i := asIso (χ.hom.app (Opposite.op (Over.mk (𝟙 U))))
  let : Small.{u} (T.obj.obj (Opposite.op (Over.mk (𝟙 U)))) :=
    small_map (Equiv.ulift.{v} :
      T.obj.obj (Opposite.op (Over.mk (𝟙 U))) ≃
        S.obj.obj (Opposite.op (Over.mk (𝟙 U))))
  exact small_map i.addCommGroupIsoToAddEquiv.toEquiv


-- Shrink the large sheafification objectwise, transporting the maps and the unit.
private theorem exists_locallyBijective_smallSheaf
    {C : Type v} [Category.{v} C] (J : GrothendieckTopology C)
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ∃ (S : Sheaf J AddCommGrpCat.{u}) (η : P ⟶ S.obj),
      Presheaf.IsLocallyInjective J η ∧ Presheaf.IsLocallySurjective J η := by
  let := hasSheafify_large.{u, v} J
  let := wEqualsLocallyBijective_large.{u, v} J
  let L := AddCommGrpCat.uliftFunctor.{v, u}
  let F := (presheafToSheaf J AddCommGrpCat.{max u v}).obj (P ⋙ L)
  let : ∀ X : Cᵒᵖ, Small.{u} (F.obj.obj X) := fun X ↦ small_largeSheafify_obj J P X.unop
  let S : Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
    { obj X := AddCommGrpCat.of (Shrink.{u} (F.obj.obj X))
      map {X Y} f := AddCommGrpCat.ofHom
        ((Shrink.addEquiv.symm.toAddMonoidHom).comp
          ((F.obj.map f).hom.comp Shrink.addEquiv.toAddMonoidHom))
      map_id X := by ext x; simp
      map_comp f g := by ext x; simp }
  let i : S ⋙ L ≅ F.obj := NatIso.ofComponents
    (fun X ↦ (AddEquiv.ulift.trans Shrink.addEquiv).toAddCommGrpIso)
    (fun f ↦ by
      ext x
      change Shrink.addEquiv (Shrink.addEquiv.symm (F.obj.map f (Shrink.addEquiv x.down))) = _
      exact Shrink.addEquiv.apply_symm_apply _)
  have hS : Presheaf.IsSheaf J S :=
    Presheaf.isSheaf_of_isSheaf_comp J S L
      ((Presheaf.isSheaf_of_iso_iff i).mpr F.property)
  let η : P ⟶ S :=
    { app X := AddCommGrpCat.ofHom
        (Shrink.addEquiv.symm.toAddMonoidHom.comp
          (((toSheafify J (P ⋙ L)).app X).hom.comp AddEquiv.ulift.symm.toAddMonoidHom))
      naturality X Y f := by
        apply ConcreteCategory.hom_ext
        intro x
        change Shrink.addEquiv.symm ((toSheafify J (P ⋙ L)).app Y (ULift.up (P.map f x))) =
          Shrink.addEquiv.symm
            (F.obj.map f (Shrink.addEquiv (Shrink.addEquiv.symm
              ((toSheafify J (P ⋙ L)).app X (ULift.up x)))))
        rw [AddEquiv.apply_symm_apply]
        exact congrArg Shrink.addEquiv.symm
          (NatTrans.naturality_apply (toSheafify J (P ⋙ L)) f (ULift.up x)) }
  refine ⟨⟨S, hS⟩, η, ?_, ?_⟩
  · constructor
    intro X x y h
    have hxy : (toSheafify J (P ⋙ L)).app _ (ULift.up x) =
        (toSheafify J (P ⋙ L)).app _ (ULift.up y) := by
      exact Shrink.addEquiv.symm.injective h
    have hc := Presheaf.equalizerSieve_mem J (toSheafify J (P ⋙ L)) _ _ hxy
    apply J.superset_covering _ hc
    intro W f hf
    exact congrArg ULift.down hf
  · constructor
    intro X x
    have hc := Presheaf.imageSieve_mem J (toSheafify J (P ⋙ L)) (Shrink.addEquiv x)
    apply J.superset_covering _ hc
    intro W f hf
    obtain ⟨y, hy⟩ := hf
    refine ⟨y.down, ?_⟩
    change Shrink.addEquiv.symm ((toSheafify J (P ⋙ L)).app _ y) =
      Shrink.addEquiv.symm (F.obj.map f.op (Shrink.addEquiv x))
    exact congrArg Shrink.addEquiv.symm hy


-- Mathlib transports the scalar action along the locally bijective abelian unit.
private theorem exists_locallyInjective_moduleSheaf
    {C : Type v} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (P : PresheafOfModules.{u} R.obj) :
    ∃ (Q : SheafOfModules.{u} R) (η : P ⟶ Q.val),
      PresheafOfModules.IsLocallyInjective J η := by
  obtain ⟨S, η, hη₁, hη₂⟩ := exists_locallyBijective_smallSheaf J P.presheaf
  let : Presheaf.IsLocallyInjective J η := hη₁
  let : Presheaf.IsLocallySurjective J η := hη₂
  exact ⟨PresheafOfModules.sheafify (𝟙 R.obj) η,
    PresheafOfModules.toSheafify (𝟙 R.obj) η, inferInstance⟩

/-- Restriction to an over-site preserves epimorphisms.
Source: Stacks Project, Modules, Lemma 01BY, local lifting argument.
An epimorphism of sheaves is locally surjective; pulling a local lift back along
an object of the over-site gives the same local lift there. We apply the
locally-surjective characterization of epimorphisms on the over-site, after
pulling back the covering and lift. (blueprint: lem-stage3-epi-over-functor) -/
theorem epi_overFunctor_map
    {C : Type v} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {A B : SheafOfModules.{u} R} (e : A ⟶ B) [Epi e] (U : C) :
    Epi ((SheafOfModules.overFunctor R U).map e) := by
  -- The sheafified presheaf cokernel detects the local image of e.
  let P := cokernel e.val
  let p := cokernel.π e.val
  obtain ⟨Q, η, hη⟩ := exists_locallyInjective_moduleSheaf P
  let q : B ⟶ Q := ⟨p ≫ η⟩
  have heq : e ≫ q = 0 := by
    ext1
    change e.val ≫ p ≫ η = 0
    rw [← Category.assoc, cokernel.condition, zero_comp]
  have hq : q = 0 := by
    apply (cancel_epi e).mp
    simpa using heq
  -- Presheaf cokernels are computed pointwise in the abelian module categories.
  have hexact (V : Cᵒᵖ) (s : B.val.obj V) (hs : p.app V s = 0) :
      ∃ t : A.val.obj V, e.val.app V t = s := by
    let S := ShortComplex.mk e.val p (cokernel.condition e.val)
    have hS : S.Exact := S.exact_of_g_is_cokernel (cokernelIsCokernel e.val)
    exact (ShortComplex.moduleCat_exact_iff _).mp
      (hS.map (PresheafOfModules.evaluation R.obj V)) s hs
  have he : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map e.val) := by
    constructor
    intro V s
    have hs : η.app (Opposite.op V) (p.app (Opposite.op V) s) =
        η.app (Opposite.op V) 0 := by
      have hz := congrArg (fun f : B ⟶ Q ↦ f.val.app (Opposite.op V) s) hq
      change η.app (Opposite.op V) (p.app (Opposite.op V) s) = 0 at hz
      simpa only [map_zero] using hz
    have hc := Presheaf.equalizerSieve_mem J
      ((PresheafOfModules.toPresheaf R.obj).map η) _ _ hs
    apply J.superset_covering _ hc
    intro W f hf
    apply hexact
    have hn := PresheafOfModules.naturality_apply p f.op s
    change P.map f.op (p.app (Opposite.op V) s) = P.map f.op 0 at hf
    rw [map_zero] at hf
    exact hn.trans hf
  -- Restriction along the cocontinuous over-site forgetful functor preserves local lifts.
  have hres := Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U)
    ((PresheafOfModules.toPresheaf R.obj).map e.val)
  have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf (R.over U)).map
      ((SheafOfModules.overFunctor R U).map e)) := hres
  exact (SheafOfModules.toSheaf (R.over U)).epi_of_epi_map inferInstance

end
