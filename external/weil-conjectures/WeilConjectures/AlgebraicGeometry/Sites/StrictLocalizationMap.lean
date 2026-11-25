/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Representable
public import WeilConjectures.AlgebraicGeometry.Sites.Cospecialization
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Representable

/-!
# Functoriality of the strict localization

Let `g: S' ⟶ S` be a morphism of schemes and `s': Spec Ω ⟶ S'` a geometric point. Pulling
back a pointed étale neighbourhood `(V, v)` of `s' ≫ g` along `g` gives the pointed étale
neighbourhood `(V ×_S S', (v, s'))` of `s'`. Hence the legs of the limit cone of
`S'_(s')` give a cone over the affine pointed étale neighbourhoods of `s' ≫ g`, and we obtain
the morphism `strictLocalizationMap g s': S'_(s') ⟶ S_(s' ≫ g)` over `g`, compatible with the
canonical geometric points.

## Main definitions

- `AlgebraicGeometry.Scheme.PointedEtaleNeighborhood.pullback g s'`: base change of pointed étale
  neighbourhoods along `g`.
- `AlgebraicGeometry.Scheme.strictLocalizationMap g s'`: the morphism `S'_(s') ⟶ S_(s' ≫ g)`.

## Main results

- `AlgebraicGeometry.Scheme.strictLocalizationMap_comp_strictLocalizationToBase`.
- `AlgebraicGeometry.Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationMap`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {S S' : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

namespace PointedEtaleNeighborhood

variable (g : S' ⟶ S) (s' : Spec (.of Ω) ⟶ S')

/-- The base change `(V ×_S S', (v, s'))` of a pointed étale neighbourhood `(V, v)` of `s' ≫ g`
along `g`, a pointed étale neighbourhood of `s'`. -/
noncomputable def pullbackObj (x : PointedEtaleNeighborhood (s' ≫ g)) :
    PointedEtaleNeighborhood s' :=
  { obj := Etale.mk (pullback.snd x.1.hom g)
    val := CategoryTheory.Over.homMk (pullback.lift x.2.left s' (CategoryTheory.Over.w x.2))
      (pullback.lift_snd _ _ _) }

lemma pullbackObj_snd_left (x : PointedEtaleNeighborhood (s' ≫ g)) :
    (pullbackObj g s' x).2.left = pullback.lift x.2.left s' (CategoryTheory.Over.w x.2) :=
  rfl


/-- Base change of pointed étale neighbourhoods along `g : S' ⟶ S`. -/
@[simps obj]
noncomputable def pullback :
    PointedEtaleNeighborhood (s' ≫ g) ⥤ PointedEtaleNeighborhood s' where
  obj := pullbackObj g s'
  map {x y} f := ⟨MorphismProperty.Over.homMk
      (pullback.map x.1.hom g y.1.hom g f.1.left (𝟙 _) (𝟙 _)
        (by simp) (by simp)) ((pullback.lift_snd _ _ _).trans (Category.comp_id _)), by
      have e {T : Scheme.{u}} (t : Spec (.of Ω) ⟶ T) {X Y : T.Etale} (φ : X ⟶ Y)
          (a : (pointSmallEtale t).fiber.obj X) :
          ((pointSmallEtale t).fiber.map φ a).left = a.left ≫ φ.left := rfl
      refine CategoryTheory.Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
      · have h := (e _ _ _).symm.trans (congrArg CommaMorphism.left f.2)
        simp [pullbackObj, e, h]
      · simp [pullbackObj, e]⟩
  map_id x := by
    apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext <;>
      simp only [Functor.id_obj, Functor.const_obj_obj, Functor.Elements.id_hom, Etale.id_left_eq,
        pullback.map_id, MorphismProperty.Over.homMk_hom, Over.homMk_left] <;>
      exact Category.id_comp _
  map_comp f g := by
    apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext <;> simp [Functor.Elements.comp_hom]

end PointedEtaleNeighborhood

section Eval

variable (s : Spec (.of Ω) ⟶ S)

/-- The leg `S_(s) ⟶ V` of the limit cone of the strict localization at an arbitrary pointed
étale neighbourhood `(V, v)` of `s`. -/
noncomputable def strictLocalizationLeg (y : PointedEtaleNeighborhood s) :
    strictLocalization s ⟶ (neighborhoodDiagram s).obj y :=
  (strictLocalizationConeAll s).π.app y

@[reassoc]
lemma strictLocalizationLeg_comp {y z : PointedEtaleNeighborhood s} (f : y ⟶ z) :
    strictLocalizationLeg s y ≫ (neighborhoodDiagram s).map f = strictLocalizationLeg s z :=
  (strictLocalizationConeAll s).w f

/-- The leg of the limit cone of `S_(s)` at a pointed étale neighbourhood `(V, v)`, followed by
the structure morphism `V ⟶ S`, is the structure morphism `S_(s) ⟶ S`. -/
@[reassoc (attr := simp)]
lemma strictLocalizationLeg_hom (y : PointedEtaleNeighborhood s) :
    strictLocalizationLeg s y ≫ y.1.hom = strictLocalizationToBase s :=
  (strictLocalizationConeAll s).w (PointedEtaleNeighborhood.toBase s y)

set_option backward.isDefEq.respectTransparency false in
/-- The lift `v : Spec Ω ⟶ V` of the geometric point to any pointed étale neighbourhood `(V, v)`
is the composite of `Spec` of the evaluation map with the leg `S_(s) ⟶ V` of the limit cone. -/
@[reassoc]
lemma spec_map_strictHenselizationEval_comp_strictLocalizationLeg
    (y : PointedEtaleNeighborhood s) :
    Spec.map (strictHenselizationEval s) ≫ strictLocalizationLeg s y = y.2.left := by
  obtain ⟨z, ⟨f⟩⟩ := AffinePointedEtaleNeighborhood.exists_hom s y
  rw [← strictLocalizationLeg_comp s f, strictLocalizationLeg]
  have h : (strictLocalizationConeAll s).π.app ((AffinePointedEtaleNeighborhood.ι s).obj z) =
      (strictLocalizationCone s).π.app z :=
    (Functor.Initial.extendCone_obj_π_app' (F := AffinePointedEtaleNeighborhood.ι s) _
      (𝟙 _)).trans (Category.comp_id _)
  rw [h, spec_map_strictHenselizationEval_comp_strictLocalizationCone_π_app_assoc]
  exact congrArg CommaMorphism.left f.2

end Eval

variable (g : S' ⟶ S) (s' : Spec (.of Ω) ⟶ S')

/-- The leg `S'_(s') ⟶ V ×_S S' ⟶ V` attached to an affine pointed étale neighbourhood `(V, v)`
of `s' ≫ g`. -/
noncomputable def strictLocalizationMapCone : Cone (affineNeighborhoodDiagram (s' ≫ g)) where
  pt := strictLocalization s'
  π :=
    { app x := strictLocalizationLeg s'
          ((PointedEtaleNeighborhood.pullback g s').obj
            ((AffinePointedEtaleNeighborhood.ι _).obj x)) ≫ pullback.fst x.obj.1.hom g
      naturality x y f := by
        refine (Category.id_comp _).trans ?_
        rw [← strictLocalizationLeg_comp s'
          ((PointedEtaleNeighborhood.pullback g s').map
            ((AffinePointedEtaleNeighborhood.ι _).map f))]
        simp only [Category.assoc]
        congr 1
        exact pullback.lift_fst _ _ _ }

/-- **Functoriality of the strict localization**: the morphism `S'_(s') ⟶ S_(s' ≫ g)` induced
by `g: S' ⟶ S`, given by the base change of pointed étale neighbourhoods along `g`. -/
noncomputable def strictLocalizationMap : strictLocalization s' ⟶ strictLocalization (s' ≫ g) :=
  (isLimitStrictLocalizationCone (s' ≫ g)).lift (strictLocalizationMapCone g s')

@[reassoc (attr := simp)]
lemma strictLocalizationMap_comp_strictLocalizationCone_π_app
    (x : AffinePointedEtaleNeighborhood (s' ≫ g)) :
    strictLocalizationMap g s' ≫ (strictLocalizationCone (s' ≫ g)).π.app x =
      strictLocalizationLeg s'
          ((PointedEtaleNeighborhood.pullback g s').obj
            ((AffinePointedEtaleNeighborhood.ι _).obj x)) ≫ pullback.fst x.obj.1.hom g :=
  (isLimitStrictLocalizationCone (s' ≫ g)).fac _ x

/-- The morphism `strictLocalizationMap g s'` lies over `g`. -/
@[reassoc (attr := simp)]
lemma strictLocalizationMap_comp_strictLocalizationToBase :
    strictLocalizationMap g s' ≫ strictLocalizationToBase (s' ≫ g) =
      strictLocalizationToBase s' ≫ g := by
  obtain ⟨x⟩ := IsCofiltered.nonempty (C := AffinePointedEtaleNeighborhood (s' ≫ g))
  rw [← strictLocalizationCone_π_app_hom _ x,
    strictLocalizationMap_comp_strictLocalizationCone_π_app_assoc,
    ← strictLocalizationLeg_hom s' ((PointedEtaleNeighborhood.pullback g s').obj
      ((AffinePointedEtaleNeighborhood.ι _).obj x)), Category.assoc]
  congr 1
  exact pullback.condition

/-- The morphism `strictLocalizationMap g s'` carries the canonical geometric point of `S'_(s')`
to the canonical geometric point of `S_(s' ≫ g)`. -/
@[reassoc (attr := simp)]
lemma spec_map_strictHenselizationEval_comp_strictLocalizationMap :
    Spec.map (strictHenselizationEval s') ≫ strictLocalizationMap g s' =
      Spec.map (strictHenselizationEval (s' ≫ g)) := by
  refine (isLimitStrictLocalizationCone (s' ≫ g)).hom_ext fun x ↦ ?_
  rw [Category.assoc, strictLocalizationMap_comp_strictLocalizationCone_π_app,
    spec_map_strictHenselizationEval_comp_strictLocalizationLeg_assoc,
    spec_map_strictHenselizationEval_comp_strictLocalizationCone_π_app]
  exact pullback.lift_fst _ _ _

end AlgebraicGeometry.Scheme
