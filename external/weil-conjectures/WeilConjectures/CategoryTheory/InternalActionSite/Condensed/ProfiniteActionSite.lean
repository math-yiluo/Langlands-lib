/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionSiteBasic
public import WeilConjectures.CategoryTheory.CondensedBar.CondensedEquivariantBarData
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Condensed.TopComparison
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-!
# The small profinite site for internal condensed actions

Source: paragraph (3) of the direct-image stability proof, action-site presentation
(blueprint: def-sfb-condensed-derived-invariants).

We replace `Profinite.{u}` by its small model `AsSmall.{u + 1} Profinite.{u}`, carrying the
transported coherent topology, presented by the precoverage of all covering presieves. On
this small site we record the group presheaf `S ↦ C(S, G)` of a topological group, which is
a sheaf, and the section ring sheaf of an internal condensed ring.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CondensedBar.ActionSite

/-- The small model of the profinite site: same objects, morphisms lifted to `Type (u + 1)`. -/
abbrev Model : Type (u + 1) := AsSmall.{u + 1} Profinite.{u}

/-- The coherent topology transported to the small model. -/
abbrev modelTopology : GrothendieckTopology Model.{u} :=
  (AsSmall.down : Model.{u} ⥤ Profinite.{u}).inducedTopology (coherentTopology Profinite.{u})

/-- The precoverage of all presieves generating a covering sieve of the model topology. -/
abbrev modelPrecoverage : Precoverage Model.{u} :=
  modelTopology.toPrecoverage

/-- The model precoverage generates the transported coherent topology. -/
theorem modelPrecoverage_toGrothendieck :
    modelPrecoverage.{u}.toGrothendieck = modelTopology := by
  apply le_antisymm
  · exact GrothendieckTopology.toGrothendieck_toPrecoverage_le _
  · intro X S hS
    rw [← Sieve.generate_sieve S]
    exact Precoverage.generate_mem_toGrothendieck
      ((GrothendieckTopology.arrows_mem_toPrecoverage_iff _ S).2 hS)

/-- The small model has finite limits, transported from `Profinite`. -/
instance model_hasFiniteLimits : HasFiniteLimits Model.{u} :=
  ⟨fun _ _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence
    (AsSmall.equiv.{u, u + 1, u + 1} (C := Profinite.{u})).inverse⟩

/-- The model precoverage satisfies the covering axioms of a site. -/
theorem modelPrecoverage_isSiteForCoverings : modelPrecoverage.{u}.IsSiteForCoverings := by
  refine ⟨inferInstanceAs (modelTopology.toPrecoverage.HasIsos), ?_, ?_⟩
  · intro X R P hR hP
    exact modelTopology.toPrecoverage_bind_mem R P hR hP
  · intro I X U a ha Y b
    refine ⟨fun i ↦ pullback b (a i), fun i ↦ pullback.fst _ _, fun i ↦ pullback.snd _ _,
      fun i ↦ IsPullback.of_hasPullback _ _, ?_⟩
    exact Precoverage.IsStableUnderBaseChange.mem_coverings_of_isPullback
      a ha b _ _ (fun i ↦ IsPullback.of_hasPullback _ _)

/-- The projection to `Profinite` is continuous for the generated topology. -/
instance down_isContinuous :
    (AsSmall.down : Model.{u} ⥤ Profinite.{u}).IsContinuous
      modelPrecoverage.{u}.toGrothendieck (coherentTopology Profinite.{u}) := by
  rw [modelPrecoverage_toGrothendieck]
  infer_instance

/-- The inclusion of `Profinite` in its small model is continuous for the generated
topology. -/
instance up_isContinuous :
    (AsSmall.up : Profinite.{u} ⥤ Model.{u}).IsContinuous
      (coherentTopology Profinite.{u}) modelPrecoverage.{u}.toGrothendieck := by
  rw [modelPrecoverage_toGrothendieck]
  exact inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := Profinite.{u})).functor.IsContinuous
    (coherentTopology Profinite.{u})
      ((AsSmall.equiv.{u, u + 1, u + 1} (C := Profinite.{u})).inverse.inducedTopology
        (coherentTopology Profinite.{u})))

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The group presheaf of continuous maps `S ↦ C(S, G)` on the small model. -/
def groupPresheaf : Model.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of
    (ULift.{u + 1} C((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop, G))
  map f := GrpCat.ofHom
    { toFun := fun g ↦
        ⟨g.down.comp ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).map f.unop).hom.hom⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }

@[simp]
theorem groupPresheaf_map_down {X Y : Model.{u}ᵒᵖ} (f : X ⟶ Y)
    (g : (groupPresheaf G).obj X) :
    ((groupPresheaf G).map f g).down =
      g.down.comp ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).map f.unop).hom.hom :=
  rfl

/-- Sections of the group presheaf are continuous maps to `G`. -/
def groupPresheafObjEquiv (X : Model.{u}ᵒᵖ) :
    (groupPresheaf G).obj X ≃* C((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop, G) :=
  MulEquiv.ulift

/-- Continuous maps on a profinite set are sections of the group presheaf at its model. -/
def groupPresheafUpEquiv (S : Profinite.{u}) :
    C(S, G) ≃* (groupPresheaf G).obj (op ((AsSmall.up : Profinite.{u} ⥤ Model.{u}).obj S)) :=
  MulEquiv.ulift.symm

/-- The sheaf of continuous maps to `G` on `Profinite`. -/
noncomputable abbrev continuousMapSheaf :
    Sheaf (coherentTopology Profinite.{u}) (Type u) :=
  TopCat.toSheafCompHausLike.{u, u} (fun X ↦ TotallyDisconnectedSpace X) (TopCat.of G)
    (fun _ _ f h ↦ ((Profinite.effectiveEpi_tfae f).out 1 3).mp h)

/-- The group presheaf is a sheaf on the small model. -/
theorem groupPresheaf_isSheaf :
    Presheaf.IsSheaf modelPrecoverage.{u}.toGrothendieck
      (groupPresheaf G ⋙ forget GrpCat.{u + 1}) := by
  have h := Functor.op_comp_isSheaf (AsSmall.down : Model.{u} ⥤ Profinite.{u})
    modelPrecoverage.{u}.toGrothendieck (coherentTopology Profinite.{u})
    ((sheafCompose (coherentTopology Profinite.{u}) uliftFunctor.{u + 1, u}).obj
      (continuousMapSheaf G))
  refine (Presheaf.isSheaf_of_iso_iff ?_).1 h
  exact NatIso.ofComponents (fun X ↦ Equiv.toIso (Equiv.refl _)) (fun _ ↦ rfl)

variable (A : Ring.{u})

/-- The section ring sheaf of an internal condensed ring, on the small model. -/
noncomputable def ringSheaf : Sheaf modelPrecoverage.{u}.toGrothendieck CommRingCat.{u + 1} :=
  ⟨AsSmall.down.op ⋙
      (InternalAbelianSheafModule.sectionRingSheaf (coherentTopology Profinite.{u}) A.X).obj,
    Functor.op_comp_isSheaf _ _ _ _⟩

end CategoryTheory.CondensedBar.ActionSite
