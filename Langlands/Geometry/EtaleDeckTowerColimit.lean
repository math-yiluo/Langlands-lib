import Langlands.Geometry.EtaleCanonicalDeckTower
import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.SmoothPart.Definitions
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Level colimits of canonical deck-tower cohomology and their smoothness -/

noncomputable section

universe u v w t wS wR

set_option autoImplicit false

namespace Langlands

open CategoryTheory CategoryTheory.Limits

section SmoothAction

variable {R : Type u} [CommRing R] {G : Type t} [Group G] [TopologicalSpace G]

/-- An action on a module in which an open subgroup acts by the identity is smooth. -/
theorem isSmooth_actionToRep_of_open_trivial (V : Action (ModuleCat.{u} R) G)
    (U : OpenSubgroup G) (hU : ∀ g ∈ U, V.ρ g = 𝟙 V.V) :
    IsSmooth ((Rep.ActionToRep R G).obj V).ρ := by
  intro v
  refine ⟨U, ?_⟩
  intro g
  change (V.ρ (g : G)).hom v = v
  rw [hU g g.property]
  rfl

/-- A colimit of module actions is smooth when each vertex has an open subgroup
acting by the identity. No filteredness of the indexing category is used. -/
theorem isSmooth_actionToRep_colimit {K : Type v} [Category.{w} K]
    [HasColimitsOfShape K (ModuleCat.{u} R)] (D : K ⥤ Action (ModuleCat.{u} R) G)
    (hD : ∀ i, ∃ U : OpenSubgroup G, ∀ g ∈ U, (D.obj i).ρ g = 𝟙 (D.obj i).V) :
    IsSmooth ((Rep.ActionToRep R G).obj (colimit D)).ρ := by
  let S : Submodule R (colimit D).V := smoothVectors ((Rep.ActionToRep R G).obj (colimit D)).ρ
  have hι : ∀ (i : K) (x : (D.obj i).V), (colimit.ι D i).hom.hom x ∈ S := by
    intro i x
    obtain ⟨U, hU⟩ := hD i
    refine ⟨U, ?_⟩
    intro g
    change ((colimit D).ρ (g : G)).hom ((colimit.ι D i).hom.hom x) = (colimit.ι D i).hom.hom x
    have h := congrArg (fun f => f.hom x) ((colimit.ι D i).comm (g : G))
    rw [hU g g.property] at h
    exact h.symm
  have hc := isColimitOfPreserves (Action.forget (ModuleCat.{u} R) G) (colimit.isColimit D)
  have h0 : (ModuleCat.ofHom S.mkQ : (colimit D).V ⟶ ModuleCat.of R ((colimit D).V ⧸ S)) = 0 := by
    apply hc.hom_ext
    intro i
    rw [Limits.comp_zero]
    ext x
    exact (Submodule.Quotient.mk_eq_zero S).mpr (hι i x)
  have hS : S = ⊤ := by
    rw [← Submodule.ker_mkQ S]
    have h1 : S.mkQ = 0 := congrArg ModuleCat.Hom.hom h0
    rw [h1, LinearMap.ker_zero]
  have hv : ∀ w : (colimit D).V, w ∈ S := fun w => hS ▸ Submodule.mem_top
  exact hv

end SmoothAction

/-- When the forgetful functor of modules preserves colimits of shape `K`, every
vector of a colimit of module actions comes from some vertex. -/
theorem actionColimit_exists_rep {R : Type u} [CommRing R] {G : Type t} [Group G]
    {K : Type v} [Category.{w} K] [HasColimitsOfShape K (ModuleCat.{u} R)]
    [PreservesColimitsOfShape K (forget (ModuleCat.{u} R))]
    (D : K ⥤ Action (ModuleCat.{u} R) G) (x : (colimit D).V) :
    ∃ (i : K) (y : (D.obj i).V), (colimit.ι D i).hom.hom y = x := by
  obtain ⟨i, y, hy⟩ := Concrete.isColimit_exists_rep (D ⋙ Action.forget (ModuleCat.{u} R) G)
    (isColimitOfPreserves (Action.forget (ModuleCat.{u} R) G) (colimit.isColimit D)) x
  exact ⟨i, y, hy⟩

end Langlands

namespace Langlands.Geometry.EtaleCanonicalDeckTower

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EtaleGeometricDiagram EtaleDerivedSections EtaleInverseImage

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme.{u}} {J : Type v} [Category.{w} J]
variable {G : Type t} [Group G]
variable (R : Type u) [CommRing R] (A : J ⥤ Action ((Over X)ᵒᵖ) G)

/-- Every level of the original geometric tower has an open subgroup acting
by the identity over-base automorphism. -/
def IsLevelwiseSmooth [TopologicalSpace G] : Prop :=
  ∀ i : J, ∃ U : OpenSubgroup G, ∀ g ∈ U, (A.obj i).ρ g = 𝟙 (A.obj i).V

section Cohomology

variable [∀ x : J × SingleObj G,
  HasDerivedCategory.{wS} (ModuleSheaf ((schemeDiagram A).obj x).unop R)]
variable [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

local instance etaleDeckTowerColimitInst1 (i : J) :
    HasDerivedCategory.{wS} (ModuleSheaf (A.obj i).V.unop.left R) :=
  inferInstanceAs (HasDerivedCategory.{wS}
    (ModuleSheaf ((schemeDiagram A).obj (i, SingleObj.star G)).unop R))

/-- The ordinary cohomology action depends on a group element only through its
original deck automorphism. -/
theorem cohomologyFunctor_obj_obj_ρ_congr (q : ℕ) (M : ModuleSheaf X R) (i : J)
    {g h : G} (hgh : (A.obj i).ρ g = (A.obj i).ρ h) :
    (((cohomologyFunctor R A q).obj M).obj i).ρ g =
      (((cohomologyFunctor R A q).obj M).obj i).ρ h := by
  rw [cohomologyFunctor_obj_obj_ρ, cohomologyFunctor_obj_obj_ρ]
  have key : ∀ e e' : (A.obj i).V ⟶ (A.obj i).V, e = e' →
      EtaleDerivedGlobalPullback.cohomologyPullbackWithCoefficients e.unop.left R q
          ((projectionInverseImageIso R _ _ _ (Over.w e.unop)).hom.app M) =
        EtaleDerivedGlobalPullback.cohomologyPullbackWithCoefficients e'.unop.left R q
          ((projectionInverseImageIso R _ _ _ (Over.w e'.unop)).hom.app M) := by
    rintro e _ rfl
    rfl
  exact key _ _ hgh

/-- The section action depends on a group element only through its original
deck automorphism. -/
theorem sectionsFunctor_obj_obj_ρ_congr (M : ModuleSheaf X R) (i : J)
    {g h : G} (hgh : (A.obj i).ρ g = (A.obj i).ρ h) :
    (((sectionsFunctor R A).obj M).obj i).ρ g =
      (((sectionsFunctor R A).obj M).obj i).ρ h := by
  rw [sectionsFunctor_obj_obj_ρ, sectionsFunctor_obj_obj_ρ]
  have key : ∀ e e' : (A.obj i).V ⟶ (A.obj i).V, e = e' →
      EtaleDerivedGlobalPullback.sectionsPullbackWithCoefficients e.unop.left R
          ((projectionInverseImageIso R _ _ _ (Over.w e.unop)).hom.app M) =
        EtaleDerivedGlobalPullback.sectionsPullbackWithCoefficients e'.unop.left R
          ((projectionInverseImageIso R _ _ _ (Over.w e'.unop)).hom.app M) := by
    rintro e _ rfl
    rfl
  exact key _ _ hgh

/-- A group element acting trivially on the original level geometry acts
trivially on its ordinary cohomology. -/
theorem cohomologyFunctor_obj_obj_ρ_eq_id (q : ℕ) (M : ModuleSheaf X R) (i : J)
    {g : G} (hg : (A.obj i).ρ g = 𝟙 (A.obj i).V) :
    (((cohomologyFunctor R A q).obj M).obj i).ρ g = 𝟙 _ := by
  have h1 : (A.obj i).ρ g = (A.obj i).ρ 1 := by
    rw [hg, map_one]
    rfl
  rw [cohomologyFunctor_obj_obj_ρ_congr R A q M i h1, map_one]
  rfl

/-- A group element acting trivially on the original level geometry acts
trivially on its global sections. -/
theorem sectionsFunctor_obj_obj_ρ_eq_id (M : ModuleSheaf X R) (i : J)
    {g : G} (hg : (A.obj i).ρ g = 𝟙 (A.obj i).V) :
    (((sectionsFunctor R A).obj M).obj i).ρ g = 𝟙 _ := by
  have h1 : (A.obj i).ρ g = (A.obj i).ρ 1 := by
    rw [hg, map_one]
    rfl
  rw [sectionsFunctor_obj_obj_ρ_congr R A M i h1, map_one]
  rfl

section Colimit

variable [HasColimitsOfShape J (ModuleCat.{u} R)]

/-- Ordinary cohomology of the canonical coefficients, in the colimit over levels. -/
def colimitCohomologyFunctor (q : ℕ) : ModuleSheaf X R ⥤ Action (ModuleCat.{u} R) G :=
  cohomologyFunctor R A q ⋙ colim

/-- Global sections of the canonical coefficients, in the colimit over levels. -/
def colimitSectionsFunctor : ModuleSheaf X R ⥤ Action (ModuleCat.{u} R) G :=
  sectionsFunctor R A ⋙ colim

/-- The levelwise degree-zero recovery passes to the colimit over levels. -/
def colimitCohomologyZeroIso :
    colimitCohomologyFunctor R A 0 ≅ colimitSectionsFunctor R A :=
  Functor.isoWhiskerRight (cohomologyZeroFunctorIso R A) colim

/-- The equivariant inclusion of one level into the colimit cohomology. -/
def levelCohomologyι (q : ℕ) (i : J) :
    cohomologyFunctor R A q ⋙ (evaluation J (Action (ModuleCat.{u} R) G)).obj i ⟶
      colimitCohomologyFunctor R A q where
  app M := colimit.ι ((cohomologyFunctor R A q).obj M) i
  naturality M N α := by
    change ((cohomologyFunctor R A q).map α).app i ≫ _ =
      colimit.ι _ i ≫ colimMap ((cohomologyFunctor R A q).map α)
    rw [ι_colimMap]

/-- The equivariant inclusion of one level into the colimit sections. -/
def levelSectionsι (i : J) :
    sectionsFunctor R A ⋙ (evaluation J (Action (ModuleCat.{u} R) G)).obj i ⟶
      colimitSectionsFunctor R A where
  app M := colimit.ι ((sectionsFunctor R A).obj M) i
  naturality M N α := by
    change ((sectionsFunctor R A).map α).app i ≫ _ =
      colimit.ι _ i ≫ colimMap ((sectionsFunctor R A).map α)
    rw [ι_colimMap]

@[simp] theorem levelCohomologyι_app (q : ℕ) (i : J) (M : ModuleSheaf X R) :
    (levelCohomologyι R A q i).app M = colimit.ι ((cohomologyFunctor R A q).obj M) i := rfl

@[simp] theorem levelSectionsι_app (i : J) (M : ModuleSheaf X R) :
    (levelSectionsι R A i).app M = colimit.ι ((sectionsFunctor R A).obj M) i := rfl

/-- Level inclusions are compatible with the original level maps. -/
theorem levelCohomologyι_w (q : ℕ) {i j : J} (a : i ⟶ j) :
    Functor.whiskerLeft (cohomologyFunctor R A q)
        ((evaluation J (Action (ModuleCat.{u} R) G)).map a) ≫
      levelCohomologyι R A q j = levelCohomologyι R A q i := by
  ext M : 2
  exact colimit.w ((cohomologyFunctor R A q).obj M) a

theorem levelSectionsι_w {i j : J} (a : i ⟶ j) :
    Functor.whiskerLeft (sectionsFunctor R A)
        ((evaluation J (Action (ModuleCat.{u} R) G)).map a) ≫
      levelSectionsι R A j = levelSectionsι R A i := by
  ext M : 2
  exact colimit.w ((sectionsFunctor R A).obj M) a

/-- Degree-zero recovery on the colimit restricts to the levelwise recovery. -/
theorem levelCohomologyι_zero (i : J) :
    levelCohomologyι R A 0 i ≫ (colimitCohomologyZeroIso R A).hom =
      Functor.whiskerRight (cohomologyZeroFunctorIso R A).hom
          ((evaluation J (Action (ModuleCat.{u} R) G)).obj i) ≫
        levelSectionsι R A i := by
  ext M : 2
  change colimit.ι _ i ≫ colimMap ((cohomologyZeroFunctorIso R A).hom.app M) = _
  rw [ι_colimMap]
  rfl

/-- The colimit action is characterized on each level by the level action. -/
theorem levelCohomologyι_comm (q : ℕ) (i : J) (M : ModuleSheaf X R) (g : G) :
    (((cohomologyFunctor R A q).obj M).obj i).ρ g ≫
        ((levelCohomologyι R A q i).app M).hom =
      ((levelCohomologyι R A q i).app M).hom ≫
        ((colimitCohomologyFunctor R A q).obj M).ρ g :=
  ((levelCohomologyι R A q i).app M).comm g

theorem levelSectionsι_comm (i : J) (M : ModuleSheaf X R) (g : G) :
    (((sectionsFunctor R A).obj M).obj i).ρ g ≫ ((levelSectionsι R A i).app M).hom =
      ((levelSectionsι R A i).app M).hom ≫ ((colimitSectionsFunctor R A).obj M).ρ g :=
  ((levelSectionsι R A i).app M).comm g

/-- The underlying module of the colimit cohomology is the colimit of the
underlying level cohomology modules, naturally in every base coefficient. -/
def colimitCohomologyForgetIso (q : ℕ) :
    colimitCohomologyFunctor R A q ⋙ Action.forget (ModuleCat.{u} R) G ≅
      cohomologyFunctor R A q ⋙
        (Functor.whiskeringRight J _ _).obj (Action.forget (ModuleCat.{u} R) G) ⋙ colim :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (cohomologyFunctor R A q)
      (preservesColimitNatIso (Action.forget (ModuleCat.{u} R) G))

/-- The underlying module of the colimit sections is the colimit of the level
section modules, naturally in every base coefficient. -/
def colimitSectionsForgetIso :
    colimitSectionsFunctor R A ⋙ Action.forget (ModuleCat.{u} R) G ≅
      sectionsFunctor R A ⋙
        (Functor.whiskeringRight J _ _).obj (Action.forget (ModuleCat.{u} R) G) ⋙ colim :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sectionsFunctor R A)
      (preservesColimitNatIso (Action.forget (ModuleCat.{u} R) G))

/-- The underlying comparison sends each level module by its colimit inclusion. -/
theorem levelCohomologyι_colimitCohomologyForgetIso (q : ℕ) (i : J) (M : ModuleSheaf X R) :
    ((levelCohomologyι R A q i).app M).hom ≫ (colimitCohomologyForgetIso R A q).hom.app M =
      colimit.ι ((cohomologyFunctor R A q).obj M ⋙ Action.forget (ModuleCat.{u} R) G) i := by
  change ((levelCohomologyι R A q i).app M).hom ≫
    𝟙 _ ≫ (preservesColimitNatIso (Action.forget (ModuleCat.{u} R) G)).hom.app _ = _
  rw [Category.id_comp]
  exact ι_preservesColimitIso_hom (Action.forget (ModuleCat.{u} R) G)
    ((cohomologyFunctor R A q).obj M) i

theorem levelSectionsι_colimitSectionsForgetIso (i : J) (M : ModuleSheaf X R) :
    ((levelSectionsι R A i).app M).hom ≫ (colimitSectionsForgetIso R A).hom.app M =
      colimit.ι ((sectionsFunctor R A).obj M ⋙ Action.forget (ModuleCat.{u} R) G) i := by
  change ((levelSectionsι R A i).app M).hom ≫
    𝟙 _ ≫ (preservesColimitNatIso (Action.forget (ModuleCat.{u} R) G)).hom.app _ = _
  rw [Category.id_comp]
  exact ι_preservesColimitIso_hom (Action.forget (ModuleCat.{u} R) G)
    ((sectionsFunctor R A).obj M) i

/-- When module colimits of the level shape are computed on underlying sets,
every colimit cohomology class comes from some finite level. -/
theorem levelCohomologyι_exists_rep [PreservesColimitsOfShape J (forget (ModuleCat.{u} R))]
    (q : ℕ) (M : ModuleSheaf X R) (x : ((colimitCohomologyFunctor R A q).obj M).V) :
    ∃ (i : J) (y : (((cohomologyFunctor R A q).obj M).obj i).V),
      ((levelCohomologyι R A q i).app M).hom.hom y = x :=
  actionColimit_exists_rep ((cohomologyFunctor R A q).obj M) x

/-- When module colimits of the level shape are computed on underlying sets,
every colimit global section comes from some finite level. -/
theorem levelSectionsι_exists_rep [PreservesColimitsOfShape J (forget (ModuleCat.{u} R))]
    (M : ModuleSheaf X R) (x : ((colimitSectionsFunctor R A).obj M).V) :
    ∃ (i : J) (y : (((sectionsFunctor R A).obj M).obj i).V),
      ((levelSectionsι R A i).app M).hom.hom y = x :=
  actionColimit_exists_rep ((sectionsFunctor R A).obj M) x

section Smooth

variable [TopologicalSpace G]

omit [HasColimitsOfShape J (ModuleCat.{u} R)] in
/-- Each level of ordinary cohomology is smooth for a levelwise smooth tower. -/
theorem isSmooth_levelCohomology (hA : IsLevelwiseSmooth A) (q : ℕ) (M : ModuleSheaf X R)
    (i : J) : IsSmooth ((Rep.ActionToRep R G).obj (((cohomologyFunctor R A q).obj M).obj i)).ρ := by
  obtain ⟨U, hU⟩ := hA i
  exact isSmooth_actionToRep_of_open_trivial _ U fun g hg =>
    cohomologyFunctor_obj_obj_ρ_eq_id R A q M i (hU g hg)

omit [HasColimitsOfShape J (ModuleCat.{u} R)] in
/-- Each level of global sections is smooth for a levelwise smooth tower. -/
theorem isSmooth_levelSections (hA : IsLevelwiseSmooth A) (M : ModuleSheaf X R) (i : J) :
    IsSmooth ((Rep.ActionToRep R G).obj (((sectionsFunctor R A).obj M).obj i)).ρ := by
  obtain ⟨U, hU⟩ := hA i
  exact isSmooth_actionToRep_of_open_trivial _ U fun g hg =>
    sectionsFunctor_obj_obj_ρ_eq_id R A M i (hU g hg)

/-- The colimit ordinary cohomology of a levelwise smooth tower is smooth. -/
theorem isSmooth_colimitCohomology (hA : IsLevelwiseSmooth A) (q : ℕ) (M : ModuleSheaf X R) :
    IsSmooth ((Rep.ActionToRep R G).obj ((colimitCohomologyFunctor R A q).obj M)).ρ :=
  isSmooth_actionToRep_colimit _ fun i => by
    obtain ⟨U, hU⟩ := hA i
    exact ⟨U, fun g hg => cohomologyFunctor_obj_obj_ρ_eq_id R A q M i (hU g hg)⟩

/-- The colimit global sections of a levelwise smooth tower are smooth. -/
theorem isSmooth_colimitSections (hA : IsLevelwiseSmooth A) (M : ModuleSheaf X R) :
    IsSmooth ((Rep.ActionToRep R G).obj ((colimitSectionsFunctor R A).obj M)).ρ :=
  isSmooth_actionToRep_colimit _ fun i => by
    obtain ⟨U, hU⟩ := hA i
    exact ⟨U, fun g hg => sectionsFunctor_obj_obj_ρ_eq_id R A M i (hU g hg)⟩

/-- Level ordinary cohomology as smooth representations. -/
def smoothLevelCohomologyFunctor (hA : IsLevelwiseSmooth A) (q : ℕ) (i : J) :
    ModuleSheaf X R ⥤ SmoothRep.{u, t, u} R G :=
  (smoothRepProperty R G).lift
    (cohomologyFunctor R A q ⋙ (evaluation J (Action (ModuleCat.{u} R) G)).obj i ⋙
      Rep.ActionToRep R G)
    (isSmooth_levelCohomology R A hA q · i)

/-- Level global sections as smooth representations. -/
def smoothLevelSectionsFunctor (hA : IsLevelwiseSmooth A) (i : J) :
    ModuleSheaf X R ⥤ SmoothRep.{u, t, u} R G :=
  (smoothRepProperty R G).lift
    (sectionsFunctor R A ⋙ (evaluation J (Action (ModuleCat.{u} R) G)).obj i ⋙
      Rep.ActionToRep R G)
    (isSmooth_levelSections R A hA · i)

/-- Colimit ordinary cohomology as smooth representations. -/
def smoothColimitCohomologyFunctor (hA : IsLevelwiseSmooth A) (q : ℕ) :
    ModuleSheaf X R ⥤ SmoothRep.{u, t, u} R G :=
  (smoothRepProperty R G).lift (colimitCohomologyFunctor R A q ⋙ Rep.ActionToRep R G)
    (isSmooth_colimitCohomology R A hA q)

/-- Colimit global sections as smooth representations. -/
def smoothColimitSectionsFunctor (hA : IsLevelwiseSmooth A) :
    ModuleSheaf X R ⥤ SmoothRep.{u, t, u} R G :=
  (smoothRepProperty R G).lift (colimitSectionsFunctor R A ⋙ Rep.ActionToRep R G)
    (isSmooth_colimitSections R A hA)

@[simp] theorem smoothColimitCohomologyFunctor_obj_obj (hA : IsLevelwiseSmooth A) (q : ℕ)
    (M : ModuleSheaf X R) :
    ((smoothColimitCohomologyFunctor R A hA q).obj M).obj =
      (Rep.ActionToRep R G).obj ((colimitCohomologyFunctor R A q).obj M) := rfl

@[simp] theorem smoothColimitSectionsFunctor_obj_obj (hA : IsLevelwiseSmooth A)
    (M : ModuleSheaf X R) :
    ((smoothColimitSectionsFunctor R A hA).obj M).obj =
      (Rep.ActionToRep R G).obj ((colimitSectionsFunctor R A).obj M) := rfl

/-- The level inclusion of ordinary cohomology as morphisms of smooth representations. -/
def smoothLevelCohomologyι (hA : IsLevelwiseSmooth A) (q : ℕ) (i : J) :
    smoothLevelCohomologyFunctor R A hA q i ⟶ smoothColimitCohomologyFunctor R A hA q where
  app M := ObjectProperty.homMk ((Rep.ActionToRep R G).map ((levelCohomologyι R A q i).app M))
  naturality M N α := by
    apply ObjectProperty.hom_ext
    change (Rep.ActionToRep R G).map (((cohomologyFunctor R A q).map α).app i) ≫
        (Rep.ActionToRep R G).map ((levelCohomologyι R A q i).app N) =
      (Rep.ActionToRep R G).map ((levelCohomologyι R A q i).app M) ≫
        (Rep.ActionToRep R G).map ((colimitCohomologyFunctor R A q).map α)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (Rep.ActionToRep R G).map ((levelCohomologyι R A q i).naturality α)

/-- The level inclusion of global sections as morphisms of smooth representations. -/
def smoothLevelSectionsι (hA : IsLevelwiseSmooth A) (i : J) :
    smoothLevelSectionsFunctor R A hA i ⟶ smoothColimitSectionsFunctor R A hA where
  app M := ObjectProperty.homMk ((Rep.ActionToRep R G).map ((levelSectionsι R A i).app M))
  naturality M N α := by
    apply ObjectProperty.hom_ext
    change (Rep.ActionToRep R G).map (((sectionsFunctor R A).map α).app i) ≫
        (Rep.ActionToRep R G).map ((levelSectionsι R A i).app N) =
      (Rep.ActionToRep R G).map ((levelSectionsι R A i).app M) ≫
        (Rep.ActionToRep R G).map ((colimitSectionsFunctor R A).map α)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (Rep.ActionToRep R G).map ((levelSectionsι R A i).naturality α)

@[simp] theorem smoothLevelCohomologyι_app_hom (hA : IsLevelwiseSmooth A) (q : ℕ) (i : J)
    (M : ModuleSheaf X R) :
    ((smoothLevelCohomologyι R A hA q i).app M).hom =
      (Rep.ActionToRep R G).map ((levelCohomologyι R A q i).app M) := rfl

@[simp] theorem smoothLevelSectionsι_app_hom (hA : IsLevelwiseSmooth A) (i : J)
    (M : ModuleSheaf X R) :
    ((smoothLevelSectionsι R A hA i).app M).hom =
      (Rep.ActionToRep R G).map ((levelSectionsι R A i).app M) := rfl

/-- Degree-zero recovery for the smooth colimit representations. -/
def smoothColimitCohomologyZeroIso (hA : IsLevelwiseSmooth A) :
    smoothColimitCohomologyFunctor R A hA 0 ≅ smoothColimitSectionsFunctor R A hA :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _
      ((Rep.ActionToRep R G).mapIso ((colimitCohomologyZeroIso R A).app M)))
    (by
      intro M N α
      apply ObjectProperty.hom_ext
      change (Rep.ActionToRep R G).map ((colimitCohomologyFunctor R A 0).map α) ≫
          (Rep.ActionToRep R G).map ((colimitCohomologyZeroIso R A).hom.app N) =
        (Rep.ActionToRep R G).map ((colimitCohomologyZeroIso R A).hom.app M) ≫
          (Rep.ActionToRep R G).map ((colimitSectionsFunctor R A).map α)
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (Rep.ActionToRep R G).map ((colimitCohomologyZeroIso R A).hom.naturality α))

@[simp] theorem smoothColimitCohomologyZeroIso_hom_app_hom (hA : IsLevelwiseSmooth A)
    (M : ModuleSheaf X R) :
    ((smoothColimitCohomologyZeroIso R A hA).hom.app M).hom =
      (Rep.ActionToRep R G).map ((colimitCohomologyZeroIso R A).hom.app M) := rfl

end Smooth

end Colimit

end Cohomology

end Langlands.Geometry.EtaleCanonicalDeckTower
