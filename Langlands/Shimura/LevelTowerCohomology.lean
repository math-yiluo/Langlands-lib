import Langlands.Shimura.LevelColimit
import Langlands.Geometry.EtaleCohomologyDiagramFunctor

/-! # Smooth representations on colimit cohomology of level towers of schemes -/

noncomputable section

universe u

namespace Langlands.Shimura.LevelTowerCohomology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtalePullback CompactOpenLevel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {G : Type u} [Group G] [TopologicalSpace G]
variable (T : CompactOpenLevel G ⥤ Scheme.{u}) [∀ {K L : CompactOpenLevel G} (a : K ⟶ L),
  Etale (T.map a)]
variable (R : Type u) [CommRing R]

instance etale_op_map {K L : (CompactOpenLevel G)ᵒᵖ} (a : K ⟶ L) :
    Etale (T.op.map a).unop :=
  inferInstanceAs (Etale (T.map a.unop))

variable {T R}

/-- Each `k ∈ K` acts on level `K` by the identity scheme morphism, and the coefficient
morphism of its self-arrow is the identity coefficient morphism transported along that
equality. -/
def IsLevelTrivialCoefficients (D : CoefficientDiagram R T.op) : Prop :=
  ∀ (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup),
    ∃ e : (T.op.map (selfArrow K k hk).op).unop = (T.op.map (𝟙 (op K))).unop,
      D.map (selfArrow K k hk).op =
        (restrictionCongr R e).hom.app (D.obj (op K)) ≫ D.map (𝟙 (op K))

variable (T R) in
/-- Level-trivial coefficient diagrams, as a property of objects. -/
def levelTrivialCoefficients : ObjectProperty (CoefficientDiagram R T.op) :=
  fun D => IsLevelTrivialCoefficients D

/-- Cohomology of level-trivial coefficients is a level-trivial presheaf on levels. -/
theorem isLevelTrivial_cohomology {D : CoefficientDiagram R T.op}
    (hD : IsLevelTrivialCoefficients D) (q : ℕ) :
    LevelColimit.IsLevelTrivial (D.cohomology q) := by
  intro K k hk
  obtain ⟨e, he⟩ := hD K k hk
  refine Eq.trans ?_ ((D.cohomology q).map_id (op K))
  change cohomologyMapWithCoefficients (T.op.map (selfArrow K k hk).op).unop R q
      (D.map (selfArrow K k hk).op) =
    cohomologyMapWithCoefficients (T.op.map (𝟙 (op K))).unop R q (D.map (𝟙 (op K)))
  dsimp only [cohomologyMapWithCoefficients]
  rw [he, CategoryTheory.Functor.map_comp, ← Category.assoc, cohomologyMap_congr]

/-- Global sections of level-trivial coefficients form a level-trivial presheaf on levels. -/
theorem isLevelTrivial_sections {D : CoefficientDiagram R T.op}
    (hD : IsLevelTrivialCoefficients D) :
    LevelColimit.IsLevelTrivial D.sections := by
  intro K k hk
  have h := isLevelTrivial_cohomology hD 0 K k hk
  change (EtaleDerivedSections.cohomologyZeroIso (T.op.obj (op K)).unop R).inv.app _ ≫
      (D.cohomology 0).map (selfArrow K k hk).op ≫
      (EtaleDerivedSections.cohomologyZeroIso (T.op.obj (op K)).unop R).hom.app _ = 𝟙 _
  rw [h]
  erw [Category.id_comp, Iso.inv_hom_id_app]

variable [IsTopologicalGroup G]

/-- The colimit over shrinking levels of degree `q` cohomology, with `g` acting through the
conjugate levels `g K g⁻¹`. -/
def colimitCohomology (D : CoefficientDiagram R T.op) (q : ℕ) : Action (ModuleCat.{u} R) G :=
  LevelColimit.action (D.cohomology q)

/-- The colimit over levels of the cohomology of level-trivial coefficients, as a smooth
representation of `G`. -/
def smoothColimitCohomology (D : CoefficientDiagram R T.op) (hD : IsLevelTrivialCoefficients D)
    (q : ℕ) : SmoothRep.{u, u, u} R G :=
  LevelColimit.smoothRep (G := G) (R := R) (D.cohomology q) (isLevelTrivial_cohomology hD q)

/-- The colimit over levels of global sections of level-trivial coefficients, as a smooth
representation of `G`. -/
def smoothColimitSections (D : CoefficientDiagram R T.op) (hD : IsLevelTrivialCoefficients D) :
    SmoothRep.{u, u, u} R G :=
  LevelColimit.smoothRep (G := G) (R := R) D.sections (isLevelTrivial_sections hD)

variable (T R) in
/-- Degree `q` colimit cohomology as a functor from level-trivial coefficient diagrams to smooth
representations. -/
def smoothColimitCohomologyFunctor (q : ℕ) :
    (levelTrivialCoefficients T R).FullSubcategory ⥤ SmoothRep.{u, u, u} R G :=
  (LevelColimit.levelTrivialProperty G (ModuleCat.{u} R)).lift
      ((levelTrivialCoefficients T R).ι ⋙ CoefficientDiagram.cohomologyFunctor q)
      (fun D => isLevelTrivial_cohomology D.property q) ⋙
    LevelColimit.smoothFunctor G R

/-- The action of `g` on the image of a class of level `K`: it is the image at level
`g K g⁻¹` of the pullback along the translation `T(g K g⁻¹ ⟶ K)` with the coefficient map of
that arrow. -/
theorem smoothColimitCohomology_ρ_ι_apply (D : CoefficientDiagram R T.op)
    (hD : IsLevelTrivialCoefficients D) (q : ℕ) (g : G) (K : CompactOpenLevel G)
    (x : (D.cohomology q).obj (op K)) :
    (smoothColimitCohomology D hD q).obj.ρ g ((LevelColimit.ι (D.cohomology q) K).hom x) =
      (LevelColimit.ι (D.cohomology q) (conjLevel g K)).hom
        ((cohomologyMapWithCoefficients (T.map (conjArrow g K)) R q
          (D.map (conjArrow g K).op)).hom x) :=
  LevelColimit.smoothRep_ρ_ι_apply (G := G) (R := R) (D.cohomology q)
    (isLevelTrivial_cohomology hD q) g K x

/-- Every class of the colimit comes from a single level, provided some level exists. -/
theorem exists_level_class [Nonempty (CompactOpenLevel G)] (D : CoefficientDiagram R T.op)
    (q : ℕ) (x : (colimitCohomology D q).V) :
    ∃ (K : CompactOpenLevel G) (y : (D.cohomology q).obj (op K)),
      (LevelColimit.ι (D.cohomology q) K).hom y = x :=
  LevelColimit.exists_ι_apply (G := G) (R := R) (D.cohomology q) x

end Langlands.Shimura.LevelTowerCohomology
