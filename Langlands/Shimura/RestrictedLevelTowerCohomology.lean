import Langlands.Shimura.RestrictedLevelColimit
import Langlands.Shimura.LevelTowerCohomology
import Langlands.Geometry.EtaleCohomologyReindex

/-! # Smooth representations on colimit cohomology of towers over levels satisfying a property -/

noncomputable section

universe u

namespace Langlands.Shimura.RestrictedLevelTowerCohomology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtalePullback CompactOpenLevel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {G : Type u} [Group G] [TopologicalSpace G] {P : ObjectProperty (CompactOpenLevel G)}
variable (T : P.FullSubcategory ⥤ Scheme.{u}) [∀ {K L : P.FullSubcategory} (a : K ⟶ L),
  Etale (T.map a)]
variable (R : Type u) [CommRing R]

instance etale_op_map {K L : P.FullSubcategoryᵒᵖ} (a : K ⟶ L) :
    Etale (T.op.map a).unop :=
  inferInstanceAs (Etale (T.map a.unop))

variable {T R}

/-- Each `k ∈ K` acts on level `K` by the identity scheme morphism, and the coefficient
morphism of its self-arrow is the identity coefficient morphism transported along that
equality. -/
def IsLevelTrivialCoefficients (D : CoefficientDiagram R T.op) : Prop :=
  ∀ (K : P.FullSubcategory) (k : G) (hk : k ∈ K.obj.subgroup),
    ∃ e : (T.op.map (restrictedSelfArrow P K k hk).op).unop = (T.op.map (𝟙 (op K))).unop,
      D.map (restrictedSelfArrow P K k hk).op =
        (restrictionCongr R e).hom.app (D.obj (op K)) ≫ D.map (𝟙 (op K))

variable (T R) in
/-- Level-trivial coefficient diagrams, as a property of objects. -/
def levelTrivialCoefficients : ObjectProperty (CoefficientDiagram R T.op) :=
  fun D => IsLevelTrivialCoefficients D

/-- Cohomology of level-trivial coefficients is a level-trivial presheaf on levels satisfying
`P`. -/
theorem isLevelTrivial_cohomology {D : CoefficientDiagram R T.op}
    (hD : IsLevelTrivialCoefficients D) (q : ℕ) :
    RestrictedLevelColimit.IsLevelTrivial (D.cohomology q) := by
  intro K k hk
  obtain ⟨e, he⟩ := hD K k hk
  refine Eq.trans ?_ ((D.cohomology q).map_id (op K))
  change cohomologyMapWithCoefficients (T.op.map (restrictedSelfArrow P K k hk).op).unop R q
      (D.map (restrictedSelfArrow P K k hk).op) =
    cohomologyMapWithCoefficients (T.op.map (𝟙 (op K))).unop R q (D.map (𝟙 (op K)))
  dsimp only [cohomologyMapWithCoefficients]
  rw [he, CategoryTheory.Functor.map_comp, ← Category.assoc, cohomologyMap_congr]

/-- Global sections of level-trivial coefficients form a level-trivial presheaf on levels
satisfying `P`. -/
theorem isLevelTrivial_sections {D : CoefficientDiagram R T.op}
    (hD : IsLevelTrivialCoefficients D) :
    RestrictedLevelColimit.IsLevelTrivial D.sections := by
  intro K k hk
  have h := isLevelTrivial_cohomology hD 0 K k hk
  change (EtaleDerivedSections.cohomologyZeroIso (T.op.obj (op K)).unop R).inv.app _ ≫
      (D.cohomology 0).map (restrictedSelfArrow P K k hk).op ≫
      (EtaleDerivedSections.cohomologyZeroIso (T.op.obj (op K)).unop R).hom.app _ = 𝟙 _
  rw [h]
  erw [Category.id_comp, Iso.inv_hom_id_app]

/-! ## Comparison with towers over all levels -/

section Restriction

variable (T₀ : CompactOpenLevel G ⥤ Scheme.{u}) [∀ {K L : CompactOpenLevel G} (a : K ⟶ L),
  Etale (T₀.map a)]

instance etale_restrict_map {K L : P.FullSubcategory} (a : K ⟶ L) :
    Etale ((P.ι ⋙ T₀).map a) :=
  inferInstanceAs (Etale (T₀.map a.hom))

variable {T₀}

/-- Coefficients on a tower over all levels, restricted to the levels satisfying `P`. -/
def restrictCoefficients (D₀ : CoefficientDiagram R T₀.op) :
    CoefficientDiagram R (P.ι ⋙ T₀).op :=
  CoefficientDiagram.reindex P.ι.op D₀

@[simp] theorem restrictCoefficients_obj (D₀ : CoefficientDiagram R T₀.op)
    (K : P.FullSubcategoryᵒᵖ) :
    (restrictCoefficients D₀).obj K = D₀.obj (op K.unop.obj) := rfl

theorem restrictCoefficients_cohomology (D₀ : CoefficientDiagram R T₀.op) (q : ℕ) :
    (restrictCoefficients (P := P) D₀).cohomology q = P.ι.op ⋙ D₀.cohomology q := rfl

theorem restrictCoefficients_sections (D₀ : CoefficientDiagram R T₀.op) :
    (restrictCoefficients (P := P) D₀).sections = P.ι.op ⋙ D₀.sections := rfl

/-- Restricting level-trivial coefficients gives level-trivial coefficients. -/
theorem isLevelTrivialCoefficients_restrict {D₀ : CoefficientDiagram R T₀.op}
    (hD₀ : LevelTowerCohomology.IsLevelTrivialCoefficients D₀) :
    IsLevelTrivialCoefficients (restrictCoefficients (P := P) D₀) :=
  fun K k hk => hD₀ K.obj k hk

variable (P R T₀) in
/-- Restriction of coefficients to levels satisfying `P`, as a functor of level-trivial
coefficient diagrams. -/
def restrictCoefficientsFunctor :
    (LevelTowerCohomology.levelTrivialCoefficients T₀ R).FullSubcategory ⥤
      (levelTrivialCoefficients (P.ι ⋙ T₀) R).FullSubcategory :=
  (levelTrivialCoefficients (P.ι ⋙ T₀) R).lift
    ((LevelTowerCohomology.levelTrivialCoefficients T₀ R).ι ⋙
      CoefficientDiagram.reindexFunctor P.ι.op)
    (fun D₀ => isLevelTrivialCoefficients_restrict D₀.property)

end Restriction

section Colimit

variable [IsTopologicalGroup G] [IsConjStable P]

/-- The colimit over shrinking levels satisfying `P` of degree `q` cohomology, with `g`
acting through the conjugate levels `g K g⁻¹`. -/
def colimitCohomology (D : CoefficientDiagram R T.op) (q : ℕ) : Action (ModuleCat.{u} R) G :=
  RestrictedLevelColimit.action (D.cohomology q)

/-- The colimit over levels satisfying `P` of the cohomology of level-trivial coefficients, as
a smooth representation of `G`. -/
def smoothColimitCohomology (D : CoefficientDiagram R T.op) (hD : IsLevelTrivialCoefficients D)
    (q : ℕ) : SmoothRep.{u, u, u} R G :=
  RestrictedLevelColimit.smoothRep (D.cohomology q) (isLevelTrivial_cohomology hD q)

/-- The colimit over levels satisfying `P` of global sections of level-trivial coefficients,
as a smooth representation of `G`. -/
def smoothColimitSections (D : CoefficientDiagram R T.op) (hD : IsLevelTrivialCoefficients D) :
    SmoothRep.{u, u, u} R G :=
  RestrictedLevelColimit.smoothRep D.sections (isLevelTrivial_sections hD)

variable (T R) in
/-- Degree `q` colimit cohomology over levels satisfying `P`, as a functor from level-trivial
coefficient diagrams to smooth representations. -/
def smoothColimitCohomologyFunctor (q : ℕ) :
    (levelTrivialCoefficients T R).FullSubcategory ⥤ SmoothRep.{u, u, u} R G :=
  (RestrictedLevelColimit.levelTrivialProperty P (ModuleCat.{u} R)).lift
      ((levelTrivialCoefficients T R).ι ⋙ CoefficientDiagram.cohomologyFunctor q)
      (fun D => isLevelTrivial_cohomology D.property q) ⋙
    RestrictedLevelColimit.smoothFunctor P R

/-- The action of `g` on the image of a class of level `K`: it is the image at level
`g K g⁻¹` of the pullback along the translation `T(g K g⁻¹ ⟶ K)` with the coefficient map of
that arrow. -/
theorem smoothColimitCohomology_ρ_ι_apply (D : CoefficientDiagram R T.op)
    (hD : IsLevelTrivialCoefficients D) (q : ℕ) (g : G) (K : P.FullSubcategory)
    (x : (D.cohomology q).obj (op K)) :
    (smoothColimitCohomology D hD q).obj.ρ g
        ((RestrictedLevelColimit.ι (D.cohomology q) K).hom x) =
      (RestrictedLevelColimit.ι (D.cohomology q) (restrictedConj P g K)).hom
        ((cohomologyMapWithCoefficients (T.map (restrictedConjArrow P g K)) R q
          (D.map (restrictedConjArrow P g K).op)).hom x) :=
  RestrictedLevelColimit.smoothRep_ρ_ι_apply (D.cohomology q)
    (isLevelTrivial_cohomology hD q) g K x

omit [IsConjStable P] in
/-- If `P` is downward closed and holds for some level, every class of the colimit comes from
a single level satisfying `P`. -/
theorem exists_level_class [IsDownwardClosed P] [Nonempty P.FullSubcategory]
    (D : CoefficientDiagram R T.op) (q : ℕ)
    (x : (colimit (RestrictedLevelColimit.diagram (D.cohomology q)) : ModuleCat.{u} R)) :
    ∃ (K : P.FullSubcategory) (y : (D.cohomology q).obj (op K)),
      (RestrictedLevelColimit.ι (D.cohomology q) K).hom y = x :=
  RestrictedLevelColimit.exists_ι_apply (D.cohomology q) x

end Colimit

/-! ## Comparison with towers over all levels -/

section Comparison

variable [IsTopologicalGroup G] [IsConjStable P] [IsDownwardClosed P] [Nonempty P.FullSubcategory]
variable {T₀ : CompactOpenLevel G ⥤ Scheme.{u}} [∀ {K L : CompactOpenLevel G} (a : K ⟶ L),
  Etale (T₀.map a)]

/-- For `P` conjugation stable, downward closed and holding for some level, the colimit
cohomology over levels satisfying `P` of restricted coefficients is the colimit cohomology over
all levels, as objects with an action of `G`. -/
def colimitCohomologyRestrictIso (D₀ : CoefficientDiagram R T₀.op) (q : ℕ) :
    colimitCohomology (restrictCoefficients (P := P) D₀) q ≅
      LevelTowerCohomology.colimitCohomology D₀ q :=
  RestrictedLevelColimit.actionRestrictIso (D₀.cohomology q)

theorem ι_colimitCohomologyRestrictIso_hom (D₀ : CoefficientDiagram R T₀.op) (q : ℕ)
    (K : P.FullSubcategory) :
    RestrictedLevelColimit.ι ((restrictCoefficients (P := P) D₀).cohomology q) K ≫
        (colimitCohomologyRestrictIso D₀ q).hom.hom =
      LevelColimit.ι (D₀.cohomology q) K.obj :=
  RestrictedLevelColimit.ι_colimitRestrictIso_hom (D₀.cohomology q) K

/-- The comparison of smooth colimit cohomology for restricted level-trivial coefficients. -/
def smoothColimitCohomologyRestrictIso (D₀ : CoefficientDiagram R T₀.op)
    (hD₀ : LevelTowerCohomology.IsLevelTrivialCoefficients D₀) (q : ℕ) :
    smoothColimitCohomology (restrictCoefficients (P := P) D₀)
        (isLevelTrivialCoefficients_restrict hD₀) q ≅
      LevelTowerCohomology.smoothColimitCohomology D₀ hD₀ q :=
  RestrictedLevelColimit.smoothRepRestrictIso (D₀.cohomology q)
    (LevelTowerCohomology.isLevelTrivial_cohomology hD₀ q)

/-- The comparison of smooth colimits of global sections for restricted level-trivial
coefficients. -/
def smoothColimitSectionsRestrictIso (D₀ : CoefficientDiagram R T₀.op)
    (hD₀ : LevelTowerCohomology.IsLevelTrivialCoefficients D₀) :
    smoothColimitSections (restrictCoefficients (P := P) D₀)
        (isLevelTrivialCoefficients_restrict hD₀) ≅
      LevelTowerCohomology.smoothColimitSections D₀ hD₀ :=
  RestrictedLevelColimit.smoothRepRestrictIso D₀.sections
    (LevelTowerCohomology.isLevelTrivial_sections hD₀)

variable (P R T₀) in
/-- The comparison of smooth colimit cohomology, natural in the level-trivial coefficient
diagram on the tower over all levels. -/
def smoothColimitCohomologyFunctorRestrictIso (q : ℕ) :
    restrictCoefficientsFunctor P R T₀ ⋙ smoothColimitCohomologyFunctor (P.ι ⋙ T₀) R q ≅
      LevelTowerCohomology.smoothColimitCohomologyFunctor T₀ R q :=
  NatIso.ofComponents
    (fun D₀ => smoothColimitCohomologyRestrictIso D₀.obj D₀.property q)
    (fun {D₀ E₀} α => by
      apply ObjectProperty.hom_ext
      change (Rep.ActionToRep R G).map _ ≫ (Rep.ActionToRep R G).map _ =
        (Rep.ActionToRep R G).map _ ≫ (Rep.ActionToRep R G).map _
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      congr 1
      exact Action.Hom.ext
        (RestrictedLevelColimit.map_colimitRestrictIso_hom
          (CoefficientDiagram.cohomologyMap α.hom q)))

end Comparison

end Langlands.Shimura.RestrictedLevelTowerCohomology
