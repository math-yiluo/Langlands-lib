import Langlands.Shimura.RestrictedLevelTowerCohomology

/-! # Towers over levels satisfying a property that holds at every level

If a property `P` of levels holds at every level, a tower of schemes over the levels satisfying
`P` is a tower over all levels, its coefficients are coefficients over all levels, and its
colimit cohomology over the levels satisfying `P` is the colimit cohomology over all levels. See
`RestrictedLevelTowerExtension.md`.
-/

noncomputable section

universe u

namespace Langlands.Shimura.RestrictedLevelTowerCohomology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtalePullback CompactOpenLevel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {G : Type u} [Group G] [TopologicalSpace G] {P : ObjectProperty (CompactOpenLevel G)}
variable (hP : ∀ K : CompactOpenLevel G, P K)

/-! ## Levels -/

/-- Every level, as a level satisfying `P`, when `P` holds at every level. -/
abbrev extendLevels : CompactOpenLevel G ⥤ P.FullSubcategory :=
  P.lift (𝟭 _) hP

include hP in
/-- A property holding at every level is downward closed. -/
theorem isDownwardClosed_of_forall : IsDownwardClosed P :=
  ⟨fun _ _ => hP _⟩

include hP in
/-- A property holding at every level is stable under conjugation. -/
theorem isConjStable_of_forall [IsTopologicalGroup G] : IsConjStable P :=
  ⟨fun _ _ _ => hP _⟩

/-! ## Towers and coefficients -/

section Tower

variable (T : P.FullSubcategory ⥤ Scheme.{u})

/-- A tower over the levels satisfying `P`, as a tower over all levels. -/
abbrev extendTower : CompactOpenLevel G ⥤ Scheme.{u} :=
  extendLevels hP ⋙ T

/-- Restricting the tower over all levels to the levels satisfying `P` gives back `T`. -/
theorem restrict_extendTower : P.ι ⋙ extendTower hP T = T :=
  rfl

variable [∀ {K L : P.FullSubcategory} (a : K ⟶ L), Etale (T.map a)]

instance etale_extendTower_map {K L : CompactOpenLevel G} (a : K ⟶ L) :
    Etale ((extendTower hP T).map a) :=
  inferInstanceAs (Etale (T.map ((extendLevels hP).map a)))

variable {T} {R : Type u} [CommRing R]

/-- Coefficients on `T`, as coefficients on the tower over all levels. -/
def extendCoefficients (D : CoefficientDiagram R T.op) :
    CoefficientDiagram R (extendTower hP T).op :=
  CoefficientDiagram.reindex (extendLevels hP).op D

@[simp] theorem extendCoefficients_obj (D : CoefficientDiagram R T.op)
    (K : (CompactOpenLevel G)ᵒᵖ) :
    (extendCoefficients hP D).obj K = D.obj (op ⟨K.unop, hP K.unop⟩) :=
  rfl

theorem extendCoefficients_cohomology (D : CoefficientDiagram R T.op) (q : ℕ) :
    (extendCoefficients hP D).cohomology q = (extendLevels hP).op ⋙ D.cohomology q :=
  rfl

/-- Restricting the extended coefficients to the levels satisfying `P` gives back `D`. -/
theorem restrictCoefficients_extendCoefficients (D : CoefficientDiagram R T.op) :
    restrictCoefficients (P := P) (extendCoefficients hP D) = D :=
  rfl

/-- The extension of level-trivial coefficients is level-trivial. -/
theorem isLevelTrivialCoefficients_extend {D : CoefficientDiagram R T.op}
    (hD : IsLevelTrivialCoefficients D) :
    LevelTowerCohomology.IsLevelTrivialCoefficients (extendCoefficients hP D) :=
  fun K k hk => hD ⟨K, hP K⟩ k hk

end Tower

/-! ## Colimit cohomology -/

section Colimit

variable [IsTopologicalGroup G] [IsConjStable P] [Nonempty (CompactOpenLevel G)]
variable {T : P.FullSubcategory ⥤ Scheme.{u}} [∀ {K L : P.FullSubcategory} (a : K ⟶ L),
  Etale (T.map a)]
variable {R : Type u} [CommRing R]

/-- The colimit cohomology over the levels satisfying `P` is the colimit cohomology over all
levels of the extended coefficients, as objects with an action of `G`. -/
def colimitCohomologyExtendIso (D : CoefficientDiagram R T.op) (q : ℕ) :
    colimitCohomology D q ≅ LevelTowerCohomology.colimitCohomology (extendCoefficients hP D) q :=
  haveI := isDownwardClosed_of_forall hP
  haveI : Nonempty P.FullSubcategory := ⟨(extendLevels hP).obj (Classical.arbitrary _)⟩
  colimitCohomologyRestrictIso (P := P) (extendCoefficients hP D) q

/-- On a class of level `K`, the isomorphism is the inclusion of level `K` into the colimit over
all levels. -/
@[reassoc]
theorem ι_colimitCohomologyExtendIso_hom (D : CoefficientDiagram R T.op) (q : ℕ)
    (K : P.FullSubcategory) :
    RestrictedLevelColimit.ι (D.cohomology q) K ≫ (colimitCohomologyExtendIso hP D q).hom.hom =
      LevelColimit.ι ((extendCoefficients hP D).cohomology q) K.obj :=
  haveI := isDownwardClosed_of_forall hP
  haveI : Nonempty P.FullSubcategory := ⟨(extendLevels hP).obj (Classical.arbitrary _)⟩
  ι_colimitCohomologyRestrictIso_hom (P := P) (extendCoefficients hP D) q K

/-- The isomorphism of smooth colimit cohomology for level-trivial coefficients. -/
def smoothColimitCohomologyExtendIso (D : CoefficientDiagram R T.op)
    (hD : IsLevelTrivialCoefficients D) (q : ℕ) :
    smoothColimitCohomology D hD q ≅
      LevelTowerCohomology.smoothColimitCohomology (extendCoefficients hP D)
        (isLevelTrivialCoefficients_extend hP hD) q :=
  haveI := isDownwardClosed_of_forall hP
  haveI : Nonempty P.FullSubcategory := ⟨(extendLevels hP).obj (Classical.arbitrary _)⟩
  smoothColimitCohomologyRestrictIso (P := P) (extendCoefficients hP D)
    (isLevelTrivialCoefficients_extend hP hD) q

/-- The isomorphism of smooth colimits of global sections for level-trivial coefficients. -/
def smoothColimitSectionsExtendIso (D : CoefficientDiagram R T.op)
    (hD : IsLevelTrivialCoefficients D) :
    smoothColimitSections D hD ≅
      LevelTowerCohomology.smoothColimitSections (extendCoefficients hP D)
        (isLevelTrivialCoefficients_extend hP hD) :=
  haveI := isDownwardClosed_of_forall hP
  haveI : Nonempty P.FullSubcategory := ⟨(extendLevels hP).obj (Classical.arbitrary _)⟩
  smoothColimitSectionsRestrictIso (P := P) (extendCoefficients hP D)
    (isLevelTrivialCoefficients_extend hP hD)

end Colimit

end Langlands.Shimura.RestrictedLevelTowerCohomology
