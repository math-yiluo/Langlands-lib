import Langlands.CategoryTheory.Renard.UnitCounitStatements

/-!
# Renard A.V.2: proofs of the unit–counit statements

Proofs of the seven closed unit–counit components and their aggregate. The
first four components read off Mathlib's adjunction data. The raw Hom maps are
natural by naturality of the supplied transformations alone; the triangles make
them mutually inverse and assemble the supplied transformations into an
adjunction.
-/

open CategoryTheory

namespace Langlands.Renard.UnitCounit

universe vA uA vB uB

/-- The unit and counit are the images of the identity arrows. -/
theorem unitCounitAtIdentitiesStatement :
    UnitCounitAtIdentitiesStatement.{vA, uA, vB, uB} := by
  intro A _ B _ G F adj
  exact ⟨fun Y => (adj.homEquiv_id Y).symm, fun X => (adj.homEquiv_symm_id X).symm⟩

/-- The components of the actual unit and counit are natural. -/
theorem unitCounitNaturalityStatement :
    UnitCounitNaturalityStatement.{vA, uA, vB, uB} := by
  intro A _ B _ G F adj
  exact ⟨fun _ _ f => adj.unit.naturality f, fun _ _ g => adj.counit.naturality g⟩

/-- The two triangle identities, right triangle first. -/
theorem triangleIdentitiesStatement :
    TriangleIdentitiesStatement.{vA, uA, vB, uB} := by
  intro A _ B _ G F adj
  exact ⟨adj.right_triangle_components, adj.left_triangle_components⟩

/-- The Hom equivalence and its inverse are given by the unit and counit formulas. -/
theorem homEquivFormulasStatement :
    HomEquivFormulasStatement.{vA, uA, vB, uB} := by
  intro A _ B _ G F adj
  exact ⟨fun Y X h => adj.homEquiv_unit Y X h, fun Y X k => adj.homEquiv_counit Y X k⟩

/-- Both raw Hom maps are natural in both variables, without triangle hypotheses. -/
theorem homMapNaturalityStatement :
    HomMapNaturalityStatement.{vA, uA, vB, uB} := by
  intro A _ B _ G F η ε
  constructor
  · intro Y Y' X X' f g h
    have hη : η.app Y' ≫ F.map (G.map f) = f ≫ η.app Y := (η.naturality f).symm
    simp only [Functor.map_comp, Category.assoc, reassoc_of% hη]
  · intro Y Y' X X' f g k
    have hε : G.map (F.map g) ≫ ε.app X' = ε.app X ≫ g := ε.naturality g
    simp only [Functor.map_comp, Category.assoc, hε]

/-- The two triangles make the raw Hom maps mutually inverse. -/
theorem homMapInverseIdentitiesStatement :
    HomMapInverseIdentitiesStatement.{vA, uA, vB, uB} := by
  intro A _ B _ G F η ε hright hleft
  constructor
  · intro Y X h
    have hε : G.map (F.map h) ≫ ε.app X = ε.app (G.obj Y) ≫ h := ε.naturality h
    rw [G.map_comp, Category.assoc, hε, ← Category.assoc, hleft Y]
    exact Category.id_comp h
  · intro Y X k
    have hη : η.app Y ≫ F.map (G.map k) = k ≫ η.app (F.obj X) := (η.naturality k).symm
    rw [F.map_comp, ← Category.assoc, hη, Category.assoc, hright X]
    exact Category.comp_id k

/-- The supplied unit and counit, with both triangles, form an adjunction. -/
theorem adjunctionFromUnitCounitStatement :
    AdjunctionFromUnitCounitStatement.{vA, uA, vB, uB} := by
  intro A _ B _ G F η ε hright hleft
  let adj : G ⊣ F :=
    { unit := η
      counit := ε
      left_triangle_components := hleft
      right_triangle_components := hright }
  exact ⟨adj, rfl, rfl⟩

/-- Renard A.V.2: the seven native unit–counit components, in source order. -/
theorem unitCounitStatements : UnitCounitStatements.{vA, uA, vB, uB} :=
  ⟨unitCounitAtIdentitiesStatement, unitCounitNaturalityStatement,
    triangleIdentitiesStatement, homEquivFormulasStatement, homMapNaturalityStatement,
    homMapInverseIdentitiesStatement, adjunctionFromUnitCounitStatement⟩

end Langlands.Renard.UnitCounit
