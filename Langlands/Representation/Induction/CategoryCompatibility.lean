import Langlands.Representation.Induction.Definitions

/-!
# Definitional compatibility of the induction category

These examples check transparent reuse of the canonical smooth category and the
complete types and morphism formulas of the existing induction interfaces.
They introduce no new instances or mathematical assumptions.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Induction

universe uR uG uV uW

-- Equality of the unapplied constants checks the entire instance telescope.
example : @SmoothRep.{uR, uG, uV} = @Langlands.SmoothRep.{uR, uG, uV} := rfl

section Category

variable (R : Type uR) (G : Type uG) [CommRing R] [Group G] [TopologicalSpace G]

-- This is the exact full-subcategory expression used before the consolidation.
example : SmoothRep.{uR, uG, uV} R G =
    ObjectProperty.FullSubcategory (fun A : Rep.{uV} R G => IsSmooth A.ρ) := rfl

example :
    (inferInstance : Category (SmoothRep.{uR, uG, uV} R G)) =
    (inferInstance : Category (Langlands.SmoothRep.{uR, uG, uV} R G)) := rfl

example :
    (inferInstance : Preadditive (SmoothRep.{uR, uG, uV} R G)) =
    (inferInstance : Preadditive (Langlands.SmoothRep.{uR, uG, uV} R G)) := rfl

example :
    (inferInstance : Linear R (SmoothRep.{uR, uG, uV} R G)) =
    (inferInstance : Linear R (Langlands.SmoothRep.{uR, uG, uV} R G)) := rfl

end Category

-- The functors retain arbitrary coefficients and the independently sized input
-- carrier. Only the induction constructions require a topological group.
example :
    ∀ {R : Type uR} {G : Type uG} [CommRing R] [Group G]
      [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G),
      Rep.{uV} R P ⥤ Langlands.SmoothRep.{uR, uG, max uG uV} R G :=
  @smoothInductionFunctor.{uR, uG, uV}

example :
    ∀ {R : Type uR} {G : Type uG} [CommRing R] [Group G]
      [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G),
      Rep.{uV} R P ⥤ Langlands.SmoothRep.{uR, uG, max uG uV} R G :=
  @compactInductionFunctor.{uR, uG, uV}

example :
    ∀ {R : Type uR} {G : Type uG} [CommRing R] [Group G]
      [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G)
      (_χ : SmoothCharacter R P),
      Rep.{uV} R P ⥤ Langlands.SmoothRep.{uR, uG, max uG uV} R G :=
  @normalizedSmoothInductionFunctor.{uR, uG, uV}

example :
    ∀ {R : Type uR} {G : Type uG} [CommRing R] [Group G]
      [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G)
      (_χ : SmoothCharacter R P),
      Rep.{uV} R P ⥤ Langlands.SmoothRep.{uR, uG, max uG uV} R G :=
  @normalizedCompactInductionFunctor.{uR, uG, uV}

-- The map constructors also retain independently sized source and target modules.
example :
    ∀ {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
      [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
      (P : Subgroup G) {σ : Representation R P V} {τ : Representation R P W},
      σ.IntertwiningMap τ →
        (smoothInduced P σ).IntertwiningMap (smoothInduced P τ) :=
  @smoothInducedMap.{uR, uG, uV, uW}

example :
    ∀ {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
      [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
      (P : Subgroup G) {σ : Representation R P V} {τ : Representation R P W},
      σ.IntertwiningMap τ →
        (compactInduced P σ).IntertwiningMap (compactInduced P τ) :=
  @compactInducedMap.{uR, uG, uV, uW}

section Maps

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G)
  {A B : Rep.{uV} R P} (f : A ⟶ B)

example : Langlands.SmoothRep.hom ((smoothInductionFunctor P).map f) =
    smoothInducedMap P f.hom := rfl

example : Langlands.SmoothRep.hom ((compactInductionFunctor P).map f) =
    compactInducedMap P f.hom := rfl

example (χ : SmoothCharacter R P) :
    Langlands.SmoothRep.hom ((normalizedSmoothInductionFunctor P χ).map f) =
      smoothInducedMap P (twistIntertwining χ.toMonoidHom f.hom) := rfl

example (χ : SmoothCharacter R P) :
    Langlands.SmoothRep.hom ((normalizedCompactInductionFunctor P χ).map f) =
      compactInducedMap P (twistIntertwining χ.toMonoidHom f.hom) := rfl

end Maps

end Langlands.Induction
