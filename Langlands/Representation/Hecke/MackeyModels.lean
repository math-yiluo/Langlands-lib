import Langlands.Representation.Hecke.HomomorphismSmooth
import Langlands.Representation.Smooth.RenardTensorHomExactnessProof
import Langlands.Representation.Category.SmoothPartAdjunction
import Mathlib.CategoryTheory.Products.Basic

/-! # Actual tensor and smooth Hom bifunctors for the Mackey isomorphisms

Renard III.1.15 and III.2.11, printed pp.67–70 and 82–83 / PDF pp.73–76 and 88–89.
-/

noncomputable section

open CategoryTheory MeasureTheory

namespace Langlands.Hecke.Homomorphism

universe uG uH v

section Algebraic

variable (G : Type uG) [Group G]

/-- The diagonal tensor bifunctor on the existing algebraic representations. -/
def algebraicTensorBifunctor : Rep.{v} ℂ G × Rep.{v} ℂ G ⥤ Rep.{v} ℂ G where
  obj X := Rep.of (X.1.ρ.tprod X.2.ρ)
  map f := Rep.ofHom (f.1.hom.tensor f.2.hom)
  map_id X := by ext x y; rfl
  map_comp f g := by ext x y; rfl

/-- The actual conjugation Hom bifunctor, contravariant in its first argument. -/
def algebraicHomBifunctor : (Rep.{v} ℂ G)ᵒᵖ × Rep.{v} ℂ G ⥤ Rep.{v} ℂ G where
  obj X := Rep.of (Representation.linHom X.1.unop.ρ X.2.ρ)
  map {X Y} f := Rep.ofHom
    ((Renard.Smooth.TensorHom.postcompose Y.1.unop.ρ X.2.ρ Y.2.ρ f.2.hom).comp
      (Renard.Smooth.TensorHom.precompose Y.1.unop.ρ X.1.unop.ρ X.2.ρ f.1.unop.hom))
  map_id X := by ext L x; rfl
  map_comp f g := by ext L x; rfl

end Algebraic

section Smooth

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The actual tensor product of two smooth representations, with diagonal action. -/
def smoothTensorBifunctor :
    SmoothRep.{0, uG, v} ℂ G × SmoothRep.{0, uG, v} ℂ G ⥤ SmoothRep.{0, uG, v} ℂ G :=
  ObjectProperty.lift _
    ((SmoothRep.toRep.prod SmoothRep.toRep) ⋙ algebraicTensorBifunctor G)
    (fun X => Renard.Smooth.TensorHom.tensor_smooth X.1.representation X.2.representation
      X.1.isSmooth X.2.isSmooth)

/-- The existing smooth part of the conjugation Hom representation. -/
abbrev smoothHomBifunctor :
    (SmoothRep.{0, uG, v} ℂ G)ᵒᵖ × SmoothRep.{0, uG, v} ℂ G ⥤ SmoothRep.{0, uG, v} ℂ G :=
  (SmoothRep.toRep.op.prod SmoothRep.toRep) ⋙ algebraicHomBifunctor G ⋙
    SmoothRep.smoothPartFunctor ℂ G

end Smooth

section Mackey

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] [T2Space H]
  [NonarchimedeanGroup H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  (μG : Measure G) [μG.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]
  (φ : H →* G) (hφ : Continuous φ)
  (eG : (heckeNondegenerateModuleFunctor.{uG, max uG v} μG).IsEquivalence)

/-- `(V,W) ↦ Hom(V,I(W))₀`, on the product category with `V` contravariant. -/
abbrev mackeyHomLeft :
    (SmoothRep.{0, uG, max uG v} ℂ G)ᵒᵖ × SmoothRep.{0, uH, max uG v} ℂ H ⥤
      SmoothRep.{0, uG, max uG v} ℂ G :=
  ((𝟭 (SmoothRep.{0, uG, max uG v} ℂ G)ᵒᵖ).prod (smoothI μG μH φ hφ eG)) ⋙
    smoothHomBifunctor G

/-- `(V,W) ↦ I(Hom(Fφ(V),W)₀)`, with the actual continuous pullback. -/
abbrev mackeyHomRight :
    (SmoothRep.{0, uG, max uG v} ℂ G)ᵒᵖ × SmoothRep.{0, uH, max uG v} ℂ H ⥤
      SmoothRep.{0, uG, max uG v} ℂ G :=
  ((restriction.{uG, uH, max uG v} φ hφ).op.prod
    (𝟭 (SmoothRep.{0, uH, max uG v} ℂ H))) ⋙
    smoothHomBifunctor H ⋙ smoothI μG μH φ hφ eG

/-- `(W,V) ↦ P(W) ⊗ V`, with the actual tensor-induced representation. -/
abbrev mackeyTensorLeft :
    SmoothRep.{0, uH, max uG v} ℂ H × SmoothRep.{0, uG, max uG v} ℂ G ⥤
      SmoothRep.{0, uG, max uG v} ℂ G :=
  ((smoothP μG μH φ hφ eG).prod (𝟭 (SmoothRep.{0, uG, max uG v} ℂ G))) ⋙
    smoothTensorBifunctor G

/-- `(W,V) ↦ P(W ⊗ Fφ(V))`, using the original tensor and pullback. -/
abbrev mackeyTensorRight :
    SmoothRep.{0, uH, max uG v} ℂ H × SmoothRep.{0, uG, max uG v} ℂ G ⥤
      SmoothRep.{0, uG, max uG v} ℂ G :=
  ((𝟭 (SmoothRep.{0, uH, max uG v} ℂ H)).prod
    (restriction.{uG, uH, max uG v} φ hφ)) ⋙
    smoothTensorBifunctor H ⋙ smoothP μG μH φ hφ eG

end Mackey

end Langlands.Hecke.Homomorphism
