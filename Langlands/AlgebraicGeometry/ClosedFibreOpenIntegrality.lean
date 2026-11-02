import Langlands.AlgebraicGeometry.ProperLocalClosedFibreCover
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Geometric integrality of opens meeting the closed fibre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry

/-- A surjective open restriction of a geometrically integral morphism has
geometrically integral fibres. Surjectivity retains nonempty fibres. -/
theorem geometricallyIntegral_open_of_surjective
    {X S : Scheme.{u}} (p : X ⟶ S) [GeometricallyIntegral p]
    (U : X.Opens) [Surjective (U.ι ≫ p)] :
    GeometricallyIntegral (U.ι ≫ p) := by
  refine ⟨?_⟩
  intro K _ y Z fst snd h
  let T := pullback (U.ι ≫ p) y
  let e := pullbackRightPullbackFstIso p y U.ι
  have hT : Nonempty T := by
    obtain ⟨z, _⟩ := (pullback.snd (U.ι ≫ p) y).surjective
      (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of K))))
    exact ⟨z⟩
  let : Nonempty ↥(pullback U.ι (pullback.fst p y)) :=
    hT.map (fun z => e.inv z)
  let : IsIntegral (pullback p y) :=
    pullback_of_geometrically
      (GeometricallyIntegral.geometrically_isIntegral (f := p)) K y
  let : IsIntegral (pullback U.ι (pullback.fst p y)) :=
    isIntegral_of_isOpenImmersion (pullback.snd U.ι (pullback.fst p y))
  let : IsIntegral T := isIntegral_of_isOpenImmersion e.inv
  let : Nonempty Z := hT.map (fun z => h.isoPullback.inv z)
  exact isIntegral_of_isOpenImmersion h.isoPullback.hom

/-- A smooth geometrically connected morphism has geometrically integral
fibres over every base point. -/
theorem geometricallyIntegral_of_smooth_geometricallyConnected
    {X S : Scheme.{u}} (p : X ⟶ S) [Smooth p] [GeometricallyConnected p] :
    GeometricallyIntegral p := by
  rw [GeometricallyIntegral.iff_geometricallyIntegral_fiber]
  intro s
  have hs : Smooth (p.fiberToSpecResidueField s) :=
    MorphismProperty.pullback_snd _ _ (inferInstance : Smooth p)
  have hc : GeometricallyConnected (p.fiberToSpecResidueField s) :=
    MorphismProperty.pullback_snd _ _ (inferInstance : GeometricallyConnected p)
  exact Langlands.AbelianScheme.smoothGeometricIntegrality _ _ _
    hs hc

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))

/-- An open of an open morphism to a local spectrum maps onto the base as
soon as it meets the closed fibre. -/
theorem surjective_open_of_meets_closedFibre [UniversallyOpen p]
    (U : X.Opens)
    (hU : (p ⁻¹' {IsLocalRing.closedPoint R} ∩ (U : Set X)).Nonempty) :
    Surjective (U.ι ≫ p) := by
  obtain ⟨x, hpx, hx⟩ := hU
  have hm : IsLocalRing.closedPoint R ∈ p '' (U : Set X) :=
    ⟨x, hx, hpx⟩
  have hopen : IsOpen (p '' (U : Set X)) := p.isOpenMap _ U.isOpen
  refine ⟨fun s => ?_⟩
  have hs : s ∈ p '' (U : Set X) :=
    (IsLocalRing.specializes_closedPoint s).mem_open hopen hm
  obtain ⟨z, hz, hpz⟩ := hs
  exact ⟨⟨z, hz⟩, hpz⟩

/-- Every total open meeting the closed fibre of a smooth geometrically
connected morphism over a local ring has geometrically integral fibres. -/
theorem geometricallyIntegral_open_of_meets_closedFibre
    [Smooth p] [GeometricallyConnected p] (U : X.Opens)
    (hU : (p ⁻¹' {IsLocalRing.closedPoint R} ∩ (U : Set X)).Nonempty) :
    GeometricallyIntegral (U.ι ≫ p) := by
  let : GeometricallyIntegral p :=
    geometricallyIntegral_of_smooth_geometricallyConnected p
  let : Surjective (U.ι ≫ p) := surjective_open_of_meets_closedFibre p U hU
  exact geometricallyIntegral_open_of_surjective p U

end Langlands.AlgebraicGeometry
