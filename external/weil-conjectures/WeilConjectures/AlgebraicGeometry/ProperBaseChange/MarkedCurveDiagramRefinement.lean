/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.MarkedCurveDiagramRestriction
import WeilConjectures.AlgebraicGeometry.Finite.FiniteImagesNeighbourhoodShrinking
import WeilConjectures.AlgebraicGeometry.Proper.Smooth.ProperSmoothGeometricComponentsLocallyConstant
import WeilConjectures.AlgebraicGeometry.Proper.ProperFibreDimensionUpperSemicontinuous

/-!
# Final shrinking of an existing marked curve diagram

## References

* Stacks Project, Tag 0GK7, final shrinking paragraphs
* Stacks Project, Tag 0GK7, the proper-smooth fibre and marked-open shrinking paragraphs
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- An existing diagram with good fibres and nonempty marks above one base point can
be restricted to a base neighbourhood where those conditions hold everywhere.
The output includes the cartesian comparisons with the original diagram and lifts a
specified map whose image lies over the point. No generic diagram is constructed here.
-/
theorem exists_marked_curve_diagram_refinement
    {X S V Z : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (η : S) (hη : η ∈ U)
    (g : V ⟶ U.toScheme) [IsFinite g] [Surjective g] [UniversallyInjective g]
    (σ : Z ⟶ V) (hσ : ∀ z : Z, (g ≫ U.ι) (σ z) = η)
    (n : ℕ) (T Y B : Fin n → Scheme.{u}) (t : ∀ i, T i ⟶ V)
    (j : ∀ i, Y i ⟶ B i) (p : ∀ i, B i ⟶ T i)
    (ν : (∐ Y) ⟶ pullback f (g ≫ U.ι)) [IsFinite ν] [Surjective ν]
    (hcomm : ∀ i, Sigma.ι Y i ≫ ν ≫ pullback.snd f (g ≫ U.ι) = j i ≫ p i ≫ t i)
    (ht : ∀ i, IsFinite (t i) ∧ Etale (t i))
    (hj : ∀ i, IsOpenImmersion (j i)) (hp : ∀ i, Smooth (p i) ∧ IsProper (p i))
    (W : (pullback f (g ≫ U.ι)).Opens) (hW : IsThickening (pullback.snd ν W.ι))
    (hgood : ∀ i (s : T i), (t i ≫ g ≫ U.ι) s = η →
      GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
      topologicalKrullDim ((p i).fiber s) ≤ 1 ∧
      s ∈ Set.range (((Sigma.ι Y i ≫ ν) ⁻¹ᵁ W).ι ≫ j i ≫ p i)) :
    ∃ (U' : S.Opens) (_ : η ∈ U') (V' : Scheme.{u}) (g' : V' ⟶ U'.toScheme),
      IsFinite g' ∧ Surjective g' ∧ UniversallyInjective g' ∧
      ∃ (aV : V' ⟶ V) (σ' : Z ⟶ V'),
        IsOpenImmersion aV ∧ σ' ≫ aV = σ ∧
        aV ≫ g ≫ U.ι = g' ≫ U'.ι ∧
        ∃ (T' Y' B' : Fin n → Scheme.{u})
          (t' : ∀ i, T' i ⟶ V') (j' : ∀ i, Y' i ⟶ B' i)
          (p' : ∀ i, B' i ⟶ T' i)
          (ν' : (∐ Y') ⟶ pullback f (g' ≫ U'.ι)),
          IsFinite ν' ∧ Surjective ν' ∧
          (∀ i, Sigma.ι Y' i ≫ ν' ≫ pullback.snd f (g' ≫ U'.ι) =
            j' i ≫ p' i ≫ t' i) ∧
          (∀ i, IsFinite (t' i) ∧ Etale (t' i)) ∧
          (∀ i, IsOpenImmersion (j' i)) ∧
          (∀ i, Smooth (j' i ≫ p' i) ∧ Surjective (j' i ≫ p' i)) ∧
          (∀ i, Smooth (p' i) ∧ IsProper (p' i) ∧
            ∀ s : T' i, GeometricallyConnected ((p' i).fiberToSpecResidueField s) ∧
              topologicalKrullDim ((p' i).fiber s) ≤ 1) ∧
          (∃ W' : (pullback f (g' ≫ U'.ι)).Opens,
            (∀ i, Surjective (((Sigma.ι Y' i ≫ ν') ⁻¹ᵁ W').ι ≫ j' i ≫ p' i)) ∧
            IsThickening (pullback.snd ν' W'.ι)) ∧
          ∃ (aY : ∀ i, Y' i ⟶ Y i) (aB : ∀ i, B' i ⟶ B i)
            (aT : ∀ i, T' i ⟶ T i),
            ∀ i,
              IsPullback (aY i) (j' i ≫ p' i ≫ t' i) (j i ≫ p i ≫ t i) aV ∧
              IsPullback (aB i) (p' i ≫ t' i) (p i ≫ t i) aV ∧
              IsPullback (aT i) (t' i) (t i) aV ∧
              j' i ≫ aB i = aY i ≫ j i ∧ p' i ≫ aT i = aB i ≫ p i := by
  classical
  have (i : Fin n) : IsFinite (t i) := (ht i).1
  have (i : Fin n) : IsFinite (t i ≫ g) := inferInstance
  have (i : Fin n) : IsOpenImmersion (j i) := hj i
  have (i : Fin n) : Smooth (p i) := (hp i).1
  have (i : Fin n) : IsProper (p i) := (hp i).2
  let M (i : Fin n) := (Sigma.ι Y i ≫ ν) ⁻¹ᵁ W
  let m (i : Fin n) : (M i).toScheme ⟶ T i := (M i).ι ≫ j i ≫ p i
  have (i : Fin n) : Smooth (m i) := by dsimp [m]; infer_instance
  let G (i : Fin n) : Set (T i) :=
    {s | GeometricallyConnected ((p i).fiberToSpecResidueField s)}
  have hG (i : Fin n) : IsOpen (G i) := by
    rw [isOpen_iff_forall_mem_open]
    intro s hs
    obtain ⟨O, hsO, hO⟩ :=
      (proper_smooth_geometric_components_locally_constant (p i)).2.2.2 s hs
    exact ⟨O, hO, O.isOpen, hsO⟩
  let O (i : Fin n) : (T i).Opens :=
    ⟨G i ∩ {s | topologicalKrullDim ((p i).fiber s) ≤ 1} ∩ Set.range (m i),
      ((hG i).inter (isOpen_setOf_topologicalKrullDim_fiber_le (p i) 1)).inter
        (by simpa only [Set.image_univ] using (m i).isOpenMap Set.univ isOpen_univ)⟩
  have hO (i : Fin n) (s : T i) (hs : (t i ≫ g) s = (⟨η, hη⟩ : U.toScheme)) :
      s ∈ O i := by
    have hs' : (t i ≫ g ≫ U.ι) s = η := by
      simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using
        congrArg (fun x : U.toScheme ↦ x.1) hs
    obtain ⟨hc, hd, hm⟩ := hgood i s hs'
    exact ⟨⟨hc, hd⟩, hm⟩
  obtain ⟨U₀, hη₀, _, hU₀⟩ := exists_affine_neighbourhood_below_finite_maps
    U.toScheme ⟨η, hη⟩ n T (fun i ↦ t i ≫ g) O hO
  apply exists_marked_curve_diagram_restriction f U η hη g U₀ hη₀ σ
    (fun z ↦ by rw [show g (σ z) = (⟨η, hη⟩ : U.toScheme) from
      Subtype.ext (hσ z)]; exact hη₀) n T Y B t j p ν hcomm ht hj hp W hW
  intro i s hs
  obtain ⟨⟨hc, hd⟩, hm⟩ := hU₀ i hs
  exact ⟨hc, hd, hm⟩

end AlgebraicGeometry
