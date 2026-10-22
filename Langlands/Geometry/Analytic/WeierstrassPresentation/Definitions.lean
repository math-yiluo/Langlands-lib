import Langlands.Geometry.Analytic.TatePresentation.Definitions
import Langlands.Geometry.Analytic.TateUniversal
import Langlands.Geometry.Analytic.BoundedQuotient
import Langlands.Geometry.Analytic.Spectrum.Properties
import Mathlib.Data.Fin.Tuple.Basic

/-! # Actual Weierstrass quotient presentations -/

noncomputable section

universe u

namespace Langlands.Analytic.WeierstrassPresentation

open StrictTateAlgebra PresentedStrictAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (n m : ℕ)

/-- Include the old Tate variables in the first block of a larger Tate algebra. -/
def adjoinVariables :
    BoundedAlgHom K (StrictTateAlgebra (Fin n) K) (StrictTateAlgebra (Fin (n + m)) K) :=
  evaluateHom (Fin n) K _ (fun i => X (Fin (n + m)) K (Fin.castAdd m i))
    (hasBoundedMonomials_of_norm_le _ _ _ fun _ => (norm_X _ _ _).le)

@[simp]
theorem adjoinVariables_X (i : Fin n) :
    adjoinVariables K n m (X (Fin n) K i) =
      X (Fin (n + m)) K (Fin.castAdd m i) :=
  evaluate_X _ _ _ _ _

variable (S : Set (StrictTateAlgebra (Fin n) K))
  (f : Fin m → StrictTateAlgebra (Fin n) K)

/-- Old equations together with the genuine equations `Y_j - f_j = 0`. -/
def relations : Set (StrictTateAlgebra (Fin (n + m)) K) :=
  adjoinVariables K n m '' S ∪
    Set.range (fun j => X (Fin (n + m)) K (Fin.natAdd n j) - adjoinVariables K n m (f j))

/-- The actual quotient of the enlarged Tate algebra by the closed relation ideal. -/
def algebra : PresentedStrictAffinoidAlgebra K :=
  ofRelations K (n + m) (relations K n m S f)

/-- The map from the old presentation, constructed by bounded quotient descent. -/
def baseMap : BoundedAlgHom K (ofRelations K n S) (algebra K n m S f) := by
  let γ := (presentationMap K (algebra K n m S f)).comp (adjoinVariables K n m)
  have hS : ∀ h ∈ S, γ h = 0 := fun h hh =>
    presentationMap_relation K (n + m) (relations K n m S f)
      (Set.mem_union_left _ ⟨h, hh, rfl⟩)
  have hspan : ∀ h ∈ Ideal.span S, γ h = 0 :=
    (Ideal.span_le.mpr hS : Ideal.span S ≤ RingHom.ker γ.toAlgHom.toRingHom)
  letI := (ofRelations K n S).ideal_closed
  exact BoundedAlgHom.liftQuotient K (ofRelations K n S).ideal γ
    (γ.annihilates_closure (Ideal.span S) hspan)

@[simp]
theorem baseMap_presentationMap (h : StrictTateAlgebra (Fin n) K) :
    baseMap K n m S f (presentationMap K (ofRelations K n S) h) =
      presentationMap K (algebra K n m S f) (adjoinVariables K n m h) := rfl

theorem baseMap_coordinate (i : Fin n) :
    baseMap K n m S f (coordinate K (ofRelations K n S) i) =
      coordinate K (algebra K n m S f) (Fin.castAdd m i) := by
  change presentationMap K (algebra K n m S f)
    (adjoinVariables K n m (X (Fin n) K i)) = _
  rw [adjoinVariables_X]
  rfl

/-- The new coordinate is the image of the element whose norm is constrained. -/
theorem coordinate_equation (j : Fin m) :
    coordinate K (algebra K n m S f) (Fin.natAdd n j) =
      baseMap K n m S f (presentationMap K (ofRelations K n S) (f j)) := by
  have h := presentationMap_relation K (n + m) (relations K n m S f)
    (Set.mem_union_right _ (Set.mem_range_self j))
  change Ideal.Quotient.mk ((Ideal.span (relations K n m S f)).closure)
    (X (Fin (n + m)) K (Fin.natAdd n j) - adjoinVariables K n m (f j)) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  exact h

/-- The expected Weierstrass point locus in the spectrum of the base algebra. -/
def locus : Set (BanachSpectrum (ofRelations K n S)) :=
  {x | ∀ j, x (presentationMap K (ofRelations K n S) (f j)) ≤ 1}

end Langlands.Analytic.WeierstrassPresentation
