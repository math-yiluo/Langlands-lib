import Langlands.Geometry.Analytic.WeierstrassPresentation.Definitions

/-! # Actual rational quotient presentations -/

noncomputable section

universe u

namespace Langlands.Analytic.RationalPresentation

open StrictTateAlgebra PresentedStrictAffinoidAlgebra
open WeierstrassPresentation (adjoinVariables adjoinVariables_X)

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (n m : ℕ) (S : Set (StrictTateAlgebra (Fin n) K))
  (g : StrictTateAlgebra (Fin n) K) (f : Fin m → StrictTateAlgebra (Fin n) K)

/-- The actual base elements `g,f_1,...,f_m` generate the unit ideal.
This is an algebraic condition, not an assumed localization output. -/
def GeneratesUnitIdeal : Prop :=
  Ideal.span (insert (presentationMap K (ofRelations K n S) g)
    (Set.range fun j => presentationMap K (ofRelations K n S) (f j))) = ⊤

/-- The old equations and the genuine rational relations `g * Y_j - f_j`. -/
def relations : Set (StrictTateAlgebra (Fin (n + m)) K) :=
  adjoinVariables K n m '' S ∪ Set.range (fun j =>
    adjoinVariables K n m g * X (Fin (n + m)) K (Fin.natAdd n j) -
      adjoinVariables K n m (f j))

/-- The rational presentation is an actual closed-ideal Tate quotient. -/
def algebra : PresentedStrictAffinoidAlgebra K :=
  ofRelations K (n + m) (relations K n m S g f)

/-- The bounded base map is constructed by descent through the old relations. -/
def baseMap : BoundedAlgHom K (ofRelations K n S) (algebra K n m S g f) := by
  let γ := (presentationMap K (algebra K n m S g f)).comp (adjoinVariables K n m)
  have hS : ∀ h ∈ S, γ h = 0 := fun h hh =>
    presentationMap_relation K (n + m) (relations K n m S g f)
      (Set.mem_union_left _ ⟨h, hh, rfl⟩)
  have hspan : ∀ h ∈ Ideal.span S, γ h = 0 :=
    (Ideal.span_le.mpr hS : Ideal.span S ≤ RingHom.ker γ.toAlgHom.toRingHom)
  letI := (ofRelations K n S).ideal_closed
  exact BoundedAlgHom.liftQuotient K (ofRelations K n S).ideal γ
    (γ.annihilates_closure (Ideal.span S) hspan)

@[simp]
theorem baseMap_presentationMap (h : StrictTateAlgebra (Fin n) K) :
    baseMap K n m S g f (presentationMap K (ofRelations K n S) h) =
      presentationMap K (algebra K n m S g f) (adjoinVariables K n m h) := rfl

theorem baseMap_coordinate (i : Fin n) :
    baseMap K n m S g f (coordinate K (ofRelations K n S) i) =
      coordinate K (algebra K n m S g f) (Fin.castAdd m i) := by
  change presentationMap K (algebra K n m S g f)
    (adjoinVariables K n m (X (Fin n) K i)) = _
  rw [adjoinVariables_X]
  rfl

/-- The quotient satisfies the actual denominator equations. -/
theorem coordinate_equation (j : Fin m) :
    baseMap K n m S g f (presentationMap K (ofRelations K n S) g) *
      coordinate K (algebra K n m S g f) (Fin.natAdd n j) =
        baseMap K n m S g f (presentationMap K (ofRelations K n S) (f j)) := by
  have h := presentationMap_relation K (n + m) (relations K n m S g f)
    (Set.mem_union_right _ (Set.mem_range_self j))
  change Ideal.Quotient.mk ((Ideal.span (relations K n m S g f)).closure)
    (adjoinVariables K n m g * X (Fin (n + m)) K (Fin.natAdd n j) -
      adjoinVariables K n m (f j)) = 0 at h
  rw [map_sub, map_mul, sub_eq_zero] at h
  exact h

/-- The unit-radius rational norm locus in the base spectrum. -/
def locus : Set (BanachSpectrum (ofRelations K n S)) :=
  {x | ∀ j, x (presentationMap K (ofRelations K n S) (f j)) ≤
    x (presentationMap K (ofRelations K n S) g)}


end Langlands.Analytic.RationalPresentation
