import Langlands.Geometry.Analytic.GeneralizedAffinoid.Relations
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Embedding

/-! # Finite weighted variable adjunction with added equations -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s : PositivePolyradius (Fin m))
  (equations : Set (GeneralizedTateAlgebra (A.polyradius.append s) K))

/-- Include the actual old ideal and impose the supplied enlarged-series equations. -/
def relations : Set (GeneralizedTateAlgebra (A.polyradius.append s) K) :=
  appendLeft A.polyradius s K '' (A.ideal : Set (GeneralizedTateAlgebra A.polyradius K)) ∪
    equations

/-- The actual closed-relation quotient of the enlarged weighted Tate algebra. -/
def algebra : PresentedAffinoidAlgebra K :=
  ofRelations K (A.arity + m) (A.polyradius.append s) (relations K A s equations)

/-- The map from the original quotient, obtained by descending its variable inclusion. -/
def baseMap : BoundedAlgHom K A (algebra K A s equations) := by
  let γ := (presentationMap K (algebra K A s equations)).comp (appendLeft A.polyradius s K)
  have hI : ∀ f ∈ A.ideal, γ f = 0 := fun f hf =>
    presentationMap_relation K (A.arity + m) (A.polyradius.append s)
      (relations K A s equations) (Set.mem_union_left _ ⟨f, hf, rfl⟩)
  letI := A.ideal_closed
  exact BoundedAlgHom.liftQuotient K A.ideal γ hI

@[simp] theorem baseMap_presentationMap (f : GeneralizedTateAlgebra A.polyradius K) :
    baseMap K A s equations (presentationMap K A f) =
      presentationMap K (algebra K A s equations) (appendLeft A.polyradius s K f) := rfl

/-- The map on quotient norms is contractive, not just bounded. -/
theorem norm_baseMap_le (a : A) : ‖baseMap K A s equations a‖ ≤ ‖a‖ := by
  let := A.ideal_closed
  have h := BoundedAlgHom.quotient_norm_bound A.ideal
    (baseMap K A s equations).toAlgHom.toRingHom 1 zero_lt_one
    (fun f => by
      change ‖presentationMap K (algebra K A s equations)
        (appendLeft A.polyradius s K f)‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact (norm_presentationMap_le K (algebra K A s equations)
        (appendLeft A.polyradius s K f)).trans_eq (norm_appendLeft A.polyradius s K f)) a
  change ‖baseMap K A s equations a‖ ≤ 1 * ‖a‖ at h
  simpa only [one_mul] using h

/-- The original coordinates retain their places in the first variable block. -/
theorem baseMap_coordinate (i : Fin A.arity) :
    baseMap K A s equations (coordinate K A i) =
      coordinate K (algebra K A s equations) (Fin.castAdd m i) := by
  change presentationMap K (algebra K A s equations)
    (appendLeft A.polyradius s K (X A.polyradius K i)) = _
  rw [appendLeft_X]
  rfl

/-- The actual newly adjoined coordinate in the quotient. -/
def newCoordinate (j : Fin m) : algebra K A s equations :=
  coordinate K (algebra K A s equations) (Fin.natAdd A.arity j)

/-- Each new coordinate has norm at most its specified positive radius. -/
theorem norm_newCoordinate_le (j : Fin m) : ‖newCoordinate K A s equations j‖ ≤ s j := by
  have h :=
    norm_coordinate_le K (algebra K A s equations) (Fin.natAdd A.arity j)
  change ‖newCoordinate K A s equations j‖ ≤
    (A.polyradius.append s) (Fin.natAdd A.arity j) at h
  simpa only [PositivePolyradius.append_natAdd] using h

/-- Every supplied extra equation vanishes in the constructed quotient. -/
theorem presentationMap_equation {f : GeneralizedTateAlgebra (A.polyradius.append s) K}
    (hf : f ∈ equations) :
    presentationMap K (algebra K A s equations) f = 0 :=
  presentationMap_relation K (A.arity + m) (A.polyradius.append s)
    (relations K A s equations) (Set.mem_union_right _ hf)

/-- With no extra equations, setting every new variable to zero descends to the
original quotient. -/
def zeroSpecialization : BoundedAlgHom K (algebra K A s ∅) A := by
  let γ := (presentationMap K A).comp (appendProjectLeft A.polyradius s K)
  apply descendRelations K (A.arity + m) (A.polyradius.append s)
    (relations K A s ∅) A γ
  intro f hf
  rcases hf with ⟨g, hg, rfl⟩ | hf
  · change presentationMap K A
      (appendProjectLeft A.polyradius s K (appendLeft A.polyradius s K g)) = 0
    rw [appendProjectLeft_appendLeft]
    exact (presentationMap_eq_zero_iff K A g).mpr hg
  · exact False.elim hf

@[simp] theorem zeroSpecialization_presentationMap
    (f : GeneralizedTateAlgebra (A.polyradius.append s) K) :
    zeroSpecialization K A s (presentationMap K (algebra K A s ∅) f) =
      presentationMap K A (appendProjectLeft A.polyradius s K f) := rfl

/-- Zero specialization is contractive for the actual quotient norms. -/
theorem norm_zeroSpecialization_le (b : algebra K A s ∅) :
    ‖zeroSpecialization K A s b‖ ≤ ‖b‖ := by
  let := (algebra K A s ∅).ideal_closed
  have h := BoundedAlgHom.quotient_norm_bound (algebra K A s ∅).ideal
    (zeroSpecialization K A s).toAlgHom.toRingHom 1 zero_lt_one
    (fun f => by
      change ‖presentationMap K A (appendProjectLeft A.polyradius s K f)‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact (norm_presentationMap_le K A _).trans
        (norm_appendProjectLeft_le A.polyradius s K f)) b
  change ‖zeroSpecialization K A s b‖ ≤ 1 * ‖b‖ at h
  simpa only [one_mul] using h

@[simp] theorem zeroSpecialization_baseMap (a : A) :
    zeroSpecialization K A s (baseMap K A s ∅ a) = a := by
  obtain ⟨f, rfl⟩ := presentationMap_surjective K A a
  rw [baseMap_presentationMap, zeroSpecialization_presentationMap, appendProjectLeft_appendLeft]

/-- Unconstrained variable adjunction preserves the original quotient norm exactly. -/
theorem norm_baseMap_empty (a : A) : ‖baseMap K A s ∅ a‖ = ‖a‖ := by
  apply le_antisymm (norm_baseMap_le K A s ∅ a)
  simpa only [zeroSpecialization_baseMap] using
    norm_zeroSpecialization_le K A s (baseMap K A s ∅ a)

theorem isometry_baseMap_empty : Isometry (baseMap K A s ∅) :=
  AddMonoidHomClass.isometry_of_norm (baseMap K A s ∅).toAlgHom
    (norm_baseMap_empty K A s)

end Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin
