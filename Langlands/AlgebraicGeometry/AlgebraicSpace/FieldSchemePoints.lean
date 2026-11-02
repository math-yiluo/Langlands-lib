import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenChartCoverage
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Closed points on schemes locally of finite type over fields -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.FieldSchemePoints

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]

include f in
/-- The Jacobson property is inherited from the spectrum of the base field. -/
theorem jacobsonSpace : JacobsonSpace X :=
  LocallyOfFiniteType.jacobsonSpace f

include f in
/-- Every point specializes to a closed point, without a quasi-compactness
assumption on the scheme. -/
theorem exists_closed_specialization (x : X) :
    ∃ y : X, IsClosed ({y} : Set X) ∧ x ⤳ y := by
  let := jacobsonSpace f
  obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints
    (Z := closure ({x} : Set X))
    ⟨x, subset_closure (Set.mem_singleton x)⟩ isClosed_closure.isLocallyClosed
  exact ⟨y, hyclosed, specializes_iff_mem_closure.mpr hy⟩

include f in
/-- Every nonempty open subset contains a point closed in the entire scheme. -/
theorem exists_closed_mem_open {O : Set X} (hO : IsOpen O) (h : O.Nonempty) :
    ∃ x : X, x ∈ O ∧ IsClosed ({x} : Set X) := by
  let := jacobsonSpace f
  exact nonempty_inter_closedPoints h hO.isLocallyClosed

/-- The base-field algebra structure on the residue field is obtained from
the actual composite of the residue-field point with the structure map. -/
abbrev residueFieldAlgebra (x : X) : Algebra k (X.residueField x) :=
  (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra

/-- At a closed point, the actual residue field is finite dimensional over
the base field with the algebra structure specified above. -/
theorem residueField_finiteDimensional (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := residueFieldAlgebra f x
    FiniteDimensional k (X.residueField x) := by
  have : _root_.AlgebraicGeometry.IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hfinite : _root_.AlgebraicGeometry.IsFinite (X.fromSpecResidueField x ≫ f) := by
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  have hring : (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.Finite := by
    rw [← _root_.AlgebraicGeometry.IsFinite.SpecMap_iff, Spec.map_preimage]
    exact hfinite
  exact hring

end Langlands.AlgebraicGeometry.AlgebraicSpace.FieldSchemePoints
