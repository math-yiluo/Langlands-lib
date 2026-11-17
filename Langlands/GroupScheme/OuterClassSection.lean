import Langlands.GroupScheme.OuterIsomorphismScheme

/-! # Integral sections and finite carriers of outer classes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme.FiniteGenericOuterClass

section GeneralBase

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  {I : GroupIsomorphismScheme G H} {a : AutomorphicAction A G}
  {O : OuterIsomorphismScheme I a} {T : Over S} {p : T ⟶ I.parameter}

/-- An integral outer class supplies a finite carrier equal to the base. -/
def ofIntegralClass (s : Over.mk (𝟙 S) ⟶ O.parameter)
    (hs : toUnit T ≫ s = p ≫ O.classMap) : FiniteGenericOuterClass O p where
  component := Over.mk (𝟙 S)
  finite := by change IsFinite (𝟙 S); infer_instance
  classMap := s
  genericPoint := toUnit T
  generic_class := hs

/-- If the entire outer parameter is finite, it is itself a finite carrier. -/
def ofFiniteParameter [IsFinite O.parameter.hom] : FiniteGenericOuterClass O p where
  component := O.parameter
  classMap := 𝟙 _
  genericPoint := p ≫ O.classMap
  generic_class := Category.comp_id _

/-- A carrier depends only on the outer class of the specified point. -/
def ofClassEq (C : FiniteGenericOuterClass O p) {q : T ⟶ I.parameter}
    (hpq : p ≫ O.classMap = q ≫ O.classMap) : FiniteGenericOuterClass O q where
  component := C.component
  classMap := C.classMap
  genericPoint := C.genericPoint
  generic_class := C.generic_class.trans hpq

/-- Finite-carrier existence depends only on the specified outer class. -/
theorem nonempty_iff_of_class_eq {q : T ⟶ I.parameter}
    (hpq : p ≫ O.classMap = q ≫ O.classMap) :
    Nonempty (FiniteGenericOuterClass O p) ↔ Nonempty (FiniteGenericOuterClass O q) :=
  ⟨fun ⟨C⟩ => ⟨C.ofClassEq hpq⟩, fun ⟨C⟩ => ⟨C.ofClassEq hpq.symm⟩⟩

end GeneralBase

section ValuationBase

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {G H A : GroupScheme (Spec (CommRingCat.of R))}
  {I : GroupIsomorphismScheme G H} {a : AutomorphicAction A G}
  {O : OuterIsomorphismScheme I a}
  {p : Over.mk (Spec.algebraMap R K) ⟶ I.parameter}

/-- Over a valuation ring, a finite carrier exists exactly when the generic
outer class extends to a section over the base. -/
theorem nonempty_iff_exists_integralClass :
    Nonempty (FiniteGenericOuterClass O p) ↔
      ∃ s : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ O.parameter,
        toUnit (Over.mk (Spec.algebraMap R K)) ≫ s = p ≫ O.classMap := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.integralClass, C.integralClass_generic⟩
  · rintro ⟨s, hs⟩
    exact ⟨ofIntegralClass s hs⟩

end ValuationBase

end Langlands.GroupScheme.FiniteGenericOuterClass
