import Langlands.GroupScheme.Adjoint.RelativeQuotient
import Langlands.GroupScheme.OuterIsomorphismScheme
import Langlands.GroupScheme.Reductive.GenericInnerIsomorphismTorsor

/-! # Integral inner-isomorphism torsors from supplied outer geometry -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GenericInnerIsomorphismTorsor

variable {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {G H A : GroupScheme (Spec (CommRingCat.of R))}
  {q : G ⟶ A} (hq : IsRelativeAdjointQuotient q)
  (I : GroupIsomorphismScheme G H)
  (O : OuterIsomorphismScheme I hq.innerAction)
  (f : (baseChange (Spec.algebraMap R K)).obj G ≅
    (baseChange (Spec.algebraMap R K)).obj H)
  (C : FiniteGenericOuterClass O (I.classify
    (LocalGroupIso.ofBaseChangeIso (U := Over.mk (Spec.algebraMap R K)) f)))

/-- The actual fibre over the extended finite outer class is an integral
inner-isomorphism torsor containing the prescribed generic isomorphism. -/
def ofOuter : GenericInnerIsomorphismTorsor R K G H f where
  adjoint := A
  isReductive_adjoint := hq.isReductive_target
  quotient := q
  isQuotient := hq.isQuotient
  action := hq.innerAction
  action_restrict := hq.innerAction_restrict
  genericQuotient := hq.fieldQuotient (Spec.algebraMap R K)
  genericAction := hq.innerAction_fieldQuotient (Spec.algebraMap R K)
  parameter := O.fibre C.integralClass
  modObj := O.fibreModObj C.integralClass
  flat := by infer_instance
  surjective := by infer_instance
  quasiCompact := by infer_instance
  shear := O.fibreShear C.integralClass
  localIso := O.fibreLocalIso C.integralClass
  action_localIso := fun _ d p g => O.fibreLocalIso_smul C.integralClass d p g
  genericPoint := C.genericFibrePoint
  genericIso := by
    rw [C.genericFibrePoint_localIso, I.refine_classify,
      LocalGroupIso.toBaseChangeIso_ofBaseChangeIso]

end Langlands.GroupScheme.GenericInnerIsomorphismTorsor
