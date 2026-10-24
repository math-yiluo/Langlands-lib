import Langlands.Geometry.Analytic.StrictTestDomain.RationalTransportSheafStatement
import Langlands.Geometry.Analytic.StrictTestDomain.RationalTransportNormalization

/-! # Conditional sheaf comparison for finite rational transport sites -/

universe u v w

namespace Langlands.Analytic.StrictTestDomain.RationalTransport

open CategoryTheory Opposite

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}

/-- The ordinary rational sheaf condition implies the transport sheaf condition
for type-valued presheaves. -/
theorem isSheaf_of_isSheaf_inclusion {Q : (RationalTransport K P)ᵒᵖ ⥤ Type w}
    (hQ : Presieve.IsSheaf (RationalData.finiteRationalTopology K P)
      (inclusion.op ⋙ Q)) :
    Presieve.IsSheaf (finiteTopology K P) Q := by
  intro U S hS x hx
  obtain ⟨t, ht, hu⟩ := hQ (inclusionSieve S)
    ((mem_finiteTopology_iff_inclusionSieve S).mp hS)
    (x.functorPullback (Z := U.data) inclusion) (hx.functorPullback _)
  change Q.obj (op U) at t
  refine ⟨t, ?_, fun t' ht' => hu t' fun W i hi => ht' _ hi⟩
  intro V f hf
  have hj : S (inclusion.map (normalizedInclusion f)) :=
    (normalizedInclusion_mem_iff S f).mpr hf
  have ht' : Q.map (inclusion.map (normalizedInclusion f)).op t =
      x (inclusion.map (normalizedInclusion f)) hj := ht (normalizedInclusion f) hj
  have hcomp := hx (𝟙 V) (translationIso f.label V).hom hf hj
    ((Category.id_comp f).trans
      (translationIso_hom_comp_normalizedInclusion f).symm)
  calc Q.map f.op t
      = Q.map ((translationIso f.label V).hom ≫
          inclusion.map (normalizedInclusion f)).op t := by
        exact congrArg (fun g : V ⟶ U => Q.map g.op t)
          (translationIso_hom_comp_normalizedInclusion f).symm
    _ = Q.map (translationIso f.label V).hom.op
          (Q.map (inclusion.map (normalizedInclusion f)).op t) := by
        exact Q.map_comp_apply (inclusion.map (normalizedInclusion f)).op
          (translationIso f.label V).hom.op t
    _ = Q.map (translationIso f.label V).hom.op
          (x (inclusion.map (normalizedInclusion f)) hj) := congrArg (Q.map (translationIso f.label V).hom.op) ht'
    _ = x f hf := by simpa using hcomp.symm

/-- A transport presheaf is a sheaf exactly when its restriction to ordinary
rational inclusions is a sheaf, with independent coefficient universes. -/
theorem isSheaf_finiteTopology_iff {A : Type v} [Category.{w} A]
    (Q : (RationalTransport K P)ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (finiteTopology K P) Q ↔
      Presheaf.IsSheaf (RationalData.finiteRationalTopology K P) (inclusion.op ⋙ Q) := by
  constructor
  · intro hQ
    exact inclusion.op_comp_isSheaf_of_isSheaf
      (RationalData.finiteRationalTopology K P) (finiteTopology K P) Q hQ
  · intro hQ E
    exact isSheaf_of_isSheaf_inclusion (hQ E)

/-- The actual transport and ordinary quotient-algebra presheaves have
 equivalent sheaf conditions. -/
theorem algebraPresheaf_isSheaf_iff :
    Presheaf.IsSheaf (finiteTopology K P) (algebraPresheaf (K := K) (P := P)) ↔
      Presheaf.IsSheaf (RationalData.finiteRationalTopology K P)
        (RationalData.rationalPresheaf K P) :=
  (isSheaf_finiteTopology_iff algebraPresheaf).trans
    (Presheaf.isSheaf_of_iso_iff inclusionAlgebraPresheafIso)

/-- The conditional comparison, both for arbitrary coefficients and for the
actual quotient-algebra presheaves. -/
theorem sheafComparison : SheafComparisonStatement.{u, v, w} := by
  constructor
  · intro K _ _ _ P A _ Q
    exact isSheaf_finiteTopology_iff Q
  · intro K _ _ _ P
    exact algebraPresheaf_isSheaf_iff

end Langlands.Analytic.StrictTestDomain.RationalTransport
