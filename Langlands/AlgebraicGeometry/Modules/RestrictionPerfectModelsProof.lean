import Langlands.AlgebraicGeometry.Modules.RestrictionPerfectModelsReduction
import Langlands.AlgebraicGeometry.Modules.CechResolution.PerfectModelBaseChange
import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsProof
import Langlands.AlgebraicGeometry.OrderedAffineCoverCompact
import Langlands.Cohomology.ModuleComplex.FlatQuasiIsoBaseChange

/-!
# Restriction-compatible perfect models: proof

Every line bundle on a smooth proper family over an affine base has a universal perfect model.
Take a strictly perfect `K` with some derived isomorphism `e : K ≅ RΓ_R(X, L)`
(`universalPerfectSections`) and a finite ordered affine cover `𝒰` of `X`. The derived Čech
comparison `c` from the alternating Čech complex `C` of `L` to `RΓ_R(X, L)` is an isomorphism,
and `e ≫ c⁻¹` is the image of a chain map `v : K ⟶ C`, a quasi-isomorphism. The model is
`a = Q(v) ≫ c`. Its base change along a pullback square is invertible exactly when the scalar
extension of `v` is a quasi-isomorphism. That holds because `K` and `C` are bounded above with
flat terms (`f` is flat).
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules

attribute [local instance] HasDerivedCategory.standard

open DerivedSections

/-- Every line bundle on a smooth proper family over an affine base has a universal perfect
model, built from the derived Čech comparison of a finite affine cover. -/
theorem universalPerfectModel {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    [Smooth f] [IsProper f] (L : LineBundle X) : UniversalPerfectModel f L := by
  obtain ⟨K, hK, ⟨e⟩, -⟩ := universalPerfectSections R X f inferInstance inferInstance L
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := Scheme.OrderedAffineCover.ofCompactSpace X
  let c := CechResolution.cechDerivedComparisonIso f 𝒰 L.obj
  obtain ⟨v, hv⟩ := exists_chainMap_of_isStrictlyPerfect hK (e.hom ≫ c.inv)
  have hva : DerivedCategory.Q.map v ≫ CechResolution.cechDerivedComparison f 𝒰 L.obj =
      e.hom := by
    rw [hv, Category.assoc]
    change e.hom ≫ c.inv ≫ c.hom = e.hom
    rw [c.inv_hom_id]
    exact Category.comp_id _
  refine ⟨K, hK, DerivedCategory.Q.map v ≫ CechResolution.cechDerivedComparison f 𝒰 L.obj,
    ?_, ?_⟩
  · rw [hva]
    infer_instance
  intro T φ X' p f' hp
  rw [CechResolution.isIso_perfectModelBaseChange_cechDerivedComparison_iff hp L 𝒰 v hK]
  have : QuasiIso v := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, hv]
    infer_instance
  obtain ⟨⟨-, b, -, hb⟩, hfin⟩ := hK
  let n : ℤ := Fintype.card 𝒰.ι
  have := CochainComplex.isStrictlyLE_of_le K b (max b n) (le_max_left _ _)
  have := CechResolution.isStrictlyLE_extend_cechCochainComplex f 𝒰 L.obj
  have := CochainComplex.isStrictlyLE_of_le
    ((CechResolution.cechCochainComplex f 𝒰 L.obj).extend ComplexShape.embeddingUpNat)
    n (max b n) (le_max_right _ _)
  exact ModuleComplex.quasiIso_baseChange_map_of_flat φ.hom v (max b n)
    (fun i => have := (hfin i).2; inferInstance)
    (CechResolution.flat_extend_cechCochainComplex_X f 𝒰 L)

/-- Line bundles on smooth proper families over affine bases have one strictly perfect model of
derived sections computing every base change, and closed restrictions are represented by chain
maps of such models compatibly with every base change. -/
theorem restrictionPerfectModels : RestrictionPerfectModelsStatement.{u} :=
  restrictionPerfectModels_of_universalPerfectModel fun _ _ f hfs hfp L =>
    have := hfs
    have := hfp
    universalPerfectModel f L

end Langlands.AlgebraicGeometry.Modules
