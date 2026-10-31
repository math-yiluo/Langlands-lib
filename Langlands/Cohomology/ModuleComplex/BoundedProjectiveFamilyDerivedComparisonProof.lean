import Langlands.Cohomology.ModuleComplex.BoundedProjectiveFamilyDerivedComparisonStatement
import Langlands.Cohomology.ModuleComplex.BoundedNatComplexExtensionProof
import Langlands.Cohomology.ModuleComplex.NatModuleQuasiIsoCriterionProof
import Langlands.Cohomology.DerivedPlus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TensorProduct

noncomputable section

namespace Langlands.Cohomology.ModuleComplex

attribute [local instance] HasDerivedCategory.standard

/-- One bounded projective family gives the original and all scalar derived
comparisons whenever the supplied maps satisfy the explicit cycle tests. -/
theorem boundedProjectiveFamilyDerivedComparison :
    BoundedProjectiveFamilyDerivedComparisonStatement.{u} := by
  intro R _ K _ _ _ _ δ hδδ n hbound
  let KN : CochainComplex (ModuleCat.{u} R) ℕ :=
    CochainComplex.of (fun i => ModuleCat.of R (K i))
      (fun i => ModuleCat.ofHom (δ i)) (fun i => by
        apply ModuleCat.hom_ext
        exact hδδ i)
  let e := ComplexShape.embeddingUpNat
  refine ⟨KN.extend e,
    boundedNatComplexExtension R KN n hbound (fun _ => ⟨inferInstance, inferInstance⟩),
    ?_, ?_⟩
  · intro C _ _ d hdd φ hφ h0inj h0surj hposinj hpossurj
    let CN : CochainComplex (ModuleCat.{u} R) ℕ :=
      CochainComplex.of (fun i => ModuleCat.of R (C i))
        (fun i => ModuleCat.ofHom (d i)) (fun i => by
          apply ModuleCat.hom_ext
          exact hdd i)
    let φN : KN ⟶ CN := CochainComplex.ofHom (fun i => ModuleCat.ofHom (φ i))
      (fun i => by
        simp only [KN, CN, CochainComplex.of_d]
        apply ModuleCat.hom_ext
        exact hφ i)
    have hq : QuasiIso φN := by
      apply natModuleQuasiIsoCriterion R KN CN φN
      · simpa [KN, CN, φN, CochainComplex.of.d] using h0inj
      · simpa [KN, CN, φN, CochainComplex.of.d] using h0surj
      · simpa [KN, CN, φN, CochainComplex.of.d] using hposinj
      · simpa [KN, CN, φN, CochainComplex.of.d] using hpossurj
    let := hq
    have : IsIso (DerivedCategory.Q.map (HomologicalComplex.extendMap φN e)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
    exact ⟨asIso (DerivedCategory.Q.map (HomologicalComplex.extendMap φN e))⟩
  · intro A _ f
    let := f.toAlgebra
    intro C _ _ d hdd Θ hΘ h0inj h0surj hposinj hpossurj
    let CN : CochainComplex (ModuleCat.{u} A) ℕ :=
      CochainComplex.of (fun i => ModuleCat.of A (C i))
        (fun i => ModuleCat.ofHom (d i)) (fun i => by
          apply ModuleCat.hom_ext
          exact hdd i)
    let F := (ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)
    let ΘN : F.obj KN ⟶ CN :=
      CochainComplex.ofHom (fun i => ModuleCat.ofHom (Θ i)) (fun i => by
        apply ModuleCat.hom_ext
        simpa [F, KN, CN, CochainComplex.of.d, Functor.mapHomologicalComplex,
          ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
          ModuleCat.ExtendScalars.obj', ModuleCat.restrictScalars,
          ModuleCat.RestrictScalars.obj', ModuleCat.ofHom_apply] using (hΘ i).symm)
    have hq : QuasiIso ΘN := by
      apply natModuleQuasiIsoCriterion A (F.obj KN) CN ΘN
      · simpa [F, KN, CN, ΘN, CochainComplex.of.d, Functor.mapHomologicalComplex,
          ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
          ModuleCat.ExtendScalars.obj', ModuleCat.restrictScalars,
          ModuleCat.RestrictScalars.obj', ModuleCat.ofHom_apply] using h0inj
      · simpa [F, KN, CN, ΘN, CochainComplex.of.d, Functor.mapHomologicalComplex,
          ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
          ModuleCat.ExtendScalars.obj', ModuleCat.restrictScalars,
          ModuleCat.RestrictScalars.obj', ModuleCat.ofHom_apply] using h0surj
      · simpa [F, KN, CN, ΘN, CochainComplex.of.d, Functor.mapHomologicalComplex,
          ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
          ModuleCat.ExtendScalars.obj', ModuleCat.restrictScalars,
          ModuleCat.RestrictScalars.obj', ModuleCat.ofHom_apply] using hposinj
      · simpa [F, KN, CN, ΘN, CochainComplex.of.d, Functor.mapHomologicalComplex,
          ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
          ModuleCat.ExtendScalars.obj', ModuleCat.restrictScalars,
          ModuleCat.RestrictScalars.obj', ModuleCat.ofHom_apply] using hpossurj
    let := hq
    have : IsIso (DerivedCategory.Q.map (HomologicalComplex.extendMap ΘN e)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
    exact ⟨(DerivedCategory.Q.mapIso
      (DerivedPlus.mapExtendIso (ModuleCat.extendScalars f) KN e)).symm ≪≫
        asIso (DerivedCategory.Q.map (HomologicalComplex.extendMap ΘN e))⟩

end Langlands.Cohomology.ModuleComplex
