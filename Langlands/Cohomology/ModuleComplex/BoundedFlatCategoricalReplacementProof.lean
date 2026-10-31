import Langlands.Cohomology.ModuleComplex.BoundedFlatCategoricalReplacementStatement
import Langlands.Cohomology.ModuleComplex.BoundedFlatComplexProjectiveProof
import Langlands.Cohomology.ModuleComplex.BoundedFlatQuasiIsoBaseChangeProof
import Langlands.Cohomology.ModuleComplex.NatModuleQuasiIsoCriterionProof
import Langlands.Cohomology.ModuleComplex.BoundedNatComplexExtensionProof
import Langlands.Cohomology.DerivedPlus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

noncomputable section

namespace Langlands.Cohomology.ModuleComplex

attribute [local instance] HasDerivedCategory.standard

/-- A single finite projective replacement computes every scalar extension. -/
theorem boundedFlatCategoricalReplacement : BoundedFlatCategoricalReplacementStatement.{u} := by
  intro R _ _ C _ n hbound hfin0 hfin
  let d (i : ℕ) := (C.d i (i + 1)).hom
  have hdd (i : ℕ) : d (i + 1) ∘ₗ d i = 0 := by
    exact congrArg (fun f : C.X i ⟶ C.X (i + 2) => f.hom)
      (C.d_comp_d i (i + 1) (i + 2))
  obtain ⟨K, hKadd, hKmod, hKfin, hKproj, δ, hδδ, hKbound, φ, hφ,
      h0inj, h0surj, hposinj, hpossurj⟩ :=
    boundedFlatComplexProjective R (fun i => C.X i) d hdd n hbound hfin0 hfin
  let := hKadd
  let := hKmod
  let := hKfin
  let := hKproj
  let KN : CochainComplex (ModuleCat.{u} R) ℕ :=
    CochainComplex.of (fun i => ModuleCat.of R (K i))
      (fun i => ModuleCat.ofHom (δ i)) (fun i => by
        apply ModuleCat.hom_ext
        exact hδδ i)
  let φN : KN ⟶ C := CochainComplex.ofHom (fun i => ModuleCat.ofHom (φ i))
    (fun i => by
      simp only [KN, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      exact hφ i)
  have hq : QuasiIso φN := by
    apply natModuleQuasiIsoCriterion R KN C φN
    · simpa [KN, φN, CochainComplex.of.d, d] using h0inj
    · simpa [KN, φN, CochainComplex.of.d, d] using h0surj
    · simpa [KN, φN, CochainComplex.of.d, d] using hposinj
    · simpa [KN, φN, CochainComplex.of.d, d] using hpossurj
  let := hq
  let e := ComplexShape.embeddingUpNat
  have hperfect : IsStrictlyPerfect (KN.extend e) :=
    boundedNatComplexExtension R KN n hKbound (fun i => ⟨hKfin i, hKproj i⟩)
  have hQ : IsIso (DerivedCategory.Q.map (HomologicalComplex.extendMap φN e)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  refine ⟨KN.extend e, hperfect, ⟨asIso (DerivedCategory.Q.map
    (HomologicalComplex.extendMap φN e))⟩, ?_⟩
  intro A _ f
  let := f.toAlgebra
  obtain ⟨hA0inj, hA0surj, hAposinj, hApossurj⟩ :=
    boundedFlatQuasiIsoBaseChange R K δ hδδ (fun i => C.X i) d hdd n
      hKbound hbound φ hφ h0inj h0surj hposinj hpossurj A
  let F := (ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)
  have hAq : QuasiIso (F.map φN) := by
    apply natModuleQuasiIsoCriterion A (F.obj KN) (F.obj C) (F.map φN)
    · simpa [F, KN, φN, d, CochainComplex.of.d, Functor.mapHomologicalComplex,
        ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
        ModuleCat.ExtendScalars.obj', ModuleCat.restrictScalars,
        ModuleCat.RestrictScalars.obj', ModuleCat.ofHom_apply] using hA0inj
    · simpa [F, KN, φN, d, CochainComplex.of.d, Functor.mapHomologicalComplex,
        ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
        ModuleCat.ExtendScalars.obj', ModuleCat.restrictScalars,
        ModuleCat.RestrictScalars.obj', ModuleCat.ofHom_apply] using hA0surj
    · simpa [F, KN, φN, d, CochainComplex.of.d, Functor.mapHomologicalComplex,
        ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
        ModuleCat.ExtendScalars.obj', ModuleCat.restrictScalars,
        ModuleCat.RestrictScalars.obj', ModuleCat.ofHom_apply] using hAposinj
    · simpa [F, KN, φN, d, CochainComplex.of.d, Functor.mapHomologicalComplex,
        ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
        ModuleCat.ExtendScalars.obj', ModuleCat.restrictScalars,
        ModuleCat.RestrictScalars.obj', ModuleCat.ofHom_apply] using hApossurj
  let := hAq
  have hAQ : IsIso (DerivedCategory.Q.map
      (HomologicalComplex.extendMap (F.map φN) e)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  exact ⟨(DerivedCategory.Q.mapIso
    (DerivedPlus.mapExtendIso (ModuleCat.extendScalars f) KN e)).symm ≪≫
      asIso (DerivedCategory.Q.map (HomologicalComplex.extendMap (F.map φN) e))⟩

end Langlands.Cohomology.ModuleComplex
