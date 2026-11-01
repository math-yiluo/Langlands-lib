import Langlands.Cohomology.AcyclicTermsDerivedUnitStatement
import Langlands.Cohomology.AcyclicResolution.ComparisonProof

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.AcyclicComparison

universe w w' u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

theorem quasiIso_map_of_acyclic_terms {K L : CochainComplex.Plus C} (f : K ⟶ L)
    [QuasiIso f.hom]
    (hK : ∀ (i : ℤ) (q : ℕ), IsZero ((F.rightDerived (q + 1)).obj (K.obj.X i)))
    (hL : ∀ (i : ℤ) (q : ℕ), IsZero ((F.rightDerived (q + 1)).obj (L.obj.X i))) :
    QuasiIso ((F.mapHomologicalComplex _).map f.hom) := by
  obtain ⟨m, hm⟩ := K.property
  obtain ⟨n, hn⟩ := L.property
  have hcone : (CochainComplex.mappingCone f.hom).Acyclic :=
    (quasiIso_iff_acyclic_mappingCone _).1 inferInstance
  have hF := acyclic_map F _ hcone (min m n - 1)
    (fun i hi => by
      rw [CochainComplex.mappingCone.isZero_X_iff]
      exact ⟨CochainComplex.isZero_of_isStrictlyGE K.obj m (i + 1) (by omega),
        CochainComplex.isZero_of_isStrictlyGE L.obj n i (by omega)⟩)
    (fun i q => isZero_rightDerived_obj_of_iso F _
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f.hom i (i + 1) rfl).symm
      (isZero_rightDerived_obj_biprod F _ _ _ (hK (i + 1) q) (hL i q)))
  have h₂ : (CochainComplex.mappingCone
      ((F.mapHomologicalComplex _).map f.hom)).Acyclic :=
    fun i => (hF i).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso _ F)
  exact (quasiIso_iff_acyclic_mappingCone _).2 h₂

theorem isIso_derivedUnit_of_acyclic_terms (K : CochainComplex.Plus C)
    (hK : ∀ (i : ℤ) (q : ℕ), IsZero ((F.rightDerived (q + 1)).obj (K.obj.X i))) :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  obtain ⟨m, hm⟩ := K.property
  obtain ⟨L, hL, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective K m
  have : QuasiIso i.hom := hi
  have (j : ℤ) : Injective
      (((InjectiveObject.ι C).mapCochainComplexPlus.obj L).obj.X j) :=
    (L.obj.X j).property
  have hFL := fun (j : ℤ) (q : ℕ) =>
    F.isZero_rightDerived_obj_injective_succ q
      (((InjectiveObject.ι C).mapCochainComplexPlus.obj L).obj.X j)
  have hFi := quasiIso_map_of_acyclic_terms F i hK hFL
  have : IsIso (DerivedCategory.Plus.Q.map i) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso C) i hi
  have : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map i)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso D) _ hFi
  have : IsIso (F.rightDerivedFunctorPlusUnit.app K ≫
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map i)) := by
    have hnat := F.rightDerivedFunctorPlusUnit.naturality i
    simp only [Functor.comp_map] at hnat
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right (F.rightDerivedFunctorPlusUnit.app K)
    (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map i))

end Langlands.Cohomology.AcyclicComparison

namespace Langlands.Cohomology

universe w w' u v u' v'

theorem acyclicTermsDerivedUnitStatement :
    AcyclicTermsDerivedUnitStatement.{w, w', u, v, u', v'} := by
  intro C _ _ _ _ D _ _ _ F _ _ K hK
  exact AcyclicComparison.isIso_derivedUnit_of_acyclic_terms F K hK

end Langlands.Cohomology
