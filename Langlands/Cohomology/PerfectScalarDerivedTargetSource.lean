import Langlands.Cohomology.PerfectScalarDerivedTarget

/-!
# Source naturality of the perfect-source scalar adjunction

The canonical derived unit `Q K ⟶ G(Q(F K))` is natural in chain maps `K ⟶ K'`. Consequently
the perfect-source scalar adjunction `perfectScalarDerivedTargetHomEquiv` is natural in chain
maps between strictly perfect sources.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits

universe uC vC wC uD vD wD u

section General

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G)

/-- The canonical derived unit is natural in chain maps. -/
@[reassoc]
lemma derivedComplexAdjunctionUnit_naturality {K K' : CochainComplex C ℤ} (ψ : K ⟶ K') :
    DerivedCategory.Q.map ψ ≫ derivedComplexAdjunctionUnit adj K' =
      derivedComplexAdjunctionUnit adj K ≫
        G.mapDerivedCategory.map
          (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map ψ)) := by
  have h₁ := (complexAdjunction adj (.up ℤ)).unit.naturality ψ
  have h₂ := G.mapDerivedCategoryFactors.inv.naturality
    ((F.mapHomologicalComplex (.up ℤ)).map ψ)
  simp only [Functor.id_map, Functor.comp_map] at h₁ h₂
  simp only [derivedComplexAdjunctionUnit, Category.assoc, ← h₂]
  rw [← Functor.map_comp_assoc, h₁, Functor.map_comp_assoc]

end General

namespace ModuleComplex

variable {R S : Type u} [CommRing R] [CommRing S]
  [HasDerivedCategory.{wC} (ModuleCat.{u} R)]
  [HasDerivedCategory.{wD} (ModuleCat.{u} S)]

/-- The perfect-source scalar adjunction is natural in chain maps between strictly perfect
sources. -/
lemma perfectScalarDerivedTargetHomEquiv_naturality_source
    (φ : R →+* S) {K K' : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) (hK' : IsStrictlyPerfect K') (ψ : K ⟶ K')
    {Y : DerivedCategory (ModuleCat.{u} S)}
    (f : DerivedCategory.Q.obj ((baseChange φ).obj K') ⟶ Y) :
    perfectScalarDerivedTargetHomEquiv φ K hK Y
        (DerivedCategory.Q.map ((baseChange φ).map ψ) ≫ f) =
      DerivedCategory.Q.map ψ ≫ perfectScalarDerivedTargetHomEquiv φ K' hK' Y f := by
  simp only [perfectScalarDerivedTargetHomEquiv_apply]
  erw [Functor.map_comp]
  rw [derivedComplexAdjunctionUnit_naturality_assoc]
  rfl

/-- Inverse form of `perfectScalarDerivedTargetHomEquiv_naturality_source`: the scalar-extension
adjunct is natural in chain maps between strictly perfect sources. -/
lemma perfectScalarDerivedTargetHomEquiv_symm_naturality_source
    (φ : R →+* S) {K K' : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) (hK' : IsStrictlyPerfect K') (ψ : K ⟶ K')
    {Y : DerivedCategory (ModuleCat.{u} S)}
    (b : DerivedCategory.Q.obj K' ⟶
      (ModuleCat.restrictScalars φ).mapDerivedCategory.obj Y) :
    DerivedCategory.Q.map ((baseChange φ).map ψ) ≫
        (perfectScalarDerivedTargetHomEquiv φ K' hK' Y).symm b =
      (perfectScalarDerivedTargetHomEquiv φ K hK Y).symm (DerivedCategory.Q.map ψ ≫ b) := by
  rw [Equiv.eq_symm_apply, perfectScalarDerivedTargetHomEquiv_naturality_source φ hK hK',
    Equiv.apply_symm_apply]

/-- Inverse form of `perfectScalarDerivedTargetHomEquiv_naturality`: the scalar-extension
adjunct is natural in the derived target. -/
lemma perfectScalarDerivedTargetHomEquiv_symm_naturality
    (φ : R →+* S) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsStrictlyPerfect K) {Y Z : DerivedCategory (ModuleCat.{u} S)}
    (b : DerivedCategory.Q.obj K ⟶ (ModuleCat.restrictScalars φ).mapDerivedCategory.obj Y)
    (g : Y ⟶ Z) :
    (perfectScalarDerivedTargetHomEquiv φ K hK Z).symm
        (b ≫ (ModuleCat.restrictScalars φ).mapDerivedCategory.map g) =
      (perfectScalarDerivedTargetHomEquiv φ K hK Y).symm b ≫ g := by
  rw [Equiv.symm_apply_eq, perfectScalarDerivedTargetHomEquiv_naturality,
    Equiv.apply_symm_apply]

end ModuleComplex

end Langlands.Cohomology
