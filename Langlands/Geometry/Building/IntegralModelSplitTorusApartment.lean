import Langlands.GroupScheme.Torus.HenselianSplitConjugacy
import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelTorus
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.Geometry.Building.ConjugateApartmentRealization

/-! # Apartments from supplied closed split tori of an integral model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)
    {T₁ T₂ : CommGroupScheme (Spec (CommRingCat.of R))}
    {j₁ : T₁.toGrp ⟶ M.group} {j₂ : T₂.toGrp ⟶ M.group}

/-- Integral conjugacy gives the actual generic conjugacy through the supplied
generic-fibre identification, with the actual integral-point image. -/
theorem genericTorusMap_conjugation
    (g : M.integralSections) (e : T₁ ≅ T₂)
    (h : j₁ ≫ (M.group.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ j₂) :
    M.genericTorusMap T₁ j₁ ≫ (G.innerIso (M.integralPointMap g)).hom =
      CommGroupScheme.groupHom
          ((CommGroupScheme.baseChange (Spec.algebraMap R K)).mapIso e).hom ≫
        M.genericTorusMap T₂ j₂ := by
  let b := Spec.algebraMap R K
  have hg : baseChangeSectionHom b M.group g = baseChangeBasePoint b M.group g := rfl
  change ((GroupScheme.baseChange b).map j₁ ≫ M.genericIso.hom) ≫
      (G.innerIso ((baseChangeSectionHom b M.group g) ≫
        M.genericIso.hom.hom.hom)).hom = _
  rw [Category.assoc, ← innerIso_hom_comp, ← Category.assoc, hg,
    ← baseChange_innerIso_hom, ← Functor.map_comp, h, Functor.map_comp,
    Category.assoc]
  rfl

variable [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    [Smooth M.group.X.hom]
    [ConnectedSpace ((GroupScheme.baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj M.group).X.left]

/-- Two supplied closed integral split tori with maximal split generic fibres
are conjugate by an actual integral point of the generic group. -/
theorem exists_integralPoint_genericTorusMap_conjugacy
    (hG : IsConnectedReductive G)
    (hT₁ : IsSplitTorus T₁.toGrp) (hT₂ : IsSplitTorus T₂.toGrp)
    (hj₁ : IsClosedSubgroup j₁) (hj₂ : IsClosedSubgroup j₂)
    (hmax₁ : IsMaximalSplitTorus (M.genericTorusMap T₁ j₁))
    (hmax₂ : IsMaximalSplitTorus (M.genericTorusMap T₂ j₂)) :
    ∃ g : rationalPoints G, g ∈ M.integralPoints ∧
      ∃ e : T₁ ≅ T₂,
        M.genericTorusMap T₁ j₁ ≫ (G.innerIso g).hom =
          CommGroupScheme.groupHom
              ((CommGroupScheme.baseChange (Spec.algebraMap R K)).mapIso e).hom ≫
            M.genericTorusMap T₂ j₂ := by
  have hres₁ := isMaximalTorus_specialFibre_of_generic hG M hT₁ hj₁ hmax₁
  have hres₂ := isMaximalTorus_specialFibre_of_generic hG M hT₂ hj₂ hmax₂
  obtain ⟨g, e, he⟩ := exists_henselian_splitTorus_conjugacy j₁ j₂ hT₁ hT₂
    inferInstance IsLocalRing.residue_surjective hres₁ hres₂
  exact ⟨M.integralPointMap g, ⟨g, rfl⟩, e, M.genericTorusMap_conjugation g e he⟩

end Langlands.GroupScheme.IntegralModel

namespace Langlands.Geometry.Building

variable {R K : Type u} [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] [Field K] [Algebra R K]
    [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    (M : IntegralModel R K G) [Smooth M.group.X.hom]
    [ConnectedSpace ((GroupScheme.baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj M.group).X.left]
    {T₁ T₂ : CommGroupScheme (Spec (CommRingCat.of R))}
    {j₁ : T₁.toGrp ⟶ M.group} {j₂ : T₂.toGrp ⟶ M.group}

/-- If the integral points fix a subset of the first apartment, the supplied
second generic torus has a conjugate apartment containing that same subset. -/
theorem exists_integralPoint_conjugateApartment_contains
    (hG : IsConnectedReductive G)
    (hT₁ : IsSplitTorus T₁.toGrp) (hT₂ : IsSplitTorus T₂.toGrp)
    (hj₁ : IsClosedSubgroup j₁) (hj₂ : IsClosedSubgroup j₂)
    (hmax₁ : IsMaximalSplitTorus (M.genericTorusMap T₁ j₁))
    (hmax₂ : IsMaximalSplitTorus (M.genericTorusMap T₂ j₂)) :
    letI := mono_of_isMaximalSplitTorus hmax₁
    letI := mono_of_isMaximalSplitTorus hmax₂
    ∀ {ω : Kˣ → ℝ} (D : KPApartmentData (M.genericTorusMap T₁ j₁) ω)
      (Y : Set D.ReducedBuilding),
      Y ⊆ Set.range D.apartmentMap →
      M.integralPoints ≤ D.pointwiseFixer Y →
      ∃ (g : rationalPoints G), g ∈ M.integralPoints ∧
        ∃ (e : (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T₁ ≅
          (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T₂)
          (he : M.genericTorusMap T₁ j₁ ≫ (G.innerIso g).hom =
            CommGroupScheme.groupHom e.hom ≫ M.genericTorusMap T₂ j₂),
          (∀ y ∈ Y, ∃ x : D.Apartment, y = g • D.apartmentMap x) ∧
            Y ⊆ Set.range (D.conjugateApartmentMap e g he) := by
  have := mono_of_isMaximalSplitTorus hmax₁
  have := mono_of_isMaximalSplitTorus hmax₂
  intro ω D Y hY hfix
  obtain ⟨g, hg, e, he⟩ :=
    M.exists_integralPoint_genericTorusMap_conjugacy hG hT₁ hT₂ hj₁ hj₂ hmax₁ hmax₂
  let eK := (CommGroupScheme.baseChange (Spec.algebraMap R K)).mapIso e
  have heK : M.genericTorusMap T₁ j₁ ≫ (G.innerIso g).hom =
      CommGroupScheme.groupHom eK.hom ≫ M.genericTorusMap T₂ j₂ := he
  have hgfix := D.mem_pointwiseFixer.mp (hfix hg)
  refine ⟨g, hg, eK, heK, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx⟩ := hY hy
    exact ⟨x, (hgfix y hy).symm.trans (congrArg (fun z => g • z) hx.symm)⟩
  · intro y hy
    obtain ⟨x, hx⟩ := hY hy
    refine ⟨D.apartmentTransportEquiv eK (G.innerIso g) heK x, ?_⟩
    rw [D.conjugateApartmentMap_transport, hx, hgfix y hy]

/-- Containment in the actual conjugate apartment for two supplied closed
integral split tori with maximal split generic fibres. -/
def IntegralModelSplitTorusApartmentStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] [Field K] [Algebra R K]
    [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    (M : IntegralModel R K G) [Smooth M.group.X.hom]
    [ConnectedSpace
      ((GroupScheme.baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj
        M.group).X.left]
    (T₁ T₂ : CommGroupScheme (Spec (CommRingCat.of R)))
    (j₁ : T₁.toGrp ⟶ M.group) (j₂ : T₂.toGrp ⟶ M.group)
    (_ : IsConnectedReductive G)
    (_ : IsSplitTorus T₁.toGrp) (_ : IsSplitTorus T₂.toGrp)
    (_ : IsClosedSubgroup j₁) (_ : IsClosedSubgroup j₂)
    (hmax₁ : IsMaximalSplitTorus (M.genericTorusMap T₁ j₁))
    (hmax₂ : IsMaximalSplitTorus (M.genericTorusMap T₂ j₂)),
    letI := mono_of_isMaximalSplitTorus hmax₁
    letI := mono_of_isMaximalSplitTorus hmax₂
    ∀ (ω : Kˣ → ℝ) (D : KPApartmentData (M.genericTorusMap T₁ j₁) ω)
      (Y : Set D.ReducedBuilding),
      Y ⊆ Set.range D.apartmentMap →
      M.integralPoints ≤ D.pointwiseFixer Y →
      ∃ (g : rationalPoints G), g ∈ M.integralPoints ∧
        ∃ (e : (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T₁ ≅
          (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T₂)
          (he : M.genericTorusMap T₁ j₁ ≫ (G.innerIso g).hom =
            CommGroupScheme.groupHom e.hom ≫ M.genericTorusMap T₂ j₂),
          (∀ y ∈ Y, ∃ x : D.Apartment, y = g • D.apartmentMap x) ∧
            Y ⊆ Set.range (D.conjugateApartmentMap e g he)

/-- The supplied integral tori and integral-point fixation imply the named
apartment-containment proposition. -/
theorem integralModelSplitTorusApartment :
    IntegralModelSplitTorusApartmentStatement.{u} := by
  intro R K _ _ _ _ _ _ _ G _ M _ _ T₁ T₂ j₁ j₂ hG hT₁ hT₂ hj₁ hj₂ hmax₁ hmax₂ ω
  exact exists_integralPoint_conjugateApartment_contains M hG hT₁ hT₂ hj₁ hj₂ hmax₁ hmax₂

end Langlands.Geometry.Building
