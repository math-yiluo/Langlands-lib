import Langlands.Geometry.Building.CentralIsogenyAffineRoots
import Langlands.Geometry.Building.AffineRootSystemTransport

/-! # Actual affine root systems under central-isogeny pullback -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.Geometry.Building.AffineRootSystem

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {C G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom C.X.hom] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType C.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ C} {j : T.toGrp ⟶ G}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  (q : C ⟶ G) (hq : IsCentralIsogeny q)
  (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
  (t : S ⟶ T) (h : i ≫ q = CommGroupScheme.groupHom t ≫ j)
  (ht : IsIsogeny (CommGroupScheme.groupHom t))
  {ω : kˣ → ℝ} (D : KPApartmentData j ω)

/-- Extended roots are exactly the transported target roots. -/
theorem transportedExtendedRoots_centralIsogenyPullback :
    transportedRoots (D.centralIsogenyApartmentAffineEquiv q hq hS hT t h ht)
        D.extendedAffineRoots =
      (D.centralIsogenyPullback q hq hS hT t h ht).extendedAffineRoots := by
  ext ψ
  obtain ⟨φ, rfl⟩ :=
    (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht).surjective ψ
  change
    D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht φ ∈
        D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht ''
          D.extendedAffineRoots ↔ _
  constructor
  · rintro ⟨χ, hχ, he⟩
    have he' := (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht).injective he
    subst χ
    exact (D.mem_extendedAffineRoots_centralIsogenyPullback_iff q hq hS hT t h ht φ).mpr hχ
  · intro hφ
    exact ⟨φ, (D.mem_extendedAffineRoots_centralIsogenyPullback_iff q hq hS hT t h ht φ).mp hφ,
      rfl⟩

/-- The root-form range transports through the actual reduced-cocharacter map. -/
theorem derivativeTransport_range_rootForm_centralIsogenyPullback :
    derivativeTransport (D.centralIsogenyApartmentAffineEquiv q hq hS hT t h ht) ''
        Set.range (rootForm j) = Set.range (rootForm i) := by
  have hr (a : relativeRoots j) :
      derivativeTransport (D.centralIsogenyApartmentAffineEquiv q hq hS hT t h ht)
          (rootForm j a) =
        rootForm i (centralIsogenyRootPullbackEquiv q hq hS hT t h ht a) := by
    apply LinearMap.ext
    intro v
    exact rootForm_centralIsogenyTranslationEquiv q hq hS hT t h ht a v
  ext f
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨_, (hr a).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨a, rfl⟩ := (centralIsogenyRootPullbackEquiv q hq hS hT t h ht).surjective a
    exact ⟨rootForm j a, ⟨a, rfl⟩, hr a⟩

/-- AS2's root-system object on the actual source apartment. -/
def centralIsogenyExtendedAffineRootSystem
    (hΨ : IsAffineRootSystemWithRankZero D.extendedAffineRoots) :
    {Ψ : Set ((D.centralIsogenyPullback q hq hS hT t h ht).Apartment →ᵃ[ℝ] ℝ) //
      IsAffineRootSystemWithRankZero Ψ} :=
  ⟨(D.centralIsogenyPullback q hq hS hT t h ht).extendedAffineRoots, by
    rw [← D.transportedExtendedRoots_centralIsogenyPullback q hq hS hT t h ht]
    exact hΨ.transport _⟩

/-- AS3's root-system object on the actual source apartment. -/
def centralIsogenyAffineRootSystem
    (hΨ : IsAffineRootSystemWithRankZero D.affineRoots) :
    {Ψ : Set ((D.centralIsogenyPullback q hq hS hT t h ht).Apartment →ᵃ[ℝ] ℝ) //
      IsAffineRootSystemWithRankZero Ψ} :=
  ⟨(D.centralIsogenyPullback q hq hS hT t h ht).affineRoots, by
    rw [← D.transportedRoots_centralIsogenyPullback q hq hS hT t h ht]
    exact hΨ.transport _⟩

/-- AS2's derivative equality is preserved with the original source root forms. -/
theorem derivativeRoots_extendedAffineRoots_centralIsogenyPullback
    (hΨ : derivativeRoots D.extendedAffineRoots = Set.range (rootForm j)) :
    derivativeRoots (D.centralIsogenyPullback q hq hS hT t h ht).extendedAffineRoots =
      Set.range (rootForm i) := by
  rw [← D.transportedExtendedRoots_centralIsogenyPullback q hq hS hT t h ht,
    derivativeRoots_transportedRoots, hΨ]
  exact D.derivativeTransport_range_rootForm_centralIsogenyPullback q hq hS hT t h ht

/-- AS3's derivative equality is preserved with the original source root forms. -/
theorem derivativeRoots_affineRoots_centralIsogenyPullback
    (hΨ : derivativeRoots D.affineRoots = Set.range (rootForm j)) :
    derivativeRoots (D.centralIsogenyPullback q hq hS hT t h ht).affineRoots =
      Set.range (rootForm i) := by
  rw [← D.transportedRoots_centralIsogenyPullback q hq hS hT t h ht,
    derivativeRoots_transportedRoots, hΨ]
  exact D.derivativeTransport_range_rootForm_centralIsogenyPullback q hq hS hT t h ht

/-- AS4 transfers because functional transport is real-linear. -/
theorem mem_or_two_smul_mem_centralIsogenyPullback
    (hΨ : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots) :
    ∀ ψ ∈ (D.centralIsogenyPullback q hq hS hT t h ht).extendedAffineRoots,
      ψ ∈ (D.centralIsogenyPullback q hq hS hT t h ht).affineRoots ∨
        (2 : ℝ) • ψ ∈ (D.centralIsogenyPullback q hq hS hT t h ht).affineRoots := by
  intro ψ hψ
  obtain ⟨φ, rfl⟩ :=
    (D.affineFunctionalCentralIsogenyPullbackEquiv q hq hS hT t h ht).surjective ψ
  rcases hΨ φ
    ((D.mem_extendedAffineRoots_centralIsogenyPullback_iff q hq hS hT t h ht φ).mp hψ)
      with hφ | hφ
  · exact Or.inl ((D.mem_affineRoots_centralIsogenyPullback_iff q hq hS hT t h ht φ).mpr hφ)
  · right
    rw [← map_smul]
    exact (D.mem_affineRoots_centralIsogenyPullback_iff q hq hS hT t h ht _).mpr hφ

end Langlands.Geometry.Building.KPApartmentData
