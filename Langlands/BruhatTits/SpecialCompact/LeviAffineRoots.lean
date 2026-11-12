import Langlands.BruhatTits.SpecialCompact.LeviApartmentProjection
import Langlands.Geometry.Building.ChamberExchange

/-! # Actual affine root groups under prescribed-Levi projection -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G M : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [LocallyOfFiniteType M.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (iM : S.toGrp ⟶ M)
    [Mono i.hom.hom.left] [Mono iM.hom.hom.left]
    (j : M ⟶ G) (hcomp : iM ≫ j = i) (ζ : cocharacterLattice S)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {ω : Fˣ → ℝ} (D : KPApartmentData i ω)

local notation "DM" => leviRestrictedApartmentData hS i iM j hcomp ζ hj hjc hG hi D
local notation "π" => leviApartmentAffineProjection hS i iM j hcomp ζ hj hjc hG hi D

/-- Precomposition by the actual surjective prescribed-Levi apartment map. -/
def leviAffineRootPullback (ψ : (DM).Apartment →ᵃ[ℝ] ℝ) : D.Apartment →ᵃ[ℝ] ℝ :=
  ψ.comp π

/-- The pullback retains the actual character of every Levi root. -/
theorem leviAffineRootPullback_linear (a : relativeRoots iM)
    (ψ : (DM).Apartment →ᵃ[ℝ] ℝ) (hψ : ψ.linear = rootForm iM a) :
    (leviAffineRootPullback hS i iM j hcomp ζ hj hjc hG hi D ψ).linear =
      rootForm i ⟨a, relativeRoots_subset_of_factor hj iM hcomp a.property⟩ := by
  change ψ.linear.comp (leviTranslationProjection i iM j hcomp ζ hj) = _
  rw [hψ, rootForm_comp_leviTranslationProjection]

/-- Each finite filtration level has exactly the corresponding ambient image. -/
theorem map_leviApartmentFiltration (x : D.Apartment) (a : relativeRoots iM) (r : ℝ) :
    ((DM).filtration (π x) a r).map (rationalPoints.map j) = D.filtration x a r := by
  apply SetLike.coe_injective
  exact image_leviRestrictedRootFiltration iM j hS i hcomp ζ hj hjc x.val a a.property r

/-- Ordinary affine root groups have exactly the corresponding ambient images. -/
theorem map_leviAffineRootGroup (a : relativeRoots iM)
    (ψ : (DM).Apartment →ᵃ[ℝ] ℝ) (hψ : ψ.linear = rootForm iM a) :
    ((DM).affineRootGroup a ψ).map (rationalPoints.map j) =
      D.affineRootGroup a (leviAffineRootPullback hS i iM j hcomp ζ hj hjc hG hi D ψ) := by
  let x : D.Apartment := Classical.arbitrary _
  rw [(DM).affineRootGroup_eq_filtration hψ (π x),
    D.affineRootGroup_eq_filtration
      (leviAffineRootPullback_linear hS i iM j hcomp ζ hj hjc hG hi D a ψ hψ) x]
  exact map_leviApartmentFiltration hS i iM j hcomp ζ hj hjc hG hi D x a (ψ (π x))

/-- Strict affine root groups have the same image, including all real positive shifts. -/
theorem map_leviAffineRootGroupPlus (a : relativeRoots iM)
    (ψ : (DM).Apartment →ᵃ[ℝ] ℝ) (hψ : ψ.linear = rootForm iM a) :
    ((DM).affineRootGroupPlus a ψ).map (rationalPoints.map j) =
      D.affineRootGroupPlus a (leviAffineRootPullback hS i iM j hcomp ζ hj hjc hG hi D ψ) := by
  rw [KPApartmentData.affineRootGroupPlus, Subgroup.map_iSup]
  unfold KPApartmentData.affineRootGroupPlus
  apply iSup_congr
  intro c
  have hlin : (ψ + AffineMap.const ℝ (DM).Apartment (c : ℝ)).linear = rootForm iM a := by
    rw [AffineMap.add_linear, AffineMap.const_linear, add_zero, hψ]
  have heq : leviAffineRootPullback hS i iM j hcomp ζ hj hjc hG hi D
      (ψ + AffineMap.const ℝ (DM).Apartment (c : ℝ)) =
      leviAffineRootPullback hS i iM j hcomp ζ hj hjc hG hi D ψ +
        AffineMap.const ℝ D.Apartment (c : ℝ) := by
    ext x
    rfl
  rw [map_leviAffineRootGroup hS i iM j hcomp ζ hj hjc hG hi D a _ hlin, heq]

include hS hcomp hj hjc in
/-- The doubled-root subgroup retains its exact meaning under the closed inclusion. -/
theorem map_leviDoubleRootGroupPoints (a : relativeRoots iM) :
    (doubleRootGroupPoints iM a).map (rationalPoints.map j) = doubleRootGroupPoints i a := by
  classical
  have hroots := relativeRoots_centralizer_factor dynamicLie i iM j hcomp ζ hj
  have haz : latticePairing S a ζ = 0 := ((Set.ext_iff.mp hroots a).mp a.property).2
  have h2 : 2 • a.val ∈ relativeRoots iM ↔ 2 • a.val ∈ relativeRoots i := by
    rw [Set.ext_iff.mp hroots (2 • a.val)]
    simp only [Set.mem_setOf_eq, map_nsmul, LinearMap.smul_apply, haz, smul_zero,
      and_true]
  by_cases ha : 2 • a.val ∈ relativeRoots i
  · rw [doubleRootGroupPoints, ite_eq_left (h2.mpr ha), doubleRootGroupPoints, ite_eq_left ha]
    exact map_leviRootGroupPoints hS i iM j hcomp ζ hj hjc _ (h2.mpr ha)
  · rw [doubleRootGroupPoints, ite_eq_right (fun h => ha (h2.mp h)),
      doubleRootGroupPoints, ite_eq_right ha, Subgroup.map_bot]

/-- The ordinary-affine-root noncontainment test is preserved in both directions. -/
theorem leviAffineRootGroup_subset_mul_iff (a : relativeRoots iM)
    (ψ : (DM).Apartment →ᵃ[ℝ] ℝ) (hψ : ψ.linear = rootForm iM a) :
    ((DM).affineRootGroup a ψ : Set (rationalPoints M)) ⊆
        ((DM).affineRootGroupPlus a ψ : Set (rationalPoints M)) *
          (doubleRootGroupPoints iM a : Set (rationalPoints M)) ↔
      (D.affineRootGroup a (leviAffineRootPullback hS i iM j hcomp ζ hj hjc hG hi D ψ) :
          Set (rationalPoints G)) ⊆
        (D.affineRootGroupPlus a
          (leviAffineRootPullback hS i iM j hcomp ζ hj hjc hG hi D ψ) : Set (rationalPoints G)) *
            (doubleRootGroupPoints i a : Set (rationalPoints G)) := by
  have hinj : Function.Injective (rationalPoints.map j) := by
    have : Mono j.hom.hom := hj.1
    intro a b hab
    exact (cancel_mono j.hom.hom).mp hab
  have hlocal := @Set.image_subset_image_iff _ _
    ((DM).affineRootGroup a ψ : Set (rationalPoints M))
    (((DM).affineRootGroupPlus a ψ : Set (rationalPoints M)) *
      (doubleRootGroupPoints iM a : Set (rationalPoints M)))
    (rationalPoints.map j) hinj
  rw [Set.image_mul] at hlocal
  change
    ((((DM).affineRootGroup a ψ).map (rationalPoints.map j) : Set (rationalPoints G)) ⊆
      (((DM).affineRootGroupPlus a ψ).map (rationalPoints.map j) : Set (rationalPoints G)) *
        ((doubleRootGroupPoints iM a).map (rationalPoints.map j) : Set (rationalPoints G))) ↔ _
      at hlocal
  rw [map_leviAffineRootGroup hS i iM j hcomp ζ hj hjc hG hi D a ψ hψ,
    map_leviAffineRootGroupPlus hS i iM j hcomp ζ hj hjc hG hi D a ψ hψ,
    map_leviDoubleRootGroupPoints hS i iM j hcomp ζ hj hjc a] at hlocal
  exact hlocal.symm

/-- A Levi ordinary affine root pulls back to an ordinary ambient affine root. -/
theorem leviAffineRootPullback_mem_affineRoots
    {ψ : (DM).Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ (DM).affineRoots) :
    leviAffineRootPullback hS i iM j hcomp ζ hj hjc hG hi D ψ ∈ D.affineRoots := by
  obtain ⟨a, hlin, hnot⟩ := hψ
  exact ⟨⟨a, relativeRoots_subset_of_factor hj iM hcomp a.property⟩,
    leviAffineRootPullback_linear hS i iM j hcomp ζ hj hjc hG hi D a ψ hlin,
    fun h => hnot ((leviAffineRootGroup_subset_mul_iff hS i iM j hcomp ζ hj hjc hG hi D a ψ hlin).mpr h)⟩

/-- An extended affine root of the Levi pulls back to an extended ambient affine root. -/
theorem leviAffineRootPullback_mem_extendedAffineRoots
    {ψ : (DM).Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ (DM).extendedAffineRoots) :
    leviAffineRootPullback hS i iM j hcomp ζ hj hjc hG hi D ψ ∈ D.extendedAffineRoots := by
  obtain ⟨a, hlin, hnot⟩ := hψ
  refine ⟨⟨a, relativeRoots_subset_of_factor hj iM hcomp a.property⟩,
    leviAffineRootPullback_linear hS i iM j hcomp ζ hj hjc hG hi D a ψ hlin, ?_⟩
  intro heq
  apply hnot
  have hinj : Function.Injective (rationalPoints.map j) := by
    have : Mono j.hom.hom := hj.1
    intro a b hab
    exact (cancel_mono j.hom.hom).mp hab
  apply (Subgroup.map_injective hinj)
  rw [map_leviAffineRootGroup hS i iM j hcomp ζ hj hjc hG hi D a ψ hlin,
    map_leviAffineRootGroupPlus hS i iM j hcomp ζ hj hjc hG hi D a ψ hlin, heq]

/-- An ambient functional in a Levi-root direction descends with its original value. -/
theorem leviAffineFunctional_comp (a : relativeRoots iM) (x : D.Apartment)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ)
    (hψ : ψ.linear = rootForm i ⟨a, relativeRoots_subset_of_factor hj iM hcomp a.property⟩) :
    leviAffineRootPullback hS i iM j hcomp ζ hj hjc hG hi D
      ((DM).affineFunctional a (π x) (ψ x)) = ψ := by
  apply AffineMap.ext_linear
    ((leviAffineRootPullback_linear hS i iM j hcomp ζ hj hjc hG hi D a _ rfl).trans hψ.symm)
  change rootForm iM a (π x -ᵥ π x) + ψ x = ψ x
  rw [vsub_self, map_zero, zero_add]

end Langlands.BruhatTits.SpecialCompact
