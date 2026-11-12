import Langlands.BruhatTits.SpecialCompact.LeviAffineRoots
import Langlands.Geometry.Building.ActualAffineRootArrangement

/-! # Special points and vertices in the prescribed Levi apartment -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise TensorProduct
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.BruhatTits.SpecialCompact

section RootForms
variable {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)

include hS in
/-- At a split torus an actual root is determined by its reduced root form. -/
theorem rootForm_injective_of_split : Function.Injective (rootForm i) := by
  intro a b hab
  apply Subtype.ext
  apply eval_injective hS
  apply LinearMap.ext
  intro v
  exact congrArg (fun f : TranslationSpace i →ₗ[ℝ] ℝ =>
    f (Submodule.Quotient.mk v)) hab

include hS in
/-- The reduced form of every actual root of a split torus is nonzero. -/
theorem rootForm_ne_zero_of_split (a : relativeRoots i) : rootForm i a ≠ 0 := by
  intro hzero
  apply a.property.1
  apply eval_injective hS
  apply LinearMap.ext
  intro v
  have h := congrArg (fun f : TranslationSpace i →ₗ[ℝ] ℝ =>
    f (Submodule.Quotient.mk v)) hzero
  simpa only [rootForm_mk, LinearMap.zero_apply, eval_zero_char] using h

variable [Mono i.hom.hom.left] {ω : Fˣ → ℝ} (D : KPApartmentData i ω)

include hS in
/-- Every actual affine root has nonzero derivative at the split torus. -/
theorem affineRoot_linear_ne_zero_of_split {ψ : D.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ D.affineRoots) : ψ.linear ≠ 0 := by
  obtain ⟨a, hlin, -⟩ := hψ
  rw [hlin]
  exact rootForm_ne_zero_of_split hS i a

include hS in
/-- Root-direction coverage and specialness suffice for vertexhood in the
actual reduced quotient, including the rank-zero case. -/
theorem isVertex_of_isSpecialPoint_of_rootForms_occur
    (hder : ∀ a : relativeRoots i, ∃ ψ ∈ D.affineRoots, ψ.linear = rootForm i a)
    {x : D.Apartment} (hx : AffineRootSystem.IsSpecialPoint D.affineRoots x) :
    AffineRootSystem.IsVertex D.affineRoots x := by
  apply Set.Subset.antisymm
  · intro y hy
    apply Set.mem_singleton_iff.mpr
    apply vsub_eq_zero_iff_eq.mp
    apply Langlands.Geometry.Building.eq_zero_of_rootForm_eq_zero i
    intro a
    obtain ⟨ψ, hψ, hlin⟩ := hder a
    obtain ⟨phi, hphi, hker⟩ := (AffineRootSystem.isSpecialPoint_iff_ker
      (fun _ h => affineRoot_linear_ne_zero_of_split hS i D h) x).mp hx ψ hψ
    have hphiy : phi y = 0 := AffineRootSystem.facet_subset_hyperplane hphi hy
    apply LinearMap.mem_ker.mp
    rw [← hlin, hker, LinearMap.mem_ker, AffineMap.linearMap_vsub]
    change phi y - phi x = 0
    rw [hphiy, hphi.2, sub_self]
  · exact Set.singleton_subset_iff.mpr (AffineRootSystem.mem_facet_self D.affineRoots x)
end RootForms

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
local notation "P" => leviAffineRootPullback hS i iM j hcomp ζ hj hjc hG hi D

/-- An ordinary ambient affine root in a Levi-root direction descends to an
ordinary Levi affine root, with its original value at the chosen point. -/
theorem leviAffineRoot_descend (a : relativeRoots iM) (x : D.Apartment)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ D.affineRoots)
    (hlin : ψ.linear = rootForm i ⟨a, relativeRoots_subset_of_factor hj iM hcomp a.property⟩) :
    (DM).affineFunctional a (π x) (ψ x) ∈ (DM).affineRoots := by
  obtain ⟨b, hb, hnot⟩ := hψ
  have heq : b = ⟨a, relativeRoots_subset_of_factor hj iM hcomp a.property⟩ :=
    rootForm_injective_of_split hS i (hb.symm.trans hlin)
  subst b
  refine ⟨a, rfl, fun h => hnot ?_⟩
  have h' := (leviAffineRootGroup_subset_mul_iff hS i iM j hcomp ζ hj hjc hG hi D
    a ((DM).affineFunctional a (π x) (ψ x)) rfl).mp h
  rwa [leviAffineFunctional_comp hS i iM j hcomp ζ hj hjc hG hi D a x ψ hlin] at h'

/-- A special ambient point has a special image in the actual Levi apartment.
Parallelism forces the ambient vanishing root to have zero Levi pairing. -/
theorem isSpecialPoint_leviApartmentProjection
    {x : D.Apartment} (hx : AffineRootSystem.IsSpecialPoint D.affineRoots x) :
    AffineRootSystem.IsSpecialPoint (DM).affineRoots (π x) := by
  apply (AffineRootSystem.isSpecialPoint_iff_ker
    (fun _ h => affineRoot_linear_ne_zero_of_split hS iM (DM) h) (π x)).mpr
  intro ψ hψ
  obtain ⟨a, hlin, hnot⟩ := hψ
  have hψroot : ψ ∈ (DM).affineRoots := ⟨a, hlin, hnot⟩
  obtain ⟨phi, hphi, hker⟩ := (AffineRootSystem.isSpecialPoint_iff_ker
    (fun _ h => affineRoot_linear_ne_zero_of_split hS i D h) x).mp hx (P ψ)
      (leviAffineRootPullback_mem_affineRoots hS i iM j hcomp ζ hj hjc hG hi D hψroot)
  obtain ⟨b, hb, hbnot⟩ := hphi.1
  have hroots := relativeRoots_centralizer_factor dynamicLie i iM j hcomp ζ hj
  have haz : latticePairing S a ζ = 0 := ((Set.ext_iff.mp hroots a).mp a.property).2
  have hζ : (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] ζ) : TranslationSpace i) ∈
      LinearMap.ker (P ψ).linear := by
    rw [LinearMap.mem_ker, leviAffineRootPullback_linear hS i iM j hcomp ζ hj hjc hG hi D a ψ hlin,
      rootForm_mk, eval_tmul, haz, Int.cast_zero, mul_zero]
  have hbz : latticePairing S b ζ = 0 := by
    rw [hker] at hζ
    rw [LinearMap.mem_ker, hb, rootForm_mk, eval_tmul, one_mul, Int.cast_eq_zero] at hζ
    exact hζ
  let bM : relativeRoots iM := ⟨b, (Set.ext_iff.mp hroots b).mpr ⟨b.property, hbz⟩⟩
  let phiM := (DM).affineFunctional bM (π x) (phi x)
  have hcompphi : P phiM = phi :=
    leviAffineFunctional_comp hS i iM j hcomp ζ hj hjc hG hi D bM x phi hb
  have hphiM : phiM ∈ (DM).affineRoots :=
    leviAffineRoot_descend hS i iM j hcomp ζ hj hjc hG hi D bM x hphi.1 hb
  refine ⟨phiM, ⟨hphiM, ?_⟩, ?_⟩
  · change rootForm iM bM (π x -ᵥ π x) + phi x = 0
    rw [vsub_self, map_zero, zero_add, hphi.2]
  · apply SetLike.ext
    intro v
    obtain ⟨w, rfl⟩ := leviTranslationProjection_surjective i iM j hcomp ζ hj v
    change (P ψ).linear w = 0 ↔ (P phiM).linear w = 0
    rw [hcompphi]
    exact SetLike.ext_iff.mp hker w

/-- AS3 root-direction coverage in the ambient apartment descends to the Levi. -/
theorem levi_rootForms_occur
    (hder : AffineRootSystem.derivativeRoots D.affineRoots = Set.range (rootForm i))
    (a : relativeRoots iM) :
    ∃ ψ ∈ (DM).affineRoots, ψ.linear = rootForm iM a := by
  have ha : rootForm i ⟨a, relativeRoots_subset_of_factor hj iM hcomp a.property⟩ ∈
      AffineRootSystem.derivativeRoots D.affineRoots := by
    rw [hder]
    exact Set.mem_range_self _
  obtain ⟨ψ, hψ, hlin⟩ := ha
  let x : D.Apartment := Classical.arbitrary _
  exact ⟨(DM).affineFunctional a (π x) (ψ x),
    leviAffineRoot_descend hS i iM j hcomp ζ hj hjc hG hi D a x hψ hlin, rfl⟩

/-- At the same projected point, specialness and ambient AS3 yield a special vertex. -/
theorem isSpecialPoint_isVertex_leviApartmentProjection
    (hder : AffineRootSystem.derivativeRoots D.affineRoots = Set.range (rootForm i))
    {x : D.Apartment} (hx : AffineRootSystem.IsSpecialPoint D.affineRoots x) :
    AffineRootSystem.IsSpecialPoint (DM).affineRoots (π x) ∧
      AffineRootSystem.IsVertex (DM).affineRoots (π x) := by
  have hs := isSpecialPoint_leviApartmentProjection hS i iM j hcomp ζ hj hjc hG hi D hx
  exact ⟨hs, isVertex_of_isSpecialPoint_of_rootForms_occur hS iM (DM)
    (levi_rootForms_occur hS i iM j hcomp ζ hj hjc hG hi D hder) hs⟩

section LocalField
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The original projection, now packaged with its special-vertex and literal
valuation-restriction properties. No new point is chosen. -/
def leviSpecialApartmentVertex (D₀ : KPApartmentData i (localFieldOrder F))
    (hder : AffineRootSystem.derivativeRoots D₀.affineRoots = Set.range (rootForm i))
    (x : D₀.Apartment) (hx : AffineRootSystem.IsSpecialPoint D₀.affineRoots x) :
    {xM : (leviRestrictedApartmentData hS i iM j hcomp ζ hj hjc hG hi D₀).Apartment //
      (leviRestrictedApartmentData hS i iM j hcomp ζ hj hjc hG hi D₀).IsSpecialApartmentVertex xM ∧
        IsLeviRestriction j x xM} :=
  ⟨leviApartmentProjection hS i iM j hcomp ζ hj hjc hG hi D₀ x,
    isSpecialPoint_isVertex_leviApartmentProjection hS i iM j hcomp ζ hj hjc hG hi D₀ hder hx,
    isLeviRestriction_leviApartmentProjection hS i iM j hcomp ζ hj hjc hG hi D₀ x⟩

end LocalField
end Langlands.BruhatTits.SpecialCompact
