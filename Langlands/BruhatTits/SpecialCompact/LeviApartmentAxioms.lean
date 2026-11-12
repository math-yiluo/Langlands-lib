import Langlands.BruhatTits.SpecialCompact.LeviAffineRoots
import Langlands.Geometry.Building.AffineRootSystemPullback
import Langlands.Geometry.Building.KPApartmentAxioms
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedTransport
import Langlands.Geometry.Building.AffineExtendedWeylTransport

/-!
# V 7 and AS 2–AS 4 for the restriction of an apartment class to a Levi subgroup

Let `j : M → G` represent the centralizer of the cocharacter `ζ` of the split torus `S`, with
`i = iM ≫ j`, and let `DM` be the restriction of the apartment class `D` of `(G, S)` to `M`
(`leviRestrictedApartmentData`), with the surjective affine projection `π` from the apartment
of `D` onto the apartment of `DM`. An affine functional `ψ` on the apartment of `DM` is an
(extended) affine root of `DM` exactly when `ψ ∘ π` is an (extended) affine root of `D`
(KP §6.7.2). From this criterion, AS 2, AS 3 and AS 4 pass from `D` to `DM`. V 7 passes
because `M(F)` carries the subspace topology of `G(F)` and the filtrations of `DM` are the
preimages of those of `D`.
-/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry TensorProduct Topology
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.GroupScheme.RealTorusSpace
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

section General

variable {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {M : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom M.X.hom] (iM : S.toGrp ⟶ M)

/-- A vector of the Levi translation space on which every root form vanishes is zero. -/
theorem eq_zero_of_forall_rootForm_eq_zero (v : TranslationSpace iM)
    (h : ∀ f ∈ Set.range (rootForm iM), f v = 0) : v = 0 := by
  induction v using Submodule.Quotient.induction_on with
  | _ w =>
    refine (Submodule.Quotient.mk_eq_zero _).2 (mem_rootAnnihilator.2 fun a ha => ?_)
    simpa only [rootForm_mk] using h _ ⟨⟨a, ha⟩, rfl⟩

end General

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
local notation "P" => leviTranslationProjection i iM j hcomp ζ hj

omit [ConnectedSpace G.X.left] [Mono i.hom.hom.left] [Mono iM.hom.hom.left] in
include hcomp hj in
/-- The real cocharacter `1 ⊗ ζ` lies in the Levi root annihilator. -/
theorem tmul_mem_rootAnnihilator_levi : ((1 : ℝ) ⊗ₜ[ℤ] ζ : V S) ∈ rootAnnihilator iM := by
  have hroots := relativeRoots_centralizer_factor dynamicLie i iM j hcomp ζ hj
  refine mem_rootAnnihilator.2 fun a ha => ?_
  rw [hroots] at ha
  rw [eval_tmul, ha.2]
  simp

/-- Precomposition with the Levi translation projection is injective on linear forms. -/
theorem leviTranslationProjection_comp_injective :
    Function.Injective fun f : Module.Dual ℝ (TranslationSpace iM) => f.comp P := by
  intro f g hfg
  refine LinearMap.ext fun v => ?_
  obtain ⟨w, rfl⟩ := leviTranslationProjection_surjective i iM j hcomp ζ hj v
  exact LinearMap.congr_fun hfg w

include j hcomp ζ hj in
/-- The Levi root forms are finite when the ambient root forms are. -/
theorem finite_range_rootForm_levi (hfin : (Set.range (rootForm i)).Finite) :
    (Set.range (rootForm iM)).Finite := by
  refine Set.Finite.of_finite_image (f := fun f : Module.Dual ℝ (TranslationSpace iM) =>
    f.comp P) (hfin.subset ?_)
    (leviTranslationProjection_comp_injective i iM j hcomp ζ hj).injOn
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  exact ⟨_, (rootForm_comp_leviTranslationProjection i iM j hcomp ζ hj a).symm⟩

/-- An affine functional on the Levi apartment whose pullback has the derivative of an ambient
root `α` has the derivative of the same root, which is then a Levi root: its pairing with `ζ`
vanishes because `1 ⊗ ζ` projects to zero. -/
theorem exists_leviRoot_of_comp_linear (ψ : (DM).Apartment →ᵃ[ℝ] ℝ) (α : relativeRoots i)
    (hψ : (ψ.comp π).linear = rootForm i α) :
    ∃ a : relativeRoots iM, a.val = α.val ∧ ψ.linear = rootForm iM a := by
  have hroots := relativeRoots_centralizer_factor dynamicLie i iM j hcomp ζ hj
  have hz : latticePairing S α.val ζ = 0 := by
    have h0 := LinearMap.congr_fun hψ (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] ζ))
    have hP : P (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] ζ)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (tmul_mem_rootAnnihilator_levi i iM j hcomp ζ hj)
    change ψ.linear (P _) = _ at h0
    rw [hP, map_zero, rootForm_mk, eval_tmul, one_mul] at h0
    exact_mod_cast h0.symm
  have haM : α.val ∈ relativeRoots iM := hroots.symm ▸ ⟨α.property, hz⟩
  refine ⟨⟨α.val, haM⟩, rfl, ?_⟩
  apply leviTranslationProjection_comp_injective i iM j hcomp ζ hj
  change ψ.linear.comp P = (rootForm iM ⟨α.val, haM⟩).comp P
  rw [rootForm_comp_leviTranslationProjection]
  exact hψ

/-- An affine functional is an affine root of the restricted class exactly when its pullback is
an affine root of the ambient class. -/
theorem mem_affineRoots_levi_iff (ψ : (DM).Apartment →ᵃ[ℝ] ℝ) :
    ψ ∈ (DM).affineRoots ↔ ψ.comp π ∈ D.affineRoots := by
  refine ⟨fun h => leviAffineRootPullback_mem_affineRoots hS i iM j hcomp ζ hj hjc hG hi D h, ?_⟩
  rintro ⟨α, hlin, hnot⟩
  obtain ⟨a, ha, hψ⟩ :=
    exists_leviRoot_of_comp_linear hS i iM j hcomp ζ hj hjc hG hi D ψ α hlin
  refine ⟨a, hψ, fun h => hnot ?_⟩
  rw [← ha]
  exact (leviAffineRootGroup_subset_mul_iff hS i iM j hcomp ζ hj hjc hG hi D a ψ hψ).1 h

/-- An affine functional is an extended affine root of the restricted class exactly when its
pullback is an extended affine root of the ambient class. -/
theorem mem_extendedAffineRoots_levi_iff (ψ : (DM).Apartment →ᵃ[ℝ] ℝ) :
    ψ ∈ (DM).extendedAffineRoots ↔ ψ.comp π ∈ D.extendedAffineRoots := by
  refine ⟨fun h =>
    leviAffineRootPullback_mem_extendedAffineRoots hS i iM j hcomp ζ hj hjc hG hi D h, ?_⟩
  rintro ⟨α, hlin, hne⟩
  obtain ⟨a, ha, hψ⟩ :=
    exists_leviRoot_of_comp_linear hS i iM j hcomp ζ hj hjc hG hi D ψ α hlin
  refine ⟨a, hψ, fun heq => hne ?_⟩
  have h1 := map_leviAffineRootGroup hS i iM j hcomp ζ hj hjc hG hi D a ψ hψ
  have h2 := map_leviAffineRootGroupPlus hS i iM j hcomp ζ hj hjc hG hi D a ψ hψ
  rw [heq] at h2
  rw [← ha]
  exact h2.symm.trans h1

/-- AS 2/AS 3 pass to the restricted class: if `Ψ` is an affine root system with derivative the
ambient roots and `ΨM` is detected by pullback to `Ψ` and has root-form derivatives, then `ΨM`
is an affine root system with derivative the Levi roots. -/
theorem isAffineRootSystem_levi {Ψ : Set (D.Apartment →ᵃ[ℝ] ℝ)}
    {ΨM : Set ((DM).Apartment →ᵃ[ℝ] ℝ)}
    (hmem : ∀ ψ : (DM).Apartment →ᵃ[ℝ] ℝ, ψ ∈ ΨM ↔ ψ.comp π ∈ Ψ)
    (hlin : ∀ ψ ∈ ΨM, ∃ a : relativeRoots iM, ψ.linear = rootForm iM a)
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero Ψ)
    (hder : AffineRootSystem.derivativeRoots Ψ = Set.range (rootForm i)) :
    AffineRootSystem.IsAffineRootSystemWithRankZero ΨM ∧
      AffineRootSystem.derivativeRoots ΨM = Set.range (rootForm iM) := by
  have hderM : AffineRootSystem.derivativeRoots ΨM = Set.range (rootForm iM) := by
    refine AffineRootSystem.derivativeRoots_eq_of_comp hmem ?_ ?_
    · rintro _ ⟨ψ, hψ, rfl⟩
      obtain ⟨a, ha⟩ := hlin ψ hψ
      exact ⟨a, ha.symm⟩
    · rintro _ ⟨a, rfl⟩
      rw [hder]
      exact ⟨_, (rootForm_comp_leviTranslationProjection i iM j hcomp ζ hj a).symm⟩
  have hfin : (Set.range (rootForm i)).Finite := hder ▸ hΨ.finite_derivativeRoots
  refine ⟨AffineRootSystem.isAffineRootSystemWithRankZero_of_comp
    (leviApartmentAffineProjection_surjective hS i iM j hcomp ζ hj hjc hG hi D) hΨ hmem ?_,
    hderM⟩
  rw [hderM]
  exact AffineRootSystem.span_eq_top_of_finite_of_forall_eq_zero
    (finite_range_rootForm_levi i iM j hcomp ζ hj hfin) (eq_zero_of_forall_rootForm_eq_zero iM)

/-- AS 4 passes to the restricted class. -/
theorem mem_or_two_smul_mem_levi
    (h4 : ∀ ψ ∈ D.extendedAffineRoots, ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots) :
    ∀ ψ ∈ (DM).extendedAffineRoots, ψ ∈ (DM).affineRoots ∨ (2 : ℝ) • ψ ∈ (DM).affineRoots := by
  intro ψ hψ
  rw [mem_affineRoots_levi_iff, mem_affineRoots_levi_iff, AffineRootSystem.smul_comp']
  exact h4 _ ((mem_extendedAffineRoots_levi_iff hS i iM j hcomp ζ hj hjc hG hi D ψ).1 hψ)

/-! ### AS 5 when the Levi has the same roots -/

/-- The projection intertwines the normalizer of `S` in `M` with its image in `G`. -/
theorem leviApartmentProjection_smul (n : normalizerPoints iM) (x : D.Apartment) :
    π (normalizerPointsMap iM j i hcomp n • x) = n • π x := by
  apply KPApartmentData.Apartment.ext
  exact leviRestrictedRootFunctionFamily_smul iM j hS i hcomp ζ hj hjc x.val n

omit [Smooth G.X.hom] [ConnectedSpace G.X.left] [LocallyOfFiniteType M.X.hom]
  [Mono i.hom.hom.left] [Mono iM.hom.hom.left] in
/-- If the Levi has the same roots as `G`, it has the same root annihilator. -/
theorem rootAnnihilator_levi_eq (hR : relativeRoots iM = relativeRoots i) :
    rootAnnihilator iM = rootAnnihilator i := by
  ext v
  rw [Geometry.Building.mem_rootAnnihilator, Geometry.Building.mem_rootAnnihilator, hR]

/-- If the Levi has the same roots as `G`, the projection of apartments is bijective. -/
theorem leviApartmentAffineProjection_bijective (hR : relativeRoots iM = relativeRoots i) :
    Function.Bijective π := by
  refine ⟨fun x y hxy => ?_,
    leviApartmentAffineProjection_surjective hS i iM j hcomp ζ hj hjc hG hi D⟩
  have h := (leviApartmentProjection_eq_iff hS i iM j hcomp ζ hj hjc hG hi D x y).1 hxy
  rw [rootAnnihilator_levi_eq i iM hR, Submodule.mkQ_map_self, Submodule.mem_bot,
    vsub_eq_zero_iff_eq] at h
  exact h

/-- Along a bijective projection, a set of affine functionals detected by pullback is the
transport of the ambient set. -/
theorem transportedRoots_levi (hbij : Function.Bijective π) {Ψ : Set (D.Apartment →ᵃ[ℝ] ℝ)}
    {ΨM : Set ((DM).Apartment →ᵃ[ℝ] ℝ)}
    (hmem : ∀ ψ : (DM).Apartment →ᵃ[ℝ] ℝ, ψ ∈ ΨM ↔ ψ.comp π ∈ Ψ) :
    AffineRootSystem.transportedRoots (AffineEquiv.ofBijective hbij) Ψ = ΨM := by
  ext ψ
  have hψ : ψ = AffineRootSystem.affineFunctionalTransport (AffineEquiv.ofBijective hbij)
      (ψ.comp π) := by
    refine AffineMap.ext fun x => ?_
    rw [AffineRootSystem.affineFunctionalTransport_apply, AffineMap.comp_apply,
      ← AffineEquiv.ofBijective_apply hbij, AffineEquiv.apply_symm_apply]
  conv_lhs => rw [hψ]
  rw [AffineRootSystem.affineFunctionalTransport_mem_transportedRoots_iff, hmem]

/-- Along a bijective projection, the action of `n ∈ N_M(F)` on the Levi apartment is the
conjugate of the action of its image in `N_G(F)`. -/
theorem affineConjugation_normalizerAffineEquiv_levi (hbij : Function.Bijective π)
    (n : normalizerPoints iM) :
    AffineRootSystem.affineConjugation (AffineEquiv.ofBijective hbij)
        (D.normalizerAffineEquiv (normalizerPointsMap iM j i hcomp n)) =
      (DM).normalizerAffineEquiv n := by
  refine AffineEquiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := hbij.2 x
  rw [AffineRootSystem.affineConjugation_apply, ← AffineEquiv.ofBijective_apply hbij,
    AffineEquiv.symm_apply_apply, KPApartmentData.normalizerAffineEquiv_apply,
    KPApartmentData.normalizerAffineEquiv_apply, AffineEquiv.ofBijective_apply]
  exact leviApartmentProjection_smul hS i iM j hcomp ζ hj hjc hG hi D n y

/-- AS 5, second sentence, passes to a Levi with the same roots: the image of `N_M(F)` lies in
the conjugate of the image of `N_G(F)`. -/
theorem range_eq_affineWeylGroup_levi (hR : relativeRoots iM = relativeRoots i)
    (hrange : D.normalizerAffineEquiv.range = AffineRootSystem.affineWeylGroup D.affineRoots)
    (hle : AffineRootSystem.affineWeylGroup (DM).affineRoots ≤
      (DM).normalizerAffineEquiv.range) :
    (DM).normalizerAffineEquiv.range = AffineRootSystem.affineWeylGroup (DM).affineRoots := by
  have hbij := leviApartmentAffineProjection_bijective hS i iM j hcomp ζ hj hjc hG hi D hR
  have htr := transportedRoots_levi hS i iM j hcomp ζ hj hjc hG hi D hbij
    (mem_affineRoots_levi_iff hS i iM j hcomp ζ hj hjc hG hi D)
  refine le_antisymm ?_ hle
  rintro _ ⟨n, rfl⟩
  rw [← affineConjugation_normalizerAffineEquiv_levi hS i iM j hcomp ζ hj hjc hG hi D hbij n,
    ← AffineRootSystem.map_affineWeylGroup_of_transportedRoots_eq _ htr, ← hrange]
  exact Subgroup.mem_map_of_mem _ ⟨_, rfl⟩

omit [IsAffineHom G.X.hom] [IsAffineHom M.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
  [LocallyOfFiniteType M.X.hom] [Mono i.hom.hom.left] [Mono iM.hom.hom.left] in
include hcomp in
/-- If `j` is an isomorphism, every normalizing point of `G` comes from one of `M`. -/
theorem normalizerPointsMap_surjective_of_isIso [IsIso j] :
    Function.Surjective (normalizerPointsMap iM j i hcomp) := by
  have hinv : i ≫ inv j = iM := by
    rw [← hcomp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hcancel : (inv j).hom.hom ≫ j.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, IsIso.inv_hom_id]
    rfl
  rintro ⟨n, σ, hσ⟩
  refine ⟨⟨n ≫ (inv j).hom.hom, σ, hinv ▸ hσ.comp (inv j)⟩, Subtype.ext ?_⟩
  rw [normalizerPointsMap_val, Category.assoc, hcancel, Category.comp_id]

/-- AS 5, third sentence, passes to a Levi with the same roots whose inclusion is an
isomorphism: every element of `W(Ψ_M)ᵉˣᵗ` is the conjugate of the image of a point of
`N_G(F) = j(N_M(F))`. -/
theorem range_eq_extendedAffineWeylGroup_levi [IsIso j]
    (hR : relativeRoots iM = relativeRoots i)
    (hrange : D.normalizerAffineEquiv.range =
      AffineRootSystem.extendedAffineWeylGroup D.affineRoots)
    (hle : (DM).normalizerAffineEquiv.range ≤
      AffineRootSystem.extendedAffineWeylGroup (DM).affineRoots) :
    (DM).normalizerAffineEquiv.range =
      AffineRootSystem.extendedAffineWeylGroup (DM).affineRoots := by
  have hbij := leviApartmentAffineProjection_bijective hS i iM j hcomp ζ hj hjc hG hi D hR
  have htr := transportedRoots_levi hS i iM j hcomp ζ hj hjc hG hi D hbij
    (mem_affineRoots_levi_iff hS i iM j hcomp ζ hj hjc hG hi D)
  refine le_antisymm hle fun e he => ?_
  rw [← htr, ← AffineRootSystem.map_extendedAffineWeylGroup, ← hrange] at he
  obtain ⟨_, ⟨n', rfl⟩, rfl⟩ := he
  obtain ⟨n, rfl⟩ := normalizerPointsMap_surjective_of_isIso i iM j hcomp n'
  exact ⟨n, (affineConjugation_normalizerAffineEquiv_levi hS i iM j hcomp ζ hj hjc hG hi D
    hbij n).symm⟩

section Topology

variable [ValuativeRel F] [TopologicalSpace F]

omit [Mono i.hom.hom.left] [Mono iM.hom.hom.left] in
include hS hcomp hj hjc in
/-- V 7 passes from a valuation to its restriction: `M(F)` has the subspace topology of `G(F)`,
the root groups correspond homeomorphically and the filtrations are preimages. -/
theorem leviRestricted_isTopologyCompatible {φ : RootFunctionFamily S G}
    (hφ : Geometry.Building.IsTopologyCompatible i φ) :
    Geometry.Building.IsTopologyCompatible iM (leviRestrictedRootFunctionFamily iM j φ) := by
  have hroots := relativeRoots_centralizer_factor dynamicLie i iM j hcomp ζ hj
  unfold Geometry.Building.IsTopologyCompatible at hφ ⊢
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
  have : IsClosedImmersion j.hom.hom.left := hjc
  have hemb : IsEmbedding (rationalPoints.map j) := isEmbedding_rationalPointMap F j.hom.hom
  intro a ha
  have haG : a ∈ relativeRoots i := (hroots ▸ ha).1
  obtain ⟨hb, hr⟩ := hφ a haG
  have hmap := map_leviRootGroupPoints hS i iM j hcomp ζ hj hjc a ha
  let h : rootGroupPoints iM a → rootGroupPoints i a := fun m =>
    ⟨rationalPoints.map j m, hmap ▸ Subgroup.mem_map_of_mem _ m.2⟩
  have hcomm : ((↑) : rootGroupPoints i a → rationalPoints G) ∘ h =
      rationalPoints.map j ∘ ((↑) : rootGroupPoints iM a → rationalPoints M) := rfl
  have hsubM : IsInducing ((↑) : rootGroupPoints iM a → rationalPoints M) :=
    IsInducing.subtypeVal
  have hsubG : IsInducing ((↑) : rootGroupPoints i a → rationalPoints G) :=
    IsInducing.subtypeVal
  have hind : IsInducing h := by
    have := hemb.isInducing.comp hsubM
    rw [← hcomm] at this
    exact hsubG.of_comp_iff.1 this
  have h1 : h 1 = 1 := Subtype.ext (map_one _)
  have hpre : ∀ r : ℝ, ((↑) : rootGroupPoints iM a → rationalPoints M) ⁻¹'
        rootFiltration iM (leviRestrictedRootFunctionFamily iM j φ) a r =
      h ⁻¹' (((↑) : rootGroupPoints i a → rationalPoints G) ⁻¹' rootFiltration i φ a r) := by
    intro r
    rw [leviRestrictedRootFiltration_eq_comap iM j hS i hcomp ζ hj hjc φ a ha r]
    rfl
  refine ⟨?_, fun r => ⟨?_, ?_⟩⟩
  · rw [hind.nhds_eq_comap, h1]
    simpa only [hpre] using hb.comap h
  · rw [hpre]
    exact (hr r).1.preimage hind.continuous
  · apply isAlgebraicallyBounded_of_closedImmersion F j.hom.hom
    have himg : (fun p : RationalPoint F M.X => p ≫ j.hom.hom) ''
        rootFiltration iM (leviRestrictedRootFunctionFamily iM j φ) a r =
          rootFiltration i φ a r :=
      image_leviRestrictedRootFiltration iM j hS i hcomp ζ hj hjc φ a ha r
    rw [himg]
    exact (hr r).2

/-- V 7 passes from the ambient class to the restricted class. -/
theorem isTopologyCompatible_levi (hD : D.IsTopologyCompatible) : (DM).IsTopologyCompatible := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact leviRestricted_isTopologyCompatible hS i iM j hcomp ζ hj hjc (hD φ hφ)

end Topology

end Langlands.BruhatTits.SpecialCompact
