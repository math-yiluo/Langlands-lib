import Langlands.Geometry.Building.IwasawaDecompositionProof
import Langlands.Geometry.Building.SpecialPointGlobalFixedLocus
import Langlands.Geometry.Building.KPParahoricFixerComparison
import Langlands.Geometry.Building.NormalizerApartmentActionKernel
import Langlands.GroupScheme.Rational.RelativeTitsSystemProof
import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial

/-! # Relative Weyl representatives in a special-point parahoric

Shared special-point argument for the available Iwasawa and Cartan decompositions.
-/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.BruhatTits.SpecialCompact.WeylRepresentatives

private theorem linear_reflection_eq_of_ker_eq
    {V A : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
    {Ψ : Set (A →ᵃ[ℝ] ℝ)}
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero Ψ)
    {ψ φ : A →ᵃ[ℝ] ℝ} {v w : V}
    (hv : AffineRootSystem.IsCoroot Ψ ψ v)
    (hw : AffineRootSystem.IsCoroot Ψ φ w)
    (hker : LinearMap.ker ψ.linear = LinearMap.ker φ.linear) :
    (AffineRootSystem.affineReflection ψ hv.1).linear =
      (AffineRootSystem.affineReflection φ hw.1).linear := by
  let c : ℝ := φ.linear v / 2
  have hc : φ.linear = c • ψ.linear := by
    ext z
    have hz : ψ.linear (z - (ψ.linear z / 2) • v) = 0 := by
      simp only [map_sub, map_smul, hv.1, smul_eq_mul]
      ring
    have hz' : φ.linear (z - (ψ.linear z / 2) • v) = 0 :=
      LinearMap.mem_ker.mp (hker ▸ LinearMap.mem_ker.mpr hz)
    simp only [map_sub, map_smul, smul_eq_mul] at hz'
    change φ.linear z = c * ψ.linear z
    dsimp [c]
    linarith
  have hcw : ψ.linear (c • w) = 2 := by
    have h := hw.1
    rw [hc, LinearMap.smul_apply] at h
    simpa only [map_smul, smul_eq_mul] using h
  have hmaps : ∀ (f : A →ᵃ[ℝ] ℝ) (z : V),
      AffineRootSystem.IsCoroot Ψ f z →
      Set.MapsTo (Module.preReflection f.linear (Module.Dual.eval ℝ V z))
        (AffineRootSystem.derivativeRoots Ψ) (AffineRootSystem.derivativeRoots Ψ) := by
    rintro f z hz _ ⟨a, ha, rfl⟩
    exact ⟨a - a.linear z • f, hz.2 a ha, by simp [Module.preReflection_apply]⟩
  have hmaps' : Set.MapsTo
      (Module.preReflection ψ.linear (Module.Dual.eval ℝ V (c • w)))
      (AffineRootSystem.derivativeRoots Ψ) (AffineRootSystem.derivativeRoots Ψ) := by
    intro a ha
    have h := hmaps φ w hw ha
    convert h using 1
    simp [Module.preReflection_apply, hc, map_smul, smul_smul, mul_comm]
  have heq : v = c • w := Module.eval_apply_injective ℝ
    (Module.Dual.eq_of_preReflection_mapsTo hΨ.finite_derivativeRoots
      hΨ.span_derivativeRoots_eq_top (by simpa using hv.1) (hmaps ψ v hv)
      (by simpa using hcw) hmaps')
  apply LinearEquiv.ext
  intro z
  simp only [AffineRootSystem.affineReflection_linear, Module.reflection_apply, hc, heq,
    LinearMap.smul_apply, smul_smul]
  congr 1
  module

section Datum
variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ParahoricBuildingData G)

private theorem exists_parahoric_reflection
    (hA : B.SatisfiesApartmentAxioms)
    (hgen : B.HasZeroFixerGenerators)
    (hF : RelativeRoot.HasRankOneFactorization B.i)
    {x : B.Apartment} {ψ : B.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ B.affineRoots) (hx : ψ x = 0) :
    ∃ (n : normalizerPoints B.i) (v : TranslationSpace B.i)
      (hv : AffineRootSystem.IsCoroot B.affineRoots ψ v),
      (n : rationalPoints G) ∈ B.parahoricAt x ∧
      B.apartment.normalizerAffineEquiv n = AffineRootSystem.affineReflection ψ hv.1 := by
  have hext := B.apartment.affineRoots_subset_extendedAffineRoots hψ
  rw [← B.reflectionAffineRoots_eq] at hext
  obtain ⟨a, g, hg, hg1, rfl⟩ := hext
  obtain ⟨p, hp⟩ := (hF a a.property g hg hg1).1.exists
  let n := B.reflectionElement hp
  have hv := B.isCoroot_reflectionCoroot hA hg hg1 hp
  refine ⟨n, B.reflectionCoroot hg hg1 hp, hv, ?_,
    B.normalizerAffineEquiv_reflectionElement hg hg1 hp⟩
  apply hgen.zeroFixer_le_parahoric (Set.singleton_nonempty x)
    (fun f => by simpa only [Set.image_singleton] using (bddAbove_singleton : BddAbove ({f x} : Set ℝ)))
  apply B.mem_zeroFixer.mpr
  refine ⟨B.zeroDatum.simplyConnectedImage_le_zeroSubgroup
    (B.reflectionElement_mem_simplyConnectedImage hA hg hg1 hp), ?_⟩
  intro y hy
  have hyx := Set.mem_singleton_iff.mp hy
  subst y
  rw [B.normalizer_smul_apartmentMap]
  change B.apartmentMap (B.apartment.normalizerAffineEquiv n x) = B.apartmentMap x
  have hact : B.apartment.normalizerAffineEquiv n =
      AffineRootSystem.affineReflection (B.reflectionFunctional a g) hv.1 :=
    B.normalizerAffineEquiv_reflectionElement hg hg1 hp
  exact congrArg B.apartmentMap ((congrArg (fun e : B.Apartment ≃ᵃ[ℝ] B.Apartment => e x)
    hact).trans (AffineRootSystem.affineReflection_apply_of_mem _ _ hx))

private theorem quotient_eq_of_translationAction_eq
    (m n : normalizerPoints B.i)
    (h : translationAction B.i m = translationAction B.i n) :
    (QuotientGroup.mk m : relativeWeylGroup B.i) = QuotientGroup.mk n := by
  apply QuotientGroup.eq.mpr
  change (m⁻¹ * n : normalizerPoints B.i).val ∈ centralizerPoints B.i
  apply (B.toValuationBuildingData.translationAction_eq_one_iff_mem_centralizerPoints _).mp
  rw [map_mul, map_inv, h, inv_mul_cancel]

set_option maxHeartbeats 1000000 in
theorem special_parahoric_normalizer_surjective
    (hA : B.SatisfiesApartmentAxioms)
    (hgen : B.HasZeroFixerGenerators)
    (hF : RelativeRoot.HasRankOneFactorization B.i)
    (ν : cocharacterLattice B.S) (hν : IsGenericCocharacter B.i ν)
    {x : B.Apartment} (hx : AffineRootSystem.IsSpecialPoint B.affineRoots x) :
    ∀ w : relativeWeylGroup B.i, ∃ n : normalizerPoints B.i,
      (n : rationalPoints G) ∈ B.parahoricAt x ∧ QuotientGroup.mk n = w := by
  have hT := B.isMaximalSplitTorus.isSplitSubtorus.1
  have hroot := relativeRootSystem F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus
  have hTits := relativeTitsSystem F G B.isConnectedReductive B.S B.i
    B.isMaximalSplitTorus ν hν
  let π := QuotientGroup.mk' ((centralizerPoints B.i).subgroupOf (normalizerPoints B.i))
  let K := (B.parahoricAt x).subgroupOf (normalizerPoints B.i)
  have htop : K.map π = ⊤ := by
    apply top_unique
    rw [← hTits.isTitsSystem.closure_eq]
    apply (Subgroup.closure_le _).2
    rintro w ⟨a, ha, haw⟩
    have har := (simpleRelativeRoots_subset_positive B.i ν ha).1
    have hder : rootForm B.i ⟨a, har⟩ ∈ AffineRootSystem.derivativeRoots B.affineRoots := by
      rw [hA.derivativeRoots_affineRoots]
      exact Set.mem_range_self _
    obtain ⟨ψ, hψ, hlin⟩ := hder
    obtain ⟨φ, hφ, hker⟩ := (AffineRootSystem.isSpecialPoint_iff_ker
      hA.isAffineRootSystem_affineRoots.linear_ne_zero x).mp hx ψ hψ
    have : Smooth G.X.hom := B.isConnectedReductive.smooth
    obtain ⟨g, hg, hg1⟩ := RelativeRoot.exists_rootPoint_actual hT B.i har
    obtain ⟨p, hp⟩ := (hF a har g hg hg1).1.exists
    let m := B.reflectionElement (α := ⟨a, har⟩) hp
    have hmw : (QuotientGroup.mk m : relativeWeylGroup B.i) = w :=
      hroot.eq_of_isRelativeReflection
        (hp.isRelativeReflection B.i hT har hg hg1) haw
    obtain ⟨n, v, hv, hn, hact⟩ :=
      exists_parahoric_reflection B hA hgen hF hφ.1 hφ.2
    have hlinear : translationAction B.i m = translationAction B.i n := by
      have hmcoroot := B.isCoroot_reflectionCoroot (α := ⟨a, har⟩) hA hg hg1 hp
      have hker' : LinearMap.ker (B.reflectionFunctional ⟨a, har⟩ g).linear =
          LinearMap.ker φ.linear := by
        simpa only [B.reflectionFunctional_linear, hlin] using hker
      have heq := linear_reflection_eq_of_ker_eq hA.isAffineRootSystem_affineRoots
        hmcoroot hv hker'
      have hmact : B.apartment.normalizerAffineEquiv m =
          AffineRootSystem.affineReflection (B.reflectionFunctional ⟨a, har⟩ g)
            hmcoroot.1 := B.normalizerAffineEquiv_reflectionElement (α := ⟨a, har⟩) hg hg1 hp
      exact (congrArg (fun e : B.Apartment ≃ᵃ[ℝ] B.Apartment => e.linear) hmact).trans
        (heq.trans (congrArg (fun e : B.Apartment ≃ᵃ[ℝ] B.Apartment => e.linear) hact).symm)
    exact ⟨n, hn, (quotient_eq_of_translationAction_eq B m n hlinear).symm.trans hmw⟩
  intro w
  have hw : w ∈ K.map π := htop ▸ Subgroup.mem_top w
  exact hw

end Datum

end Langlands.BruhatTits.SpecialCompact.WeylRepresentatives
