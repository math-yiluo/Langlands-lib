import Langlands.Geometry.Building.UnramifiedOneFixerClosureStatement
import Langlands.Geometry.Building.RootFixerDepthClosure
import Langlands.Geometry.Building.ApartmentFacetVertexInvariance
import Langlands.Geometry.Building.GenericApartmentInjection
import Langlands.Geometry.Building.AffineBoundedFacetFiniteness
import Langlands.Geometry.Building.IntegerValuationAffineWeylProof
import Langlands.Geometry.Building.MaximalUnramifiedUniformizer

/-! # Pointwise fixers extend to affine topological closures -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

private theorem continuous_affineFunctional (f : D.Apartment →ᵃ[ℝ] ℝ) :
    @Continuous D.Apartment ℝ D.affineFunctionalTopology inferInstance f :=
  continuous_iff_le_induced.mpr (iInf_le _ f)

private theorem isClosed_weakSignRegion (c : ℝ) :
    IsClosed {t : ℝ | SignType.sign t = 0 ∨ SignType.sign t = SignType.sign c} := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have heq : {t : ℝ | SignType.sign t = 0 ∨
        SignType.sign t = SignType.sign c} = Set.Iic 0 := by
      ext t
      simp only [Set.mem_ofPred_eq, sign_neg hc, sign_eq_zero_iff,
        sign_eq_neg_one_iff, Set.mem_Iic]
      exact ⟨fun h => h.elim le_of_eq le_of_lt, fun h => (lt_or_eq_of_le h).symm⟩
    rw [heq]
    exact isClosed_Iic
  · subst c
    have hclosed : IsClosed {t : ℝ | t = 0} :=
      isClosed_eq continuous_id continuous_const
    simpa only [sign_zero, or_self, sign_eq_zero_iff] using hclosed
  · have heq : {t : ℝ | SignType.sign t = 0 ∨
        SignType.sign t = SignType.sign c} = Set.Ici 0 := by
      ext t
      simp only [Set.mem_ofPred_eq, sign_pos hc, sign_eq_zero_iff,
        sign_eq_one_iff, Set.mem_Ici]
      exact ⟨fun h => h.elim (fun h => le_of_eq h.symm) le_of_lt,
        fun h => (lt_or_eq_of_le h).elim Or.inr (fun h => Or.inl h.symm)⟩
    rw [heq]
    exact isClosed_Ici

/-- A combinatorial closed facet is closed for the initial affine topology. -/
theorem isClosed_facetClosure_affineFunctionalTopology (p : D.Apartment) :
    @IsClosed D.Apartment D.affineFunctionalTopology
      (AffineRootSystem.facetClosure D.affineRoots p) := by
  let := D.affineFunctionalTopology
  have heq : AffineRootSystem.facetClosure D.affineRoots p =
      ⋂ ψ ∈ D.affineRoots, ψ ⁻¹' {t : ℝ |
        SignType.sign t = 0 ∨ SignType.sign t = SignType.sign (ψ p)} := by
    ext x
    simp [AffineRootSystem.facetClosure]
  rw [heq]
  exact isClosed_iInter fun ψ => isClosed_iInter fun _ =>
    (isClosed_weakSignRegion (ψ p)).preimage (D.continuous_affineFunctional ψ)

/-- The fixed points of an affine self-map are closed for the initial affine
topology, using the separating root coordinates of the reduced apartment. -/
theorem isClosed_affineFixedSet (e : D.Apartment →ᵃ[ℝ] D.Apartment) :
    @IsClosed D.Apartment D.affineFunctionalTopology {x | e x = x} := by
  let := D.affineFunctionalTopology
  have heq : {x | e x = x} =
      ⋂ f : D.Apartment →ᵃ[ℝ] ℝ, {x | (f.comp e) x = f x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, AffineMap.comp_apply]
    constructor
    · intro hx f
      rw [hx]
    · intro hx
      apply vsub_eq_zero_iff_eq.mp
      apply eq_zero_of_rootForm_eq_zero i
      intro a
      simpa only [affineFunctional_apply, vsub_self, map_zero, add_zero, zero_add]
        using hx (D.affineFunctional a x 0)
  rw [heq]
  exact isClosed_iInter fun f =>
    isClosed_eq (D.continuous_affineFunctional (f.comp e))
      (D.continuous_affineFunctional f)

/-- Fixation extends to the affine closure of a set meeting finitely many
facets. The comparison with the normalizer is made separately on each facet. -/
theorem smul_apartmentMap_eq_of_mem_affineClosure_of_finite_facets
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    {Ω : Set D.Apartment}
    (hfinite : (AffineRootSystem.facet D.affineRoots '' Ω).Finite)
    {h : rationalPoints G}
    (hfix : ∀ x ∈ Ω, h • D.apartmentMap x = D.apartmentMap x)
    {x : D.Apartment}
    (hx : x ∈ @closure D.Apartment D.affineFunctionalTopology Ω) :
    h • D.apartmentMap x = D.apartmentMap x := by
  classical
  let := D.affineFunctionalTopology
  let R : Set (Set D.Apartment) := AffineRootSystem.facet D.affineRoots '' Ω
  let : Finite R := hfinite.to_subtype
  have hUnion : Ω = ⋃ F : R, Ω ∩ F.val := by
    ext y
    constructor
    · intro hy
      exact Set.mem_iUnion.mpr
        ⟨⟨AffineRootSystem.facet D.affineRoots y, y, hy, rfl⟩,
          hy, AffineRootSystem.mem_facet_self _ _⟩
    · intro hy
      obtain ⟨F, hF⟩ := Set.mem_iUnion.mp hy
      exact hF.1
  rw [hUnion, closure_iUnion_of_finite] at hx
  obtain ⟨F, hxF⟩ := Set.mem_iUnion.mp hx
  obtain ⟨p, hp, hFp⟩ := F.property
  obtain ⟨n, _, hn⟩ :=
    D.exists_normalizer_eq_on_translated_facetClosure hAS4 h (hfix p hp)
  have hsub : Ω ∩ F.val ⊆
      AffineRootSystem.facetClosure D.affineRoots p ∩
        {y | D.normalizerAffineEquiv n y = y} := by
    intro y hy
    have hyF : y ∈ AffineRootSystem.facetClosure D.affineRoots p :=
      AffineRootSystem.facet_subset_facetClosure _ p (hFp ▸ hy.2)
    refine ⟨hyF, ?_⟩
    apply D.apartmentMap_injective hG hi
    exact (hn y hyF).symm.trans (hfix y hy.1)
  have hclosed : IsClosed (AffineRootSystem.facetClosure D.affineRoots p ∩
      {y | D.normalizerAffineEquiv n y = y}) :=
    (D.isClosed_facetClosure_affineFunctionalTopology p).inter
      (D.isClosed_affineFixedSet (D.normalizerAffineEquiv n).toAffineMap)
  obtain ⟨hxFacet, hxFix⟩ := (closure_minimal hsub hclosed) hxF
  exact (hn x hxFacet).trans (congrArg D.apartmentMap hxFix)

end KPApartmentData

private instance unramifiedOneFixerClosureProofAffineHom
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

set_option maxHeartbeats 800000 in
/-- Pointwise fixers in `G(K)^1` of nonempty bounded translated apartment
subsets are unchanged by topological closure, in arbitrary characteristic. -/
theorem unramifiedOneFixerClosure : UnramifiedOneFixerClosureStatement.{u} := by
  intro F _ _ _ _ G _ C g Ω _hne hb
  let : Smooth (baseChanged F (inertiaFixedField F) G).X.hom :=
    C.isConnectedReductive.smooth
  apply le_antisymm
  · intro h hh
    refine ⟨hh.1, ?_⟩
    change h ∈ C.apartment.pointwiseFixer _
    apply C.apartment.mem_pointwiseFixer.mpr
    rintro _ ⟨x, hx, rfl⟩
    have hfix : ∀ y ∈ Ω,
        (g⁻¹ * h * g) • C.apartmentMap y = C.apartmentMap y := by
      intro y hy
      have hhy := C.apartment.mem_pointwiseFixer.mp hh.2 _ ⟨y, hy, rfl⟩
      rw [mul_smul, mul_smul, hhy, inv_smul_smul]
    have hΨ := C.isAffineRootSystemWithRankZero_affineRoots
      (MaximalUnramified.exists_order_eq_one F)
    have heq := C.apartment.smul_apartmentMap_eq_of_mem_affineClosure_of_finite_facets
      C.isConnectedReductive C.isMaximalSplitTorus
      (fun _ hψ => C.apartment.mem_or_two_smul_mem_affineRoots_of_oppositePairs
        C.isMaximalSplitTorus.isSplitSubtorus.1 C.hasOppositeFactorPairs hψ)
      (hΨ.finite_facets_meeting hb) hfix hx
    have heq' := congrArg (g • ·) heq
    simpa only [mul_smul, smul_inv_smul] using heq'
  · exact characterValuationKernel_inf_pointwiseFixer_closure_le C g Ω

end Langlands.Geometry.Building
