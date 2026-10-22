import Langlands.Galois.Local.SpectralStatement
import Mathlib.FieldTheory.PrimitiveElement

noncomputable section

open Polynomial IsLocalRing
open scoped NNReal

namespace Langlands.LocalGalois

theorem residue_isAlgClosed {L : Type*} [Field L] [IsAlgClosed L]
    (A : ValuationSubring L) : IsAlgClosed (ResidueField A) := by
  apply IsAlgClosed.of_exists_root
  intro f hf hirr
  obtain ⟨g, hg, hdeg, hmonic⟩ :=
    lifts_and_degree_eq_and_monic
      (mem_lifts_of_surjective (residue_surjective (R := A)) f) hf
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (g.map (algebraMap A L)) (by
    rw [degree_map_eq_of_injective (IsFractionRing.injective A L), hdeg]
    exact ne_of_gt hirr.degree_pos)
  have hi : IsIntegral A x := ⟨g, hmonic, by simpa only [IsRoot, eval_map, aeval_def] using hx⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
  have hy : g.eval y = 0 := by
    apply IsFractionRing.injective A L
    simpa only [map_zero, IsRoot, eval_map, eval₂_at_apply] using hx
  refine ⟨residue A y, ?_⟩
  rw [← hg, eval_map, eval₂_at_apply, hy, map_zero]

section Spectral

variable (K L : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

theorem spectral_integral (x : extensionIntegers K L) : IsIntegral (baseIntegers K) (x : L) := by
  have hm := minpoly.monic (Algebra.IsIntegral.isIntegral (x : L) (R := K))
  have hcoeff : ∀ n, ‖(minpoly K (x : L)).coeff n‖ ≤ 1 :=
    (spectralValue_le_one_iff hm).mp x.property
  have hlift : minpoly K (x : L) ∈ lifts (algebraMap (baseIntegers K) K) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hcoeff n⟩, rfl⟩
  obtain ⟨g, hg, -, hmonic⟩ := lifts_and_degree_eq_and_monic hlift hm
  refine ⟨g, hmonic, ?_⟩
  have h := minpoly.aeval K (x : L)
  rw [← hg, aeval_map_algebraMap] at h
  exact h

instance spectralIntegers_isIntegral :
    Algebra.IsIntegral (baseIntegers K) (extensionIntegers K L) where
  isIntegral x :=
    (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom (baseIntegers K) (extensionIntegers K L) L)
      (IsFractionRing.injective (extensionIntegers K L) L)).mp (spectral_integral K L x)

theorem integral_iff_mem_spectralIntegers (x : L) :
    IsIntegral (baseIntegers K) x ↔ x ∈ extensionIntegers K L := by
  refine ⟨fun hx => ?_, fun hx => spectral_integral K L ⟨x, hx⟩⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (hx.tower_top (A := extensionIntegers K L))
  exact hy ▸ y.property

instance residueExtension_isIntegral :
    Algebra.IsIntegral (ResidueField (baseIntegers K))
      (ResidueField (extensionIntegers K L)) where
  isIntegral x := by
    obtain ⟨x, rfl⟩ := residue_surjective x
    exact IsIntegral.map_of_comp_eq (residue (baseIntegers K))
      (residue (extensionIntegers K L)) rfl
      (Algebra.IsIntegral.isIntegral x (R := baseIntegers K))

theorem residueExtension_isAlgClosure [IsAlgClosed L] :
    IsAlgClosure (ResidueField (baseIntegers K))
      (ResidueField (extensionIntegers K L)) where
  isAlgClosed := residue_isAlgClosed _
  isAlgebraic := inferInstance

theorem residueHom_apply (σ : Gal(L/K)) (x : extensionIntegers K L) :
    residueHom K L σ (residue _ x) = residue _ (integerAut K L σ x) := rfl

open scoped Topology in
theorem residueHom_continuous : Continuous (residueHom K L) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨E, hE, hEN⟩ := hN
  let := hE
  let b := Module.finBasis (ResidueField (baseIntegers K)) E
  choose x hx using fun i => residue_surjective ((b i : E) :
    ResidueField (extensionIntegers K L))
  let U : Set Gal(L/K) := ⋂ i, MulAction.stabilizer Gal(L/K) (x i : L)
  have hopen : IsOpen U :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral (x i : L)
  have hone : (1 : Gal(L/K)) ∈ U := by
    simp only [U, Set.mem_iInter, SetLike.mem_coe, Subgroup.one_mem, implies_true]
  apply Filter.mem_of_superset (hopen.mem_nhds hone)
  intro σ hσ
  apply hEN
  change residueHom K L σ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  have hb : ∀ i, residueHom K L σ (b i : ResidueField (extensionIntegers K L)) =
      (b i : ResidueField (extensionIntegers K L)) := by
    intro i
    rw [← hx i, residueHom_apply]
    congr 1
    apply Subtype.ext
    exact (Set.mem_iInter.mp hσ i : σ (x i : L) = (x i : L))
  have heq :
      (residueHom K L σ).toLinearMap.comp E.val.toLinearMap = E.val.toLinearMap :=
    b.ext hb
  intro y hy
  exact LinearMap.congr_fun heq (⟨y, hy⟩ : E)

theorem mem_inertia_iff (σ : Gal(L/K)) :
    σ ∈ inertia K L ↔ ∀ x : extensionIntegers K L,
      residue _ (integerAut K L σ x) = residue _ x := by
  change residueHom K L σ = 1 ↔ _
  constructor
  · intro h x
    exact congrArg (fun τ => τ (residue _ x)) h
  · intro h
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    exact h x

theorem inertia_isClosed : IsClosed (inertia K L : Set Gal(L/K)) :=
  isClosed_eq (residueHom_continuous K L) continuous_const

theorem inertia_eq_comap_valuationSubring :
    inertia K L = ((extensionIntegers K L).inertiaSubgroup K).comap
      (decompositionHom K L) := by
  ext σ
  rw [mem_inertia_iff]
  change (∀ x : extensionIntegers K L,
      residue _ (integerAut K L σ x) = residue _ x) ↔
    MulSemiringAction.toRingAut _ (ResidueField (extensionIntegers K L))
      (decompositionHom K L σ) = 1
  constructor
  · intro h
    apply RingEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    exact h x
  · intro h x
    exact congrArg (fun τ => τ (residue _ x)) h

end Spectral

section Normal

variable (K L : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Field L] [Algebra K L] [Normal K L]

theorem residueHom_lift_single
    (τ : Gal(ResidueField (extensionIntegers K L)/ResidueField (baseIntegers K)))
    (y : ResidueField (extensionIntegers K L)) :
    ∃ σ : Gal(L/K), residueHom K L σ y = τ y := by
  let A := baseIntegers K
  let B := extensionIntegers K L
  obtain ⟨x, rfl⟩ := residue_surjective y
  have hm := minpoly.monic (Algebra.IsIntegral.isIntegral (x : L) (R := K))
  have hcoeff : ∀ n, ‖(minpoly K (x : L)).coeff n‖ ≤ 1 :=
    (spectralValue_le_one_iff hm).mp x.property
  have hlift : minpoly K (x : L) ∈ lifts (algebraMap A K) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hcoeff n⟩, rfl⟩
  obtain ⟨g, hg, -, hgmonic⟩ := lifts_and_degree_eq_and_monic hlift hm
  let gB := g.map (algebraMap A B)
  have hgL : gB.map (algebraMap B L) =
      (minpoly K (x : L)).map (algebraMap K L) := by
    dsimp only [gB]
    rw [map_map, ← IsScalarTower.algebraMap_eq, ← hg,
      map_map, ← IsScalarTower.algebraMap_eq]
  have hsplit : gB.Splits := by
    apply Splits.of_splits_map_of_injective (IsFractionRing.injective B L)
      (hgL.symm ▸ Normal.splits' (K := L) (F := K) (x : L))
    intro z hz
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    exact ⟨gB, hgmonic.map _, by
      simpa only [IsRoot, eval_map, aeval_def] using
        (mem_roots ((hgmonic.map _).map _).ne_zero).mp hz⟩
  have hxB : aeval x g = 0 := by
    apply IsFractionRing.injective B L
    change (IsScalarTower.toAlgHom A B L) (aeval x g) = (algebraMap B L) 0
    rw [map_zero, ← aeval_algHom_apply (IsScalarTower.toAlgHom A B L)]
    have h := minpoly.aeval K (x : L)
    rw [← hg, aeval_map_algebraMap] at h
    exact h
  have hxres : aeval (residue B x) g = 0 := by
    change aeval ((IsScalarTower.toAlgHom A B (ResidueField B)) x) g = 0
    rw [aeval_algHom_apply (IsScalarTower.toAlgHom A B (ResidueField B)),
      hxB, map_zero]
  have hτroot : aeval (τ (residue B x)) g = 0 := by
    change aeval ((τ.restrictScalars A) (residue B x)) g = 0
    rw [aeval_algHom_apply (τ.restrictScalars A), hxres, map_zero]
  have hgbar : gB.map (residue B) = g.map (algebraMap A (ResidueField B)) := by
    change (g.map (algebraMap A B)).map (algebraMap B (ResidueField B)) = _
    rw [map_map, ← IsScalarTower.algebraMap_eq]
  have hτmem : τ (residue B x) ∈ (gB.map (residue B)).roots := by
    rw [mem_roots ((hgmonic.map _).map _).ne_zero, hgbar]
    simpa only [IsRoot, eval_map, aeval_def] using hτroot
  rw [hsplit.roots_map_of_ne_zero ((hgmonic.map _).map _).ne_zero,
    Multiset.mem_map] at hτmem
  obtain ⟨z, hz, hzy⟩ := hτmem
  have hzroot : aeval (z : L) (minpoly K (x : L)) = 0 := by
    have hzB := (mem_roots (hgmonic.map _).ne_zero).mp hz
    have hzL := congrArg (algebraMap B L) hzB
    rw [map_zero, ← eval₂_at_apply, ← eval_map, hgL, eval_map] at hzL
    exact hzL
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root'
    (Algebra.IsAlgebraic.isAlgebraic (x : L) (R := K)) hzroot
  refine ⟨σ, ?_⟩
  rw [residueHom_apply]
  exact (congrArg (residue B) (Subtype.ext hσ)).trans hzy

open scoped Topology in
theorem residueHom_denseRange [Finite (ResidueField (baseIntegers K))] :
    DenseRange (residueHom K L) := by
  intro τ
  rw [mem_closure_iff_nhds]
  intro s hs
  have hn : (fun γ => τ * γ) ⁻¹' s ∈ 𝓝 (1 :
      Gal(ResidueField (extensionIntegers K L)/ResidueField (baseIntegers K))) := by
    apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
    simpa using hs
  obtain ⟨E, hE, hEN⟩ := (krullTopology_mem_nhds_one_iff _ _ _).mp hn
  let := hE
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_bot
    (ResidueField (baseIntegers K)) E
  have hgen : IntermediateField.adjoin (ResidueField (baseIntegers K))
      {(α : ResidueField (extensionIntegers K L))} = E := by
    have h := congrArg (fun J : IntermediateField (ResidueField (baseIntegers K)) E =>
      J.map E.val) hα
    simpa only [IntermediateField.adjoin_map, Set.image_singleton,
      ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val,
      IntermediateField.coe_val] using h
  obtain ⟨σ, hσ⟩ := residueHom_lift_single K L τ (α : ResidueField (extensionIntegers K L))
  have hfix : τ⁻¹ * residueHom K L σ ∈ E.fixingSubgroup := by
    rw [← hgen, IntermediateField.mem_fixingSubgroup_iff]
    apply (IntermediateField.forall_mem_adjoin_smul_eq_self_iff
      (ResidueField (baseIntegers K)) (τ⁻¹ * residueHom K L σ)).mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    change τ.symm (residueHom K L σ α) = α
    rw [hσ, τ.symm_apply_apply]
  have hmem := hEN hfix
  simp only [Set.mem_preimage, mul_inv_cancel_left] at hmem
  exact ⟨residueHom K L σ, hmem, ⟨σ, rfl⟩⟩

end Normal

section Galois

variable (K L : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Field L] [Algebra K L] [IsGalois K L]
    [Finite (ResidueField (baseIntegers K))]

theorem residueHom_surjective : Function.Surjective (residueHom K L) := by
  have hc : IsClosed (Set.range (residueHom K L)) :=
    (isCompact_range (residueHom_continuous K L)).isClosed
  intro τ
  change τ ∈ Set.range (residueHom K L)
  rw [← hc.closure_eq]
  exact residueHom_denseRange K L τ

def residueQuotientEquiv :
    (Gal(L/K) ⧸ inertia K L) ≃ₜ*
      Gal(ResidueField (extensionIntegers K L)/ResidueField (baseIntegers K)) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective (residueHom K L)
    (residueHom_surjective K L)
  have he : Continuous e := by
    apply (QuotientGroup.isQuotientMap_mk (inertia K L)).continuous_iff.mpr
    exact residueHom_continuous K L
  exact
    { toMulEquiv := e
      continuous_toFun := he
      continuous_invFun := he.continuous_symm_of_equiv_compact_to_t2 }

theorem residueHom_isOpenMap : IsOpenMap (residueHom K L) :=
  (residueQuotientEquiv K L).toHomeomorph.isOpenMap.comp
    (QuotientGroup.isOpenMap_coe (N := inertia K L))

omit [Finite (ResidueField (baseIntegers K))] in
theorem inertia_compactSpace : CompactSpace (inertia K L) :=
  isCompact_iff_compactSpace.mp (inertia_isClosed K L).isCompact

omit [Finite (ResidueField (baseIntegers K))] in
theorem inertia_totallyDisconnectedSpace : TotallyDisconnectedSpace (inertia K L) :=
  inferInstance

end Galois

theorem spectralResidueExactness : SpectralResidueExactness := by
  intro K L _ _ _ _ _ _ _
  exact ⟨integral_iff_mem_spectralIntegers K L,
    fun [_] => residueExtension_isAlgClosure K L, residueHom_apply K L,
    residueHom_continuous K L, residueHom_surjective K L, residueHom_isOpenMap K L,
    mem_inertia_iff K L, inertia_eq_comap_valuationSubring K L, inferInstance,
    inertia_isClosed K L, inertia_compactSpace K L, inertia_totallyDisconnectedSpace K L,
    residueQuotientEquiv K L, fun _ => rfl⟩

end Langlands.LocalGalois
