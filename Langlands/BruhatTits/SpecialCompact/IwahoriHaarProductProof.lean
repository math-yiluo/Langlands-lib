import Langlands.BruhatTits.SpecialCompact.IwahoriHaarProductStatement
import Langlands.BruhatTits.SpecialCompact.IwahoriRelativeIndexProof
import Langlands.Analysis.Local.CompactOpenIndexHaarProof

/-! # Proof of the Iwahori Haar-character product -/

noncomputable section

universe u

open MeasureTheory Filter Topology
open scoped NNReal

namespace Langlands.BruhatTits.SpecialCompact

variable {G : Type u} [Group G]

private theorem iwahori_map
    (e : G ≃* G) {K M U V : Subgroup G}
    (hK : HasIwahoriIntersectionDecomposition K M U V) :
    HasIwahoriIntersectionDecomposition (K.map e.toMonoidHom)
      (M.map e.toMonoidHom) (U.map e.toMonoidHom) (V.map e.toMonoidHom) := by
  let t (S : Subgroup G) : ↥(K ⊓ S) ≃* ↥(K.map e.toMonoidHom ⊓ S.map e.toMonoidHom) :=
    (e.subgroupMap (K ⊓ S)).trans
      (MulEquiv.subgroupCongr (Subgroup.map_inf K S e.toMonoidHom e.injective))
  let d := (t V).toEquiv.prodCongr ((t M).toEquiv.prodCongr (t U).toEquiv)
  have heq :
      orderedIntersectionProduct (K.map e.toMonoidHom) (M.map e.toMonoidHom)
          (U.map e.toMonoidHom) (V.map e.toMonoidHom) ∘ d =
        e.subgroupMap K ∘ orderedIntersectionProduct K M U V := by
    funext x
    apply Subtype.ext
    change e (x.1 : G) * e (x.2.1 : G) * e (x.2.2 : G) =
      e ((x.1 : G) * (x.2.1 : G) * (x.2.2 : G))
    simp only [map_mul]
  apply (Function.Bijective.of_comp_iff _ d.bijective).mp
  rw [heq]
  exact (e.subgroupMap K).bijective.comp hK

variable [TopologicalSpace G]

private theorem map_factor_eq
    (α : G ≃ₜ* G) (S : Subgroup G) (β : S ≃ₜ* S)
    (hβ : ∀ x : S, α (x : G) = (β x : G)) :
    S.map α.toMonoidHom = S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hβ ⟨y, hy⟩).symm ▸ (β ⟨y, hy⟩).property
  · intro hx
    refine ⟨(β.symm ⟨x, hx⟩ : G), (β.symm ⟨x, hx⟩).property, ?_⟩
    exact (hβ (β.symm ⟨x, hx⟩)).trans
      (congrArg (fun z : S => (z : G)) (β.apply_symm_apply ⟨x, hx⟩))

private theorem factor_map_comap
    (α : G ≃ₜ* G) (S J : Subgroup G) (β : S ≃ₜ* S)
    (hβ : ∀ x : S, α (x : G) = (β x : G)) :
    (J.comap S.subtype).map β.toMonoidHom =
      (J.map α.toMonoidHom).comap S.subtype := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(y : G), hy, hβ y⟩
  · rintro ⟨y, hy, heq⟩
    have hi : (β.symm x : G) = y := by
      apply α.injective
      exact ((hβ (β.symm x)).trans
        (congrArg (fun z : S => (z : G)) (β.apply_symm_apply x))).trans heq.symm
    refine ⟨β.symm x, ?_, β.apply_symm_apply x⟩
    change (β.symm x : G) ∈ J
    rwa [hi]

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

private theorem factor_haar_index
    (α : G ≃ₜ* G) (S K J : Subgroup G) (β : S ≃ₜ* S)
    (hS : IsClosed (S : Set G))
    (hβ : ∀ x : S, α (x : G) = (β x : G))
    (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (hJo : IsOpen (J : Set G)) (hJK : J ≤ K)
    (hαJK : J.map α.toMonoidHom ≤ K) :
    haveI : LocallyCompactSpace S := hS.locallyCompactSpace
    mulEquivHaarChar β * ((J.map α.toMonoidHom).relIndex (K ⊓ S) : ℝ≥0) =
      (J.relIndex (K ⊓ S) : ℝ≥0) := by
  let : LocallyCompactSpace S := hS.locallyCompactSpace
  have h := (Langlands.Haar.compactOpenIndexHaar S β
    (K.comap S.subtype) (J.comap S.subtype)
    (hS.isClosedEmbedding_subtypeVal.isCompact_preimage hKc)
    (hKo.preimage continuous_subtype_val) (hJo.preimage continuous_subtype_val)
    (Subgroup.comap_mono hJK) ?_).1
  · rw [factor_map_comap α S J β hβ] at h
    rw [Subgroup.relIndex_comap, Subgroup.relIndex_comap,
      show (K.comap S.subtype).map S.subtype = K ⊓ S from
        Subgroup.subgroupOf_map_subtype K S] at h
    exact h
  · rw [factor_map_comap α S J β hβ]
    exact Subgroup.comap_mono hαJK

/-- The simultaneous normal basis gives the product of the three Haar
characters, at every universe. -/
theorem iwahoriHaarProduct : IwahoriHaarProductStatement.{u} := by
  intro G _ _ _ _ _ _ M U V P K0 B α αM αU αV hM hU hV
    hb hi hMP hUP hVP hαM hαU hαV
  let : LocallyCompactSpace M := hM.locallyCompactSpace
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : LocallyCompactSpace V := hV.locallyCompactSpace
  obtain ⟨K, hKB⟩ := hb.2.ex_mem
  obtain ⟨hKK0, _, hKo, hKc⟩ := hb.1 K hKB
  have hn : ((K : Set G) ∩ α ⁻¹' (K : Set G)) ∈ 𝓝 (1 : G) :=
    inter_mem (hKo.mem_nhds K.one_mem)
      ((hKo.preimage α.continuous).mem_nhds (by simp))
  obtain ⟨J, hJB, hJsmall⟩ := hb.2.mem_iff.mp hn
  have hJK : J ≤ K := fun _ hx => (hJsmall hx).1
  have hαJK : J.map α.toMonoidHom ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hJsmall hx).2
  have hJo := (hb.1 J hJB).2.2.1
  have hαJo : IsOpen (J.map α.toMonoidHom : Set G) :=
    α.toHomeomorph.isOpenMap _ hJo
  have hn' : ((J : Set G) ∩ (J.map α.toMonoidHom : Set G)) ∈ 𝓝 (1 : G) :=
    inter_mem (hJo.mem_nhds J.one_mem)
      (hαJo.mem_nhds (J.map α.toMonoidHom).one_mem)
  obtain ⟨H, hHB, hHsmall⟩ := hb.2.mem_iff.mp hn'
  have hHJ : H ≤ J := fun _ hx => (hHsmall hx).1
  have hHαJ : H ≤ J.map α.toMonoidHom := fun _ hx => (hHsmall hx).2
  have hHnormal : (H.subgroupOf K).Normal :=
    (hb.1 H hHB).2.1.comap (Subgroup.inclusion hKK0)
  have hHo := (hb.1 H hHB).2.2.1
  have : (H.subgroupOf K).FiniteIndex :=
    Langlands.Haar.finiteIndex_subgroupOf_compact_open K H hKc hHo
  have hfinite : H.relIndex K ≠ 0 :=
    Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf K)
  have hαJ : HasIwahoriIntersectionDecomposition
      (J.map α.toMonoidHom) M U V := by
    have h := iwahori_map α.toMulEquiv (hi J hJB)
    rw [map_factor_eq α M αM hαM, map_factor_eq α U αU hαU,
      map_factor_eq α V αV hαV] at h
    exact h
  have hindexJ := iwahoriRelativeIndex G K J H M U V P
    hHJ hJK hHnormal hfinite hMP hUP hVP (hi K hKB) (hi J hJB) (hi H hHB)
  have hindexαJ := iwahoriRelativeIndex G K (J.map α.toMonoidHom) H M U V P
    hHαJ hαJK hHnormal hfinite hMP hUP hVP (hi K hKB) hαJ (hi H hHB)
  have hMindex := factor_haar_index α M K J αM hM hαM hKc hKo hJo hJK hαJK
  have hUindex := factor_haar_index α U K J αU hU hαU hKc hKo hJo hJK hαJK
  have hVindex := factor_haar_index α V K J αV hV hαV hKc hKo hJo hJK hαJK
  have hambient := (Langlands.Haar.compactOpenIndexHaar G α K J
    hKc hKo hJo hJK hαJK).1
  have hproduct :
      (mulEquivHaarChar αV * mulEquivHaarChar αM * mulEquivHaarChar αU) *
        ((J.map α.toMonoidHom).relIndex K : ℝ≥0) = (J.relIndex K : ℝ≥0) := by
    rw [hindexαJ, hindexJ, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
    calc
      _ = (mulEquivHaarChar αV *
            ((J.map α.toMonoidHom).relIndex (K ⊓ V) : ℝ≥0)) *
          (mulEquivHaarChar αM *
            ((J.map α.toMonoidHom).relIndex (K ⊓ M) : ℝ≥0)) *
          (mulEquivHaarChar αU *
            ((J.map α.toMonoidHom).relIndex (K ⊓ U) : ℝ≥0)) := by ac_rfl
      _ = _ := by rw [hVindex, hMindex, hUindex]
  have : ((J.map α.toMonoidHom).subgroupOf K).FiniteIndex :=
    Langlands.Haar.finiteIndex_subgroupOf_compact_open K
      (J.map α.toMonoidHom) hKc hαJo
  have hnonzero : ((J.map α.toMonoidHom).relIndex K : ℝ≥0) ≠ 0 := by
    exact_mod_cast
      (Subgroup.FiniteIndex.index_ne_zero (H := (J.map α.toMonoidHom).subgroupOf K))
  exact mul_right_cancel₀ hnonzero (hambient.trans hproduct.symm)

end Langlands.BruhatTits.SpecialCompact
