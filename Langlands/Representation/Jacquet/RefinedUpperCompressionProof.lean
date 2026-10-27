import Langlands.Representation.Jacquet.RefinedUpperCanonicalLiftProof
import Langlands.Representation.Jacquet.RefinedOppositeCompressionProof

/-!
# Compression identities for the upper refined radical of a product Levi

The multiplication law and the quotient compatibility of compression by
weakly contracting block scalars, for the product upper radical. Both are
obtained from the published opposite identities by blockwise inverse transpose.
-/

noncomputable section

namespace Langlands.Jacquet

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- Compression by weakly contracting block scalars for the upper refined
radical is multiplicative, and it is compatible with the actual quotient map. -/
theorem refinedUpperCompression :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ (ρ : Representation ℂ (B.Levi F.Carrier) V) (hρ : IsSmooth ρ)
      (K : ∀ i, OpenSubgroup (GeneralLinear (B.size i) F.Carrier))
      (hK : ∀ i, IsCompact (K i : Set (GeneralLinear (B.size i) F.Carrier))),
      (∀ i, (S i).HasBlockIwahoriFactorization T (K i)) →
        (∀ a b : ∀ i, Fin (S i).length → F.Carrierˣ,
          (∀ i, (S i).IsWeaklyContracting T (a i)) →
          (∀ i, (S i).IsWeaklyContracting T (b i)) →
            compressedAction ρ hρ (CuspidalSupport.leviPiOpenSubgroup T B K)
                (CuspidalSupport.isCompact_leviPiOpenSubgroup T B K hK)
                (fun i => (S i).blockScalar F.Carrier ((a * b) i)) =
              compressedAction ρ hρ (CuspidalSupport.leviPiOpenSubgroup T B K)
                  (CuspidalSupport.isCompact_leviPiOpenSubgroup T B K hK)
                  (fun i => (S i).blockScalar F.Carrier (a i)) *
                compressedAction ρ hρ (CuspidalSupport.leviPiOpenSubgroup T B K)
                  (CuspidalSupport.isCompact_leviPiOpenSubgroup T B K hK)
                  (fun i => (S i).blockScalar F.Carrier (b i))) ∧
        (∀ a : ∀ i, Fin (S i).length → F.Carrierˣ,
          (∀ i, (S i).IsWeaklyContracting T (a i)) →
          ∀ v : fixedVectors ρ (CuspidalSupport.leviPiOpenSubgroup T B K).toSubgroup,
            mk ρ (refinedUnipotent F.Carrier B S)
                (compressedAction ρ hρ (CuspidalSupport.leviPiOpenSubgroup T B K)
                  (CuspidalSupport.isCompact_leviPiOpenSubgroup T B K hK)
                  (fun i => (S i).blockScalar F.Carrier (a i)) v : V) =
              mk ρ (refinedUnipotent F.Carrier B S)
                (ρ (fun i => (S i).blockScalar F.Carrier (a i)) (v : V))) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro ρ hρ K hK hfac
  let e := leviInverseTranspose F T B
  let K' : ∀ i, OpenSubgroup (GeneralLinear (B.size i) F.Carrier) := fun i =>
    (K i).comap (T.generalLinearInverseTranspose (B.size i)).toMonoidHom
      (T.generalLinearInverseTranspose (B.size i)).continuous
  have hK' : ∀ i, IsCompact (K' i : Set (GeneralLinear (B.size i) F.Carrier)) := fun i =>
    BlockShape.inverseTranspose_compact_comap T (B.size i) (K i) (hK i)
  have hfac' : ∀ i, (S i).HasBlockIwahoriFactorization T (K' i) := fun i =>
    BlockShape.inverseTranspose_iwahoriFactorization T (S i) (K i) (hfac i)
  have hρ' : IsSmooth (ρ.comp e.toMonoidHom) := isSmooth_comp e.toMonoidHom e.continuous hρ
  have hopp := refinedOppositeCompression.{uF, uV} p F T n B S V (ρ.comp e.toMonoidHom) hρ'
    K' hK' hfac'
  let KP := CuspidalSupport.leviPiOpenSubgroup T B K
  let hKP := CuspidalSupport.isCompact_leviPiOpenSubgroup T B K hK
  let KP' := CuspidalSupport.leviPiOpenSubgroup T B K'
  let hKP' := CuspidalSupport.isCompact_leviPiOpenSubgroup T B K' hK'
  have hKL : KP'.toSubgroup.map e.toMonoidHom = KP.toSubgroup :=
    leviInverseTranspose_map_leviPiOpenSubgroup F T B K
  let E := fixedVectorsGroupTransportEquiv e ρ KP' KP hKL
  have hg (a : ∀ i, Fin (S i).length → F.Carrierˣ) :
      e (fun i => ((S i).blockScalar F.Carrier (a i))⁻¹) =
        fun i => (S i).blockScalar F.Carrier (a i) :=
    leviInverseTranspose_blockScalar_inv F T B S a
  have hconj (a : ∀ i, Fin (S i).length → F.Carrierˣ)
      (w : fixedVectors (ρ.comp e.toMonoidHom) KP'.toSubgroup) :
      E (compressedAction (ρ.comp e.toMonoidHom) hρ' KP' hKP'
          (fun i => ((S i).blockScalar F.Carrier (a i))⁻¹) w) =
        compressedAction ρ hρ KP hKP (fun i => (S i).blockScalar F.Carrier (a i)) (E w) := by
    have h := compressedAction_groupTransport e ρ hρ KP' hKP' KP hKP hKL
      (fun i => ((S i).blockScalar F.Carrier (a i))⁻¹) w
    rw [hg a] at h
    exact h
  refine ⟨fun a b ha hb => ?_, fun a ha v => ?_⟩
  · ext v
    obtain ⟨w, rfl⟩ := E.surjective v
    have hab := LinearMap.congr_fun (hopp.1 a b ha hb) w
    have h1 := congrArg E hab
    rw [hconj (a * b) w, Module.End.mul_apply, hconj a, hconj b] at h1
    rw [Module.End.mul_apply]
    exact congrArg Subtype.val h1
  · obtain ⟨w, rfl⟩ := E.surjective v
    have hq := hopp.2 a ha w
    have h2 := congrArg (coinvariantsGroupTransportEquiv e ρ
      (refinedOppositeUnipotent F.Carrier B S) (refinedUnipotent F.Carrier B S)
      (leviInverseTranspose_refinedOppositeUnipotent_map F T B S)) hq
    rw [coinvariantsGroupTransportEquiv_mk, coinvariantsGroupTransportEquiv_mk] at h2
    have h3 : (compressedAction (ρ.comp e.toMonoidHom) hρ' KP' hKP'
        (fun i => ((S i).blockScalar F.Carrier (a i))⁻¹) w : V) =
        (compressedAction ρ hρ KP hKP (fun i => (S i).blockScalar F.Carrier (a i))
          (E w) : V) :=
      congrArg Subtype.val (hconj a w)
    rw [h3] at h2
    change mk ρ (refinedUnipotent F.Carrier B S) _ =
      mk ρ (refinedUnipotent F.Carrier B S)
        (ρ (fun i => (S i).blockScalar F.Carrier (a i)) (w : V))
    rw [h2]
    change mk ρ (refinedUnipotent F.Carrier B S)
        (ρ (e (fun i => ((S i).blockScalar F.Carrier (a i))⁻¹)) (w : V)) = _
    rw [hg a]

end Langlands.Jacquet
