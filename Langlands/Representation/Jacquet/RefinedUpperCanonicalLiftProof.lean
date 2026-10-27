import Langlands.Representation.Jacquet.RefinedOppositeCanonicalLiftProof
import Langlands.Representation.Jacquet.CanonicalLiftGroupTransportProof
import Langlands.Group.GL.InverseTransposeIwahoriProof
import Langlands.Representation.CuspidalSupport.GroupTransport

/-!
# Upper canonical Jacquet lifts for product Levis

The product-Levi canonical-lift assertions for the upper refined radical,
obtained from the published opposite ones by blockwise inverse transpose.
-/

noncomputable section

namespace Langlands.Jacquet

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Blockwise inverse transpose on a product Levi, as a topological group
automorphism. -/
def leviInverseTranspose :
    letI := T.topology
    B.Levi F.Carrier ≃ₜ* B.Levi F.Carrier := by
  letI := T.topology
  exact
    { toMulEquiv := MulEquiv.piCongrRight fun i =>
        (T.generalLinearInverseTranspose (B.size i)).toMulEquiv
      continuous_toFun := continuous_pi fun i =>
        (T.generalLinearInverseTranspose (B.size i)).continuous.comp (continuous_apply i)
      continuous_invFun := continuous_pi fun i =>
        (T.generalLinearInverseTranspose (B.size i)).symm.continuous.comp
          (continuous_apply i) }

theorem leviInverseTranspose_apply (g : B.Levi F.Carrier) (i : Fin B.length) :
    leviInverseTranspose F T B g i = inverseTranspose (B.size i) F.Carrier (g i) :=
  rfl

theorem leviInverseTranspose_involutive (g : B.Levi F.Carrier) :
    leviInverseTranspose F T B (leviInverseTranspose F T B g) = g := by
  funext i
  exact inverseTranspose_involutive (B.size i) F.Carrier (g i)

/-- The comap of a product of open subgroups is the product of the comaps. -/
theorem leviInverseTranspose_map_leviPiOpenSubgroup :
    letI := T.topology
    ∀ K : ∀ i, OpenSubgroup (GeneralLinear (B.size i) F.Carrier),
      (CuspidalSupport.leviPiOpenSubgroup T B (fun i =>
          (K i).comap (T.generalLinearInverseTranspose (B.size i)).toMonoidHom
            (T.generalLinearInverseTranspose (B.size i)).continuous)).toSubgroup.map
          (leviInverseTranspose F T B).toMonoidHom =
        (CuspidalSupport.leviPiOpenSubgroup T B K).toSubgroup := by
  let := T.topology
  intro K
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := (CuspidalSupport.mem_leviPiOpenSubgroup T B _ x).mp hx
    exact (CuspidalSupport.mem_leviPiOpenSubgroup T B K _).mpr fun j => hx' j
  · intro hg
    have hg' := (CuspidalSupport.mem_leviPiOpenSubgroup T B K g).mp hg
    refine ⟨leviInverseTranspose F T B g, ?_, leviInverseTranspose_involutive F T B g⟩
    refine (CuspidalSupport.mem_leviPiOpenSubgroup T B _ _).mpr fun j => ?_
    change inverseTranspose (B.size j) F.Carrier
      (inverseTranspose (B.size j) F.Carrier (g j)) ∈ K j
    rw [inverseTranspose_involutive]
    exact hg' j

/-- Blockwise inverse transpose carries the product opposite radical onto the
product upper radical. -/
theorem leviInverseTranspose_refinedOppositeUnipotent_map :
    (refinedOppositeUnipotent F.Carrier B S).map
        (leviInverseTranspose F T B).toMonoidHom =
      refinedUnipotent F.Carrier B S := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := (mem_refinedOppositeUnipotent F.Carrier B S x).mp hx
    refine (Subgroup.mem_pi _).mpr fun i _ => ?_
    exact ((S i).inverseTranspose_mem_unipotentSubgroup_iff F.Carrier (x i)).mpr (hx' i)
  · intro hg
    refine ⟨leviInverseTranspose F T B g, ?_, leviInverseTranspose_involutive F T B g⟩
    refine (mem_refinedOppositeUnipotent F.Carrier B S _).mpr fun i => ?_
    exact ((S i).inverseTranspose_mem_oppositeUnipotentSubgroup_iff F.Carrier (g i)).mpr
      ((Subgroup.mem_pi _).mp hg i (Set.mem_univ i))

/-- Blockwise inverse transpose preserves the refined Levi. -/
theorem leviInverseTranspose_refinedLevi_map :
    (refinedLevi F.Carrier B S).map (leviInverseTranspose F T B).toMonoidHom =
      refinedLevi F.Carrier B S := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine (Subgroup.mem_pi _).mpr fun i _ => ?_
    exact ((S i).inverseTranspose_mem_leviSubgroup_iff F.Carrier (x i)).mpr
      ((Subgroup.mem_pi _).mp hx i (Set.mem_univ i))
  · intro hg
    refine ⟨leviInverseTranspose F T B g, ?_, leviInverseTranspose_involutive F T B g⟩
    refine (Subgroup.mem_pi _).mpr fun i _ => ?_
    exact ((S i).inverseTranspose_mem_leviSubgroup_iff F.Carrier (g i)).mpr
      ((Subgroup.mem_pi _).mp hg i (Set.mem_univ i))

/-- Blockwise inverse transpose inverts a tuple of block scalars. -/
theorem leviInverseTranspose_blockScalar_inv (a : ∀ i, Fin (S i).length → F.Carrierˣ) :
    leviInverseTranspose F T B (fun i => ((S i).blockScalar F.Carrier (a i))⁻¹) =
      fun i => (S i).blockScalar F.Carrier (a i) := by
  funext i
  change inverseTranspose (B.size i) F.Carrier ((S i).blockScalar F.Carrier (a i))⁻¹ = _
  rw [map_inv, (S i).inverseTranspose_blockScalar F.Carrier (a i), inv_inv]

variable (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- The generalized compression kernel for the product upper radical is the
kernel of the fixed-vector Jacquet map. -/
theorem refinedPowerKernelJacquet :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ (ρ : Representation ℂ (B.Levi F.Carrier) V) (hAdmissible : IsAdmissible ρ)
      (K : ∀ i, OpenSubgroup (GeneralLinear (B.size i) F.Carrier))
      (hK : ∀ i, IsCompact (K i : Set (GeneralLinear (B.size i) F.Carrier))),
      (∀ i, (S i).HasBlockIwahoriFactorization T (K i)) →
      ∀ a : ∀ i, Fin (S i).length → F.Carrierˣ,
        (∀ i, (S i).IsStrictlyContracting T (a i)) →
        powerKernelSup ρ hAdmissible.1 (CuspidalSupport.leviPiOpenSubgroup T B K)
            (CuspidalSupport.isCompact_leviPiOpenSubgroup T B K hK)
            (fun i => (S i).blockScalar F.Carrier (a i)) =
          LinearMap.ker (fixedJacquetMap ρ
            (refinedUnipotent F.Carrier B S) (refinedLevi F.Carrier B S)
            (fun m hm => (refinedLeviNormalizer F.Carrier B S ⟨m, hm⟩).property)
            (CuspidalSupport.leviPiOpenSubgroup T B K).toSubgroup) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro ρ hAdmissible K hK hfac a ha
  let e := leviInverseTranspose F T B
  let K' : ∀ i, OpenSubgroup (GeneralLinear (B.size i) F.Carrier) := fun i =>
    (K i).comap (T.generalLinearInverseTranspose (B.size i)).toMonoidHom
      (T.generalLinearInverseTranspose (B.size i)).continuous
  have hK' : ∀ i, IsCompact (K' i : Set (GeneralLinear (B.size i) F.Carrier)) := fun i =>
    BlockShape.inverseTranspose_compact_comap T (B.size i) (K i) (hK i)
  have hfac' : ∀ i, (S i).HasBlockIwahoriFactorization T (K' i) := fun i =>
    BlockShape.inverseTranspose_iwahoriFactorization T (S i) (K i) (hfac i)
  have hAdmissible' := isAdmissible_comp_continuousMulEquiv ρ e hAdmissible
  have hopp := refinedOppositePowerKernelJacquet F T B S V
    (ρ.comp e.toMonoidHom) hAdmissible' K' hK' hfac' a ha
  have htransport := powerKernelSup_eq_ker_groupTransport e ρ hAdmissible.1
    (CuspidalSupport.leviPiOpenSubgroup T B K')
    (CuspidalSupport.isCompact_leviPiOpenSubgroup T B K' hK')
    (CuspidalSupport.leviPiOpenSubgroup T B K)
    (CuspidalSupport.isCompact_leviPiOpenSubgroup T B K hK)
    (leviInverseTranspose_map_leviPiOpenSubgroup F T B K)
    (refinedOppositeUnipotent F.Carrier B S) (refinedLevi F.Carrier B S)
    (refinedUnipotent F.Carrier B S) (refinedLevi F.Carrier B S)
    (fun m hm => (refinedOppositeLeviNormalizer F.Carrier B S ⟨m, hm⟩).property)
    (fun m hm => (refinedLeviNormalizer F.Carrier B S ⟨m, hm⟩).property)
    (leviInverseTranspose_refinedOppositeUnipotent_map F T B S)
    (leviInverseTranspose_refinedLevi_map F T B S)
    (fun i => ((S i).blockScalar F.Carrier (a i))⁻¹)
  have hg : e (fun i => ((S i).blockScalar F.Carrier (a i))⁻¹) =
      fun i => (S i).blockScalar F.Carrier (a i) :=
    leviInverseTranspose_blockScalar_inv F T B S a
  have hout := htransport.mp hopp
  rw [hg] at hout
  exact hout

/-- The fixed-vector Jacquet map for the product upper radical is bijective on
the stable image of compression by the block-scalar tuple. -/
theorem refinedStableImageJacquetBijective :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ (ρ : Representation ℂ (B.Levi F.Carrier) V) (hAdmissible : IsAdmissible ρ)
      (K : ∀ i, OpenSubgroup (GeneralLinear (B.size i) F.Carrier))
      (hK : ∀ i, IsCompact (K i : Set (GeneralLinear (B.size i) F.Carrier))),
      (∀ i, (S i).HasBlockIwahoriFactorization T (K i)) →
      ∀ a : ∀ i, Fin (S i).length → F.Carrierˣ,
        (∀ i, (S i).IsStrictlyContracting T (a i)) →
        Function.Bijective (stableImageJacquetMap ρ hAdmissible.1
          (CuspidalSupport.leviPiOpenSubgroup T B K)
          (CuspidalSupport.isCompact_leviPiOpenSubgroup T B K hK)
          (fun i => (S i).blockScalar F.Carrier (a i))
          (refinedUnipotent F.Carrier B S) (refinedLevi F.Carrier B S)
          (fun m hm => (refinedLeviNormalizer F.Carrier B S ⟨m, hm⟩).property)) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro ρ hAdmissible K hK hfac a ha
  let e := leviInverseTranspose F T B
  let K' : ∀ i, OpenSubgroup (GeneralLinear (B.size i) F.Carrier) := fun i =>
    (K i).comap (T.generalLinearInverseTranspose (B.size i)).toMonoidHom
      (T.generalLinearInverseTranspose (B.size i)).continuous
  have hK' : ∀ i, IsCompact (K' i : Set (GeneralLinear (B.size i) F.Carrier)) := fun i =>
    BlockShape.inverseTranspose_compact_comap T (B.size i) (K i) (hK i)
  have hfac' : ∀ i, (S i).HasBlockIwahoriFactorization T (K' i) := fun i =>
    BlockShape.inverseTranspose_iwahoriFactorization T (S i) (K i) (hfac i)
  have hAdmissible' := isAdmissible_comp_continuousMulEquiv ρ e hAdmissible
  have hopp := refinedOppositeStableImageJacquetBijective F T B S V
    (ρ.comp e.toMonoidHom) hAdmissible' K' hK' hfac' a ha
  have htransport := stableImageJacquetMap_bijective_groupTransport e ρ hAdmissible.1
    (CuspidalSupport.leviPiOpenSubgroup T B K')
    (CuspidalSupport.isCompact_leviPiOpenSubgroup T B K' hK')
    (CuspidalSupport.leviPiOpenSubgroup T B K)
    (CuspidalSupport.isCompact_leviPiOpenSubgroup T B K hK)
    (leviInverseTranspose_map_leviPiOpenSubgroup F T B K)
    (refinedOppositeUnipotent F.Carrier B S) (refinedLevi F.Carrier B S)
    (refinedUnipotent F.Carrier B S) (refinedLevi F.Carrier B S)
    (fun m hm => (refinedOppositeLeviNormalizer F.Carrier B S ⟨m, hm⟩).property)
    (fun m hm => (refinedLeviNormalizer F.Carrier B S ⟨m, hm⟩).property)
    (leviInverseTranspose_refinedOppositeUnipotent_map F T B S)
    (leviInverseTranspose_refinedLevi_map F T B S)
    (fun i => ((S i).blockScalar F.Carrier (a i))⁻¹)
  have hg : e (fun i => ((S i).blockScalar F.Carrier (a i))⁻¹) =
      fun i => (S i).blockScalar F.Carrier (a i) :=
    leviInverseTranspose_blockScalar_inv F T B S a
  have hout := htransport.mp hopp
  rw [hg] at hout
  exact hout

end Langlands.Jacquet
