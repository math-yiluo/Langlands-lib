import Langlands.BushnellKutzko.SplitTypeJacquet.LayerCoordinates
import Langlands.BushnellKutzko.SplitTypeJacquet.StandardType

/-! # Standard coordinates for a lattice chain with cuspidal layer data

For a lattice chain `L` in `F^{m+1}` with cuspidal layer data `a`, the block shape `layerShape a`
lists the layer ranks in reversed order. Reversing makes the order `𝔄(L)` block upper
triangular modulo the maximal ideal. The matrix `layerChange a` takes the standard basis to the
adapted basis, so conjugation by it carries the unit group `J0 F (blkOf (layerShape a))` of the
standard order onto the matrices of `U(𝔄)`. -/

open ValuativeRel Matrix Langlands.GeneralLinear Langlands.Geometric

noncomputable section

namespace Langlands.BushnellKutzko.SplitTypeJacquet

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

variable (F) in
/-- A chosen uniformizer of `𝔬_F`. -/
def unif : 𝒪[F] := (IsDiscreteValuationRing.exists_irreducible 𝒪[F]).choose

theorem unif_irreducible : Irreducible (unif F) :=
  (IsDiscreteValuationRing.exists_irreducible 𝒪[F]).choose_spec

variable {m : ℕ} {L : LatticeChain 𝒪[F] F (Fin (m + 1) → F)}

theorem layerRank_pos (a : L.CuspidalLayerData) (i : Fin L.period) :
    0 < a.rank i := by
  have := L.layer_nontrivial ((i : ℕ) : ℤ)
  obtain ⟨r⟩ := (a.basis i).index_nonempty
  exact Fin.pos r

theorem layerRank_sum (a : L.CuspidalLayerData) :
    ∑ i, a.rank (Fin.revPerm i) = m + 1 := by
  rw [Equiv.sum_comp Fin.revPerm a.rank]
  have h := Module.finrank_eq_card_basis (adaptedBasis L a.basis (unif_irreducible (F := F)))
  rw [Module.finrank_fin_fun, Fintype.card_sigma] at h
  simpa using h.symm

/-- The block shape with the layer ranks of `a` in reversed order. -/
def layerShape (a : L.CuspidalLayerData) : BlockShape (m + 1) where
  length := L.period
  size i := a.rank (Fin.revPerm i)
  positive _ := layerRank_pos a _
  sum_eq := layerRank_sum a

/-- Standard coordinates numbered by the layers, the blocks being the layers in reversed
order. -/
def layerEquiv (a : L.CuspidalLayerData) :
    Fin (m + 1) ≃ Σ i : Fin L.period, Fin (a.rank i) :=
  (layerShape a).indexEquiv.symm.trans (Equiv.sigmaCongrLeft (β := fun i => Fin (a.rank i))
    Fin.revPerm)

theorem layerEquiv_fst (a : L.CuspidalLayerData) (c : Fin (m + 1)) :
    (layerEquiv a c).1 = Fin.revPerm (blockIndex (layerShape a) c) := rfl

theorem layerEquiv_symm_apply (a : L.CuspidalLayerData) (i : Fin L.period)
    (r : Fin (a.rank (Fin.revPerm i))) :
    (layerEquiv a).symm ⟨Fin.revPerm i, r⟩ = (layerShape a).index i r := by
  rw [Equiv.symm_apply_eq]
  change _ = Equiv.sigmaCongrLeft (β := fun i => Fin (a.rank i)) Fin.revPerm
    ((layerShape a).indexEquiv.symm ((layerShape a).indexEquiv ⟨i, r⟩))
  rw [Equiv.symm_apply_apply]
  rfl

theorem layerEquiv_lt_iff (a : L.CuspidalLayerData) (c c' : Fin (m + 1)) :
    ((layerEquiv a c).1 : ℕ) < ((layerEquiv a c').1 : ℕ) ↔
      blkOf (layerShape a) c' < blkOf (layerShape a) c := by
  rw [layerEquiv_fst, layerEquiv_fst, ← Fin.lt_def, Fin.revPerm_apply, Fin.revPerm_apply,
    Fin.rev_lt_rev]
  rfl

/-- The adapted basis of `a`, numbered by the standard coordinates. -/
def layerBasis (a : L.CuspidalLayerData) : Module.Basis (Fin (m + 1)) F (Fin (m + 1) → F) :=
  coordBasis L a.basis (unif_irreducible (F := F)) (layerEquiv a)

/-- The matrix whose columns are the vectors of the adapted basis. -/
def layerChange (a : L.CuspidalLayerData) : GL (Fin (m + 1)) F :=
  ⟨(Pi.basisFun F (Fin (m + 1))).toMatrix (layerBasis a),
    (layerBasis a).toMatrix (Pi.basisFun F (Fin (m + 1))),
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩

/-- Conjugation by `layerChange a` realises the action through the adapted basis. -/
theorem toLin_layerChange_conj (a : L.CuspidalLayerData) (x : GL (Fin (m + 1)) F) :
    Matrix.GeneralLinearGroup.toLin (layerChange a * x * (layerChange a)⁻¹) =
      stdToAut L a.basis (unif_irreducible (F := F)) (layerEquiv a) x := by
  apply Units.ext
  change Matrix.toLin' ((Pi.basisFun F (Fin (m + 1))).toMatrix (layerBasis a) *
    (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      (layerBasis a).toMatrix (Pi.basisFun F (Fin (m + 1)))) = _
  rw [coe_stdToAut]
  have h := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    (Pi.basisFun F (Fin (m + 1))) (layerBasis a) (Pi.basisFun F (Fin (m + 1))) (layerBasis a)
    (Matrix.toLin (layerBasis a) (layerBasis a) (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
  rw [LinearMap.toMatrix_toLin, LinearMap.toMatrix_eq_toMatrix'] at h
  rw [h, Matrix.toLin'_toMatrix']
  rfl

open Langlands.FiniteGeneralLinear Langlands.FiniteRep in
/-- An irreducible cuspidal layer factor is equivalent to the chosen representative of its
class. -/
def factorEquiv (a : L.CuspidalLayerData) (i : Fin L.period) :
    Representation.Equiv (a.factor i)
      (VirtualCharacter.rep (CuspidalModelClass.ofRepresentation (a.factor i)
        (a.cuspidal i).1 (a.cuspidal i).2).val).ρ :=
  have h : classOf (VirtualCharacter.rep (CuspidalModelClass.ofRepresentation (a.factor i)
      (a.cuspidal i).1 (a.cuspidal i).2).val) = classOf (ofRepresentation (a.factor i)) :=
    VirtualCharacter.classOf_rep _
  (modelEquiv (a.factor i)).trans (equivOfIso ((classOf_eq_iff _ _).mp h).some.symm)

open Langlands.FiniteGeneralLinear in
/-- The finite cuspidal datum of the layer factors, in reversed order. -/
def layerDatum (a : L.CuspidalLayerData) : HarishChandraDatum (m + 1) 𝓀[F] where
  shape := layerShape a
  label i := CuspidalModelClass.ofRepresentation (a.factor (Fin.revPerm i))
    (a.cuspidal _).1 (a.cuspidal _).2

open Langlands.FiniteGeneralLinear Langlands.FiniteRep in
private theorem factorClass_eq_of_label_eq {k : Type uF} [Field k] [Finite k] {r r' d d' : ℕ}
    (hr : 0 < r) (hr' : 0 < r') (f : Representation ℂ (GeneralLinear r k) (Fin d → ℂ))
    (f' : Representation ℂ (GeneralLinear r' k) (Fin d' → ℂ))
    (hf : f.IsIrreducible ∧ IsCuspidal f) (hf' : f'.IsIrreducible ∧ IsCuspidal f')
    (h : (⟨⟨r, hr⟩, CuspidalModelClass.ofRepresentation f hf.1 hf.2⟩ : PositiveCuspidalLabel k) =
      ⟨⟨r', hr'⟩, CuspidalModelClass.ofRepresentation f' hf'.1 hf'.2⟩) :
    (⟨r, (CuspidalRep.of f hf.1 hf.2).isoClass⟩ : Σ d : ℕ, CuspidalClass.{uF, 0} d k) =
      ⟨r', (CuspidalRep.of f' hf'.1 hf'.2).isoClass⟩ := by
  have hrr : r = r' := congrArg (fun x : PositiveCuspidalLabel k => x.1.val) h
  subst hrr
  have h' := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  obtain ⟨e⟩ := (CuspidalModelClass.ofRepresentation_eq_iff f f' hf.1 hf'.1 hf.2 hf'.2).mp h'
  rw [(CuspidalRep.isoClass_eq_iff (CuspidalRep.of f hf.1 hf.2) (CuspidalRep.of f' hf'.1 hf'.2)).mpr
    ⟨e⟩]

/-- Two different layer classes give two different block labels. -/
theorem exists_blockLabel_ne (a : L.CuspidalLayerData)
    (h : ∃ i j, a.factorClass i ≠ a.factorClass j) :
    ∃ i j, (layerDatum a).blockLabel i ≠ (layerDatum a).blockLabel j := by
  obtain ⟨i, j, hij⟩ := h
  obtain ⟨i', rfl⟩ := Fin.revPerm.surjective i
  obtain ⟨j', rfl⟩ := Fin.revPerm.surjective j
  exact ⟨i', j', fun hl => hij (factorClass_eq_of_label_eq _ _ _ _ (a.cuspidal _)
    (a.cuspidal _) hl)⟩

/-- The tensor product of the layer factors, reindexed in reversed order. -/
def layerTensorReindex (a : L.CuspidalLayerData) :
    PiTensorProduct ℂ (fun i => Fin (a.dim i) → ℂ) ≃ₗ[ℂ]
      PiTensorProduct ℂ (fun i => Fin (a.dim (Fin.revPerm i)) → ℂ) :=
  PiTensorProduct.reindex ℂ (fun i => Fin (a.dim i) → ℂ) Fin.revPerm.symm

theorem layerTensorReindex_tprod (a : L.CuspidalLayerData) (v : ∀ i, Fin (a.dim i) → ℂ) :
    layerTensorReindex a (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun i => v (Fin.revPerm i)) :=
  PiTensorProduct.reindex_tprod _ _

open Langlands.FiniteGeneralLinear Langlands.FiniteRep in
/-- The reindexed tensor product transported to the chosen class representatives. -/
def layerTensorCongr (a : L.CuspidalLayerData) :
    PiTensorProduct ℂ (fun i => Fin (a.dim (Fin.revPerm i)) → ℂ) ≃ₗ[ℂ]
      PiTensorProduct ℂ (fun i => (VirtualCharacter.rep ((layerDatum a).label i).val)) :=
  PiTensorProduct.congr fun i => (factorEquiv a (Fin.revPerm i)).toLinearEquiv

open Langlands.FiniteGeneralLinear Langlands.FiniteRep in
theorem layerTensorCongr_tprod (a : L.CuspidalLayerData)
    (v : ∀ i, Fin (a.dim (Fin.revPerm i)) → ℂ) :
    layerTensorCongr a (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun i => (factorEquiv a (Fin.revPerm i)).toLinearEquiv (v i)) :=
  PiTensorProduct.congr_tprod _ _

/-- The tensor product of the layer factors identified with the Levi tensor of the datum. -/
def layerTensorEquiv (a : L.CuspidalLayerData) :
    PiTensorProduct ℂ (fun i => Fin (a.dim i) → ℂ) ≃ₗ[ℂ] (layerDatum a).leviRep :=
  (layerTensorReindex a).trans (layerTensorCongr a)

open Langlands.FiniteGeneralLinear Langlands.FiniteRep in
theorem layerTensorEquiv_tprod (a : L.CuspidalLayerData) (v : ∀ i, Fin (a.dim i) → ℂ) :
    layerTensorEquiv a (PiTensorProduct.tprod ℂ v) =
      (PiTensorProduct.tprod ℂ (fun i => (factorEquiv a (Fin.revPerm i)).toLinearEquiv
        (v (Fin.revPerm i))) :
          PiTensorProduct ℂ (fun i => (VirtualCharacter.rep ((layerDatum a).label i).val))) :=
  (congrArg (layerTensorCongr a) (layerTensorReindex_tprod a v)).trans
    (layerTensorCongr_tprod a _)

theorem stdToAut_layer_mem (a : L.CuspidalLayerData) (x : J0 F (blkOf (layerShape a))) :
    stdToAut L a.basis (unif_irreducible (F := F)) (layerEquiv a) x ∈ L.unitFiltration 0 :=
  (stdToAut_mem_unitFiltration_zero_iff L a.basis _ (layerEquiv a) (layerEquiv_lt_iff a) x).mpr
    x.2

/-- On the layers, the reduction of the adapted action is the Levi part of the reduction of
the matrix. -/
theorem layerReduction_eq_leviProjection (a : L.CuspidalLayerData)
    (x : J0 F (blkOf (layerShape a))) (i : Fin L.period) :
    L.layerReduction a.basis ⟨_, stdToAut_layer_mem a x⟩ (Fin.revPerm i) =
      (layerShape a).leviProjection 𝓀[F] (redJ0 (layerShape a) x) i := by
  apply Matrix.GeneralLinearGroup.ext
  intro r s
  rw [layerReduction_stdToAut_apply L a.basis _ (layerEquiv a) (layerEquiv_lt_iff a) x x.2
    (Fin.revPerm i) r s]
  change _ = ((redJ0 (layerShape a) x : GeneralLinear (m + 1) 𝓀[F]) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) 𝓀[F]) ((layerShape a).index i r)
      ((layerShape a).index i s)
  rw [coe_redJ0, red_apply _ _ _ ((Valuation.mem_integer_iff _ _).mpr (x.2.1 _ _).1)]
  simp only [layerEquiv_symm_apply]

theorem inflation_tprod (a : L.CuspidalLayerData) (g : L.unitFiltration 0)
    (v : ∀ i, Fin (a.dim i) → ℂ) :
    a.inflation g (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun i => a.factor i (L.layerReduction a.basis g i) (v i)) :=
  PiTensorProduct.map_tprod _ _

open Langlands.FiniteGeneralLinear Langlands.FiniteRep in
theorem stdType_layer_tprod (a : L.CuspidalLayerData) (x : J0 F (blkOf (layerShape a)))
    (w : ∀ i, (VirtualCharacter.rep ((layerDatum a).label i).val)) :
    stdType (layerDatum a) x (PiTensorProduct.tprod ℂ w) =
      PiTensorProduct.tprod ℂ (fun i => (VirtualCharacter.rep ((layerDatum a).label i).val).ρ
        ((layerShape a).leviProjection 𝓀[F] (redJ0 (layerShape a) x) i) (w i)) :=
  FiniteTensor.external_tprod _ _ _

/-- **The layer inflation is the standard type.** -/
theorem layerTensorEquiv_inflation (a : L.CuspidalLayerData) (x : J0 F (blkOf (layerShape a)))
    (w : PiTensorProduct ℂ (fun i => Fin (a.dim i) → ℂ)) :
    layerTensorEquiv a (a.inflation ⟨_, stdToAut_layer_mem a x⟩ w) =
      stdType (layerDatum a) x (layerTensorEquiv a w) := by
  have key : (layerTensorEquiv a).toLinearMap ∘ₗ a.inflation ⟨_, stdToAut_layer_mem a x⟩ =
      stdType (layerDatum a) x ∘ₗ (layerTensorEquiv a).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    refine ((congrArg (layerTensorEquiv a) (inflation_tprod a _ v)).trans
      (layerTensorEquiv_tprod a _)).trans ?_
    refine Eq.trans ?_ (congrArg (stdType (layerDatum a) x) (layerTensorEquiv_tprod a v)).symm
    refine Eq.trans ?_ (stdType_layer_tprod a x _).symm
    congr 1
    funext i
    have h := (factorEquiv a (Fin.revPerm i)).toIntertwiningMap.isIntertwining _ _
      (L.layerReduction a.basis ⟨_, stdToAut_layer_mem a x⟩ (Fin.revPerm i)) (v (Fin.revPerm i))
    exact h.trans (congrArg (fun g => (FiniteRep.VirtualCharacter.rep
      ((layerDatum a).label i).val).ρ g ((factorEquiv a (Fin.revPerm i)) (v (Fin.revPerm i))))
      (layerReduction_eq_leviProjection a x i))
  exact LinearMap.congr_fun key w

end Langlands.BushnellKutzko.SplitTypeJacquet
