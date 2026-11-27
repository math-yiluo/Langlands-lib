import Langlands.BaseChange.TwistedCharacter.CompactDomination
import Langlands.AllField.Representation.Induction.BlockFactors
import Langlands.AllField.Representation.Parabolic.QuotientCompactProof
import Langlands.Group.GL.LocalFieldTopology

/-! # Fixed-vector detection on the factors of a normalized GL product -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear

universe v z

variable (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] {n : ℕ} (B : BlockShape n)

/-- At any ambient open level, a single choice of compact open level in each block
detects nonzero fixed vectors in all normalized products of that shape. -/
def InducedBlockFixedLevelStatement (K : OpenSubgroup (GeneralLinear n E)) : Prop :=
  ∃ J : ∀ i, OpenSubgroup (GeneralLinear (B.size i) E),
    (∀ i, IsCompact (J i : Set (GeneralLinear (B.size i) E))) ∧
    ∀ (V : Fin B.length → Type z) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
      (ρ : ∀ i, Representation ℂ (GeneralLinear (B.size i) E) (V i)),
      fixedVectors ((LocalFieldData.ofInstances E).normalizedProductInduced B ρ)
        K.toSubgroup ≠ ⊥ →
      ∀ i, fixedVectors (ρ i) (J i).toSubgroup ≠ ⊥

/-- Use the finite double-coset cover in the fixed-section model to choose the block levels
independently of the inducing representations. -/
theorem inducedBlockFixedLevel (K : OpenSubgroup (GeneralLinear n E)) :
    InducedBlockFixedLevelStatement.{v,z} E B K := by
  classical
  let T := LocalFieldData.ofInstances E
  let P := B.parabolic E
  let p := B.leviProjection E
  let : T2Space E := LocalFieldTopology.t2Space E
  let : CompactSpace (Induction.LeftQuotient P) :=
    AllField.Parabolic.parabolicQuotientCompact E T B
  let : ∀ i, T2Space (GeneralLinear (B.size i) E) :=
    fun i => LocalFieldTopology.generalLinear_t2Space E _
  let : ∀ i, LocallyCompactSpace (GeneralLinear (B.size i) E) :=
    fun i => LocalFieldTopology.generalLinear_locallyCompactSpace E _
  let : ∀ i, TotallyDisconnectedSpace (GeneralLinear (B.size i) E) :=
    fun i => LocalFieldTopology.generalLinear_totallyDisconnectedSpace E _
  have hpo : IsOpenMap p := isOpenMap_snd.comp (B.decompositionHomeomorph E).isOpenMap
  obtain ⟨U, _, hU⟩ := smoothInducedFixedVanishing.{v,v,z} P p hpo K
  let N : OpenSubgroup (B.Levi E) := ⟨T.normOneLevi B, T.isOpen_normOneLevi B⟩
  let H (i : Fin B.length) : OpenSubgroup (GeneralLinear (B.size i) E) :=
    OpenSubgroup.comap
      (MonoidHom.mulSingle (fun j => GeneralLinear (B.size j) E) i)
      (continuous_mulSingle i) (U ⊓ N)
  have hlevels (i : Fin B.length) :
      ∃ J : OpenSubgroup (GeneralLinear (B.size i) E),
        J ≤ H i ∧ IsCompact (J : Set (GeneralLinear (B.size i) E)) := by
    obtain ⟨J, hJH, hJ, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance
      (GeneralLinear (B.size i) E) ∅ (H i)
    exact ⟨J, hJH, hJ⟩
  choose J hJH hJ using hlevels
  let L := Subgroup.pi Set.univ (fun i => (J i).toSubgroup)
  have hL : L ≤ (U ⊓ N).toSubgroup := by
    apply Subgroup.pi_le_iff.mpr
    rintro i _ ⟨g, hg, rfl⟩
    exact hJH i hg
  refine ⟨J, hJ, ?_⟩
  intro V _ _ ρ hρ i hbot
  let Ξ := B.blockTensor ρ
  have hzero : fixedVectors Ξ L = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    obtain ⟨y, hy⟩ := FiniteTensor.fixedVectors_external_le ρ
      (fun j => (J j).toSubgroup) hx
    have hmap : PiTensorProduct.map (fun j => (fixedVectors (ρ j) (J j).toSubgroup).subtype) =
        0 := by
      apply PiTensorProduct.ext
      ext w
      rw [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod,
        LinearMap.compMultilinearMap_apply, LinearMap.zero_apply]
      apply (PiTensorProduct.tprod ℂ).map_coord_zero i
      exact (Submodule.eq_bot_iff _).mp hbot _ (w i).property
    rw [hmap, LinearMap.zero_apply] at hy
    exact hy.symm
  let Ξ' := twist (T.leviHalfModulus B) Ξ
  have hsmall : fixedVectors Ξ' U.toSubgroup ≤ fixedVectors Ξ L := by
    intro x hx g
    have hUg : g.val ∈ U := (hL g.property).1
    have hNg : g.val ∈ T.normOneLevi B := (hL g.property).2
    have hmod : T.leviHalfModulus B g.val = 1 :=
      (T.leviHalfModulus_eq_one B _).mpr
        (MonoidHom.mem_ker.mp (T.normOneLevi_le_ker_leviModulus B hNg))
    have h := hx ⟨g.val, hUg⟩
    change (T.leviHalfModulus B g.val : ℂ) • Ξ g.val x = x at h
    change Ξ g.val x = x
    simpa only [hmod, Units.val_one, one_smul] using h
  have hUzero : fixedVectors Ξ' U.toSubgroup = ⊥ := le_bot_iff.mp (hsmall.trans_eq hzero)
  apply hρ
  change fixedVectors (Induction.smoothInduced P ((twist (T.leviHalfModulus B) Ξ).comp p))
      K.toSubgroup = ⊥
  exact hU _ Ξ' hUzero

end Langlands.BaseChange
