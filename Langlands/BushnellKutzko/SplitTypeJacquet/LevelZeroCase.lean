import Langlands.BushnellKutzko.SplitTypeJacquet.LevelZeroTransport
import Langlands.BushnellKutzko.SplitTypeJacquet.StandardJacquet
import Langlands.BushnellKutzko.GLSplitTypes
import Langlands.BushnellKutzko.TypeContainment
import Langlands.Representation.CuspidalSupport.GroupTransport

/-! # Jacquet nonvanishing for split types of level `(0, 0)`

An admissible smooth complex representation of `GL_n(F)` containing a split type of level
`(0, 0)` has a nonzero Jacquet module along a conjugate of the unipotent radical of a proper
standard block parabolic. In the coordinates of a basis adapted to the lattice chain, the type
becomes the standard type of a finite cuspidal datum with two different labels, and
`standard_jacquet` applies to the conjugated representation. -/

open ValuativeRel Matrix Langlands.GeneralLinear Langlands.Geometric

noncomputable section

namespace Langlands.BushnellKutzko.SplitTypeJacquet

universe uF uV uπ uρ

section Conjugation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Conjugation by a fixed element as a topological group automorphism. -/
def conjContinuous (g : G) : G ≃ₜ* G where
  toMulEquiv := MulAut.conj g
  continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem relations_comp_conj (ρ : Representation ℂ G V) (g : G) (N : Subgroup G) :
    Jacquet.relations (ρ.comp (MulAut.conj g).toMonoidHom) N =
      Jacquet.relations ρ (N.map (MulAut.conj g).toMonoidHom) := by
  rw [Jacquet.relations_eq_span, Jacquet.relations_eq_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨n, v⟩, rfl⟩
    exact Submodule.subset_span ⟨(⟨_, Subgroup.mem_map_of_mem _ n.2⟩, v), rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨⟨⟨_, ⟨n, hn, rfl⟩⟩, v⟩, rfl⟩
    exact Submodule.subset_span ⟨(⟨n, hn⟩, v), rfl⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem subsingleton_coinvariants_iff (ρ : Representation ℂ G V) (N : Subgroup G) :
    Subsingleton (Jacquet.Coinvariants ρ N) ↔ ∀ v, v ∈ Jacquet.relations ρ N := by
  constructor
  · intro h v
    rw [← Jacquet.mk_eq_zero]
    exact Subsingleton.elim _ _
  · intro h
    refine ⟨fun x y => ?_⟩
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ N x
    obtain ⟨w, rfl⟩ := Jacquet.mk_surjective ρ N y
    rw [(Jacquet.mk_eq_zero ρ N v).mpr (h v), (Jacquet.mk_eq_zero ρ N w).mpr (h w)]

end Conjugation

theorem conjugateUnipotent_map_conj {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
    (B : BlockShape n) (g h : GeneralLinear n F) :
    (B.conjugateUnipotent h).map (MulAut.conj g).toMonoidHom = B.conjugateUnipotent (g * h) := by
  rw [BlockShape.conjugateUnipotent, BlockShape.conjugateUnipotent, Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- A representation of `GL_n(F)` has a nonzero Jacquet module along a conjugate of the
unipotent radical of a proper standard block parabolic. -/
def HasProperJacquetModule {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F) V) : Prop :=
  ∃ B : BlockShape n, B.parabolic F ≠ ⊤ ∧ ∃ g : GeneralLinear n F,
    ¬ Subsingleton (Jacquet.Coinvariants ρ (B.conjugateUnipotent g))

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- **Jacquet nonvanishing for split types of level `(0, 0)`.** -/
theorem levelZeroSplitType_jacquet {n : ℕ} (hn : 0 < n)
    (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F)) (hadm : IsAdmissible π.representation)
    {K : Subgroup (GeneralLinear n F)} (ρ : SmoothRep.{0, uF, uρ} ℂ K)
    (hρ : IsLevelZeroSplitType (V := Fin n → F) (glRepresentationToAut ρ))
    (hc : ContainsType π ρ) : HasProperJacquetModule π.representation := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨L, a, hdiff, -, hK, ⟨e0⟩⟩ := hρ
  obtain ⟨f0, hf0⟩ := hc
  set g₀ := layerChange a with hg₀
  let π' := π.representation.comp (MulAut.conj g₀).toMonoidHom
  -- the conjugate of a standard element lies in `K`
  have hk : ∀ x : J0 F (blkOf (layerShape a)), g₀ * (x : GL (Fin (m + 1)) F) * g₀⁻¹ ∈ K := by
    intro x
    have hmem : Matrix.GeneralLinearGroup.toLin (g₀ * (x : GL (Fin (m + 1)) F) * g₀⁻¹) ∈
        glSubgroupToAut K := by
      rw [hK, hg₀, toLin_layerChange_conj]
      exact stdToAut_layer_mem a x
    exact (Subgroup.mem_map_iff_mem (Matrix.GeneralLinearGroup.toLin :
      GeneralLinear (m + 1) F ≃* (Module.End F (Fin (m + 1) → F))ˣ).injective).mp hmem
  have hσ : ∀ x : J0 F (blkOf (layerShape a)),
      ((glRepresentationToAut ρ).comp (MulEquiv.subgroupCongr hK).symm.toMonoidHom)
        ⟨_, stdToAut_layer_mem a x⟩ = ρ.representation ⟨_, hk x⟩ := by
    intro x
    have he : (MulEquiv.subgroupCongr hK).symm ⟨_, stdToAut_layer_mem a x⟩ =
        glSubgroupToAutEquiv K ⟨_, hk x⟩ := by
      apply Subtype.ext
      change stdToAut L a.basis (unif_irreducible (F := F)) (layerEquiv a) x =
        Matrix.GeneralLinearGroup.toLin (g₀ * (x : GL (Fin (m + 1)) F) * g₀⁻¹)
      rw [hg₀, toLin_layerChange_conj]
    change glRepresentationToAut ρ ((MulEquiv.subgroupCongr hK).symm
      ⟨_, stdToAut_layer_mem a x⟩) = _
    rw [he, glRepresentationToAut_apply]
  -- the transported intertwiner from the standard type
  let F' : (layerDatum a).leviRep →ₗ[ℂ] π :=
    f0.toLinearMap ∘ₗ e0.symm.toLinearEquiv.toLinearMap ∘ₗ
      (layerTensorEquiv a).symm.toLinearMap
  have hF' : ∀ (x : J0 F (blkOf (layerDatum a).shape)) (w : (layerDatum a).leviRep),
      F' (stdType (layerDatum a) x w) = π' x (F' w) := by
    intro x w
    have h1 : (layerTensorEquiv a).symm (stdType (layerDatum a) x w) =
        a.inflation ⟨_, stdToAut_layer_mem a x⟩ ((layerTensorEquiv a).symm w) := by
      rw [LinearEquiv.symm_apply_eq]
      exact ((layerTensorEquiv_inflation a x ((layerTensorEquiv a).symm w)).trans
        (congrArg (stdType (layerDatum a) x) (LinearEquiv.apply_symm_apply _ w))).symm
    have h2 := e0.symm.toIntertwiningMap.isIntertwining _ _ ⟨_, stdToAut_layer_mem a x⟩
      ((layerTensorEquiv a).symm w)
    rw [hσ x] at h2
    have h3 := f0.isIntertwining _ _ ⟨_, hk x⟩ (e0.symm ((layerTensorEquiv a).symm w))
    calc F' (stdType (layerDatum a) x w)
        = f0 (e0.symm (a.inflation ⟨_, stdToAut_layer_mem a x⟩
            ((layerTensorEquiv a).symm w))) := by
          change f0 (e0.symm ((layerTensorEquiv a).symm (stdType (layerDatum a) x w))) = _
          rw [h1]
      _ = f0 (ρ.representation ⟨_, hk x⟩ (e0.symm ((layerTensorEquiv a).symm w))) := by
          exact congrArg f0 h2
      _ = π' x (F' w) := h3
  have hF'0 : F' ≠ 0 := by
    intro h
    apply hf0
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    have hz : F' (layerTensorEquiv a (e0 z)) = f0 z := by
      change f0 (e0.symm.toLinearEquiv ((layerTensorEquiv a).symm (layerTensorEquiv a (e0 z)))) =
        f0 z
      rw [LinearEquiv.symm_apply_apply]
      exact congrArg f0 (Representation.Equiv.symm_apply_apply e0 z)
    change f0 z = 0
    rw [← hz, h]
    rfl
  have hadm' : IsAdmissible π' :=
    isAdmissible_comp_continuousMulEquiv π.representation (conjContinuous g₀) hadm
  obtain ⟨B, hB, g, hcoinv⟩ := standard_jacquet π' hadm' (layerDatum a)
    (exists_blockLabel_ne a hdiff) F' hF' hF'0
  refine ⟨B, hB, g₀ * g, fun hsub => hcoinv ?_⟩
  rw [subsingleton_coinvariants_iff] at hsub ⊢
  intro v
  change v ∈ Jacquet.relations (π.representation.comp (MulAut.conj g₀).toMonoidHom) _
  rw [relations_comp_conj, conjugateUnipotent_map_conj]
  exact hsub v

end Langlands.BushnellKutzko.SplitTypeJacquet
