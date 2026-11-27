import Langlands.BushnellKutzko.LevelZeroJacquet
import Langlands.BushnellKutzko.LevelZeroMatrixCoordinates
import Langlands.BushnellKutzko.GLSimpleTypes
import Langlands.BushnellKutzko.SimpleTypeTopology
import Langlands.BushnellKutzko.TypeContainment
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! # Jacquet modules of representations containing a non-maximal level-zero simple type -/

open ValuativeRel Matrix Langlands.Jacquet

noncomputable section

namespace Langlands.BushnellKutzko.LevelZero

universe uF uρ uπ

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {e f : ℕ}

/-- Residues of the diagonal blocks of the two-block element `diag(unipLift r Z, 1)` on the
blocks `0, m`. -/
theorem residue_pairGL_unipLift (he : 0 < e) {m : Fin e} (hm : (⟨0, he⟩ : Fin e) < m) (r : ℕ)
    (Z : Matrix (Fin f) (Fin f) 𝓀[F]) (i : Fin e) (a a' : Fin f)
    (h : valuation F (((pairGL hm.ne (diagU (unipLift r Z) 1) : GL (Fin f × Fin e) F) :
      Matrix (Fin f × Fin e) (Fin f × Fin e) F) (a, i) (a', i)) ≤ 1) :
    IsLocalRing.residue 𝒪[F] ⟨((pairGL hm.ne (diagU (unipLift r Z) 1) : GL (Fin f × Fin e) F) :
      Matrix (Fin f × Fin e) (Fin f × Fin e) F) (a, i) (a', i), h⟩ =
      (((Pi.mulSingle (⟨0, he⟩ : Fin e) (cornerU r Z) : Fin e → GeneralLinear f 𝓀[F]) i :
        GeneralLinear f 𝓀[F]) : Matrix (Fin f) (Fin f) 𝓀[F]) a a' := by
  rw [← res_of_le h, coe_pairGL]
  by_cases hi0 : i = ⟨0, he⟩
  · subst hi0
    have h1 : valuation F ((1 : Matrix (Fin f) (Fin f) F) a a') ≤ 1 := by
      by_cases h' : a = a' <;> simp [Matrix.one_apply, h']
    rw [pairEmb_ll, Pi.mulSingle_eq_same, coe_cornerU, coe_diagU, Matrix.fromBlocks_apply₁₁,
      unipLift, coe_unipU, Matrix.add_apply, Matrix.add_apply, cornerMat_apply,
      res_add h1 (truncLift_le_one r Z a a')]
    congr 1
    · by_cases h' : a = a' <;> simp [Matrix.one_apply, h']
    · unfold truncLift
      split_ifs <;> simp
  · rw [Pi.mulSingle_eq_of_ne hi0]
    by_cases him : i = m
    · subst him
      rw [pairEmb_rr, coe_diagU, Matrix.fromBlocks_apply₂₂]
      by_cases h' : a = a' <;> simp [h']
    · rw [pairEmb_rest_left hm.ne _ _ _ hi0 him]
      by_cases h' : a = a' <;> simp [Matrix.one_apply, h']

/-- **BK93 (7.3.2) and the remark after it, kind (b).** A smooth representation of `GL_n(F)`
containing a simple type exhibited by level-zero data of period `e ≥ 2` has a nonzero Jacquet
module along a conjugate of the unipotent radical of a proper standard block parabolic, namely
the one of shape `(f, n - f)` conjugated by the change of basis to an adapted basis. -/
theorem levelZero_not_subsingleton_jacquet {n : ℕ} (hn : 0 < n)
    {J : Subgroup (GeneralLinear n F)} (ρ : SmoothRep.{0, uF, uρ} ℂ J)
    (L : LatticeChain 𝒪[F] F (Fin n → F)) (e : ℕ)
    (hd : IsLevelZeroSimpleTypeData (W := (ρ : Type uρ)) L e (glRepresentationToAut ρ))
    (he2 : 2 ≤ e) (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F)) (hc : ContainsType π ρ) :
    ∃ (B : GeneralLinear.BlockShape n) (g : GeneralLinear n F), B.parabolic F ≠ ⊤ ∧
      ¬ Subsingleton (Coinvariants π.representation (B.conjugateUnipotent g)) := by
  classical
  let _ : Fintype 𝓀[F] := Fintype.ofFinite _
  obtain ⟨-, he, f, d, σ₀, -, hσcusp, b, φ, hred, hρ1, hJ, ⟨ε⟩⟩ := hd
  have he' : L.period = e := he.symm
  have hepos : 0 < e := by omega
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  -- dimensions
  have hcard : n = f * e := by
    have h := Module.finrank_eq_card_basis (adaptedBasis L b hϖ he')
    rw [Module.finrank_fin_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
    exact h
  have hn' : e * f = n := by rw [hcard, mul_comm]
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, zero_mul] at hcard; omega
    · exact h0
  have hfn : f < n := by
    rw [hcard]
    exact (Nat.lt_mul_iff_one_lt_right hf).mpr (by omega)
  -- the groups
  set Ψ := stdToAut L b hϖ he' with hΨ
  set Φ := stdToGL L b hϖ he' with hΦ
  have hU0 : ∀ x : GL (Fin f × Fin e) F, x ∈ J0 F e f → Ψ x ∈ L.unitFiltration 0 :=
    fun x hx => (stdToAut_mem_unitFiltration_zero_iff L b hϖ he' x).mpr hx
  have hΦJ : ∀ x : GL (Fin f × Fin e) F, x ∈ J0 F e f → Φ x ∈ J := by
    intro x hx
    have h := hU0 x hx
    rw [← hJ] at h
    obtain ⟨j, hj, hjx⟩ := h
    have : j = Φ x := Matrix.GeneralLinearGroup.toLin.injective
      (hjx.trans (toLin_stdToGL L b hϖ he' x).symm)
    exact this ▸ hj
  -- the representation in standard coordinates
  let ι : J0 F e f →* J :=
    { toFun := fun x => ⟨Φ (x : GL (Fin f × Fin e) F), hΦJ _ x.2⟩
      map_one' := Subtype.ext (map_one Φ)
      map_mul' := fun x y => Subtype.ext (map_mul Φ (x : GL (Fin f × Fin e) F) y) }
  let ρstd : Representation ℂ (J0 F e f) ρ := ρ.representation.comp ι
  let πstd : Representation ℂ (GL (Fin f × Fin e) F) π := π.representation.comp Φ.toMonoidHom
  -- the equivalence with the tensor power
  let ρA := (glRepresentationToAut ρ).comp (MulEquiv.subgroupCongr hJ).symm.toMonoidHom
  let σT := (tensorPowerRepresentation σ₀ e).comp φ
  let A := ε.toLinearEquiv
  have hA : ∀ (y : L.unitFiltration 0) (w : ρ), A (ρA y w) = σT y (A w) := fun y w =>
    Representation.IntertwiningMap.isIntertwining _ _ ε.toIntertwiningMap y w
  have : FiniteDimensional ℂ ρ := LinearEquiv.finiteDimensional A.symm
  have hρA : ∀ (x : GL (Fin f × Fin e) F) (hx : x ∈ J0 F e f),
      ρA ⟨Ψ x, hU0 x hx⟩ = ρstd ⟨x, hx⟩ := by
    intro x hx
    change glRepresentationToAut ρ ⟨Ψ x, _⟩ = ρ.representation ⟨Φ x, hΦJ x hx⟩
    rw [← glRepresentationToAut_apply]
    congr 1
    apply Subtype.ext
    exact (toLin_stdToGL L b hϖ he' x).symm
  have hρstd : ∀ (x : GL (Fin f × Fin e) F) (hx : x ∈ J0 F e f) (w : ρ),
      ρstd ⟨x, hx⟩ w = A.symm (σT ⟨Ψ x, hU0 x hx⟩ (A w)) := by
    intro x hx w
    rw [← hρA x hx, ← hA, LinearEquiv.symm_apply_apply]
  -- the hypotheses of the standard theorem
  have hρ1' : ∀ x : J0 F e f, (x : GL (Fin f × Fin e) F) ∈ J1 F e f → ρstd x = 1 := by
    intro x hx1
    have h1 : Ψ x ∈ L.unitFiltration 1 :=
      (stdToAut_mem_unitFiltration_one_iff L b hϖ he' x).mpr hx1
    have h := hρ1 (glSubgroupToAutEquiv J (ι x)) (by
      change Matrix.GeneralLinearGroup.toLin (Φ x) ∈ L.unitFiltration 1
      rw [toLin_stdToGL]
      exact h1)
    rw [glRepresentationToAut_apply] at h
    exact h
  have hcusp : ∀ (m : Fin e) (hm : (⟨0, hepos⟩ : Fin e) < m) (r : ℕ), 0 < r → r < f →
      ∑ Z : Matrix (Fin f) (Fin f) 𝓀[F],
        ρstd ⟨pairGL hm.ne (diagU (unipLift r Z) 1),
          diagU_mem_J0 hm (isIntGL_unipLift r Z) isIntGL_one⟩ = 0 := by
    intro m hm r hr0 hrf
    have hφx : ∀ Z : Matrix (Fin f) (Fin f) 𝓀[F],
        φ ⟨Ψ (pairGL hm.ne (diagU (unipLift r Z) 1)),
          hU0 _ (diagU_mem_J0 hm (isIntGL_unipLift r Z) isIntGL_one)⟩ =
        Pi.mulSingle (⟨0, hepos⟩ : Fin e) (cornerU r Z) := by
      intro Z
      funext i
      ext a a'
      rw [layerReduction_entry L b hϖ he' _ hred _
        (diagU_mem_J0 hm (isIntGL_unipLift r Z) isIntGL_one), residue_pairGL_unipLift hepos hm r Z i a a']
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    simp only [hρstd]
    rw [← map_sum, ← LinearMap.sum_apply]
    have hσ : ∑ Z : Matrix (Fin f) (Fin f) 𝓀[F],
        σT ⟨Ψ (pairGL hm.ne (diagU (unipLift r Z) 1)),
          hU0 _ (diagU_mem_J0 hm (isIntGL_unipLift r Z) isIntGL_one)⟩ = 0 := by
      change ∑ Z : Matrix (Fin f) (Fin f) 𝓀[F], tensorPowerRepresentation σ₀ e
        (φ ⟨Ψ (pairGL hm.ne (diagU (unipLift r Z) 1)),
          hU0 _ (diagU_mem_J0 hm (isIntGL_unipLift r Z) isIntGL_one)⟩) = 0
      simp only [hφx]
      exact sum_tensorPower_cornerU_eq_zero hσcusp hr0 hrf _
    rw [hσ, LinearMap.zero_apply, map_zero]
  obtain ⟨Fc, hFc⟩ := hc
  let φstd : ρ →ₗ[ℂ] π := Fc.toLinearMap
  have hφ : ∀ (x : J0 F e f) (w : ρ), φstd (ρstd x w) = πstd x (φstd w) := fun x w =>
    Representation.IntertwiningMap.isIntertwining _ _ Fc (ι x) w
  have hφ0 : φstd ≠ 0 := by
    intro h0
    apply hFc
    ext w
    exact LinearMap.congr_fun h0 w
  -- the compact open subgroup `U^1(𝔄)` in standard coordinates
  let _ : TopologicalSpace (Module.End F (Fin n → F)) := endTopology
  have hcoeC : ∀ y : GeneralLinear n F,
      generalLinearToLinContinuous y = Matrix.GeneralLinearGroup.toLin y := fun y => rfl
  have hJ1set : ((J1 F e f : Subgroup (GL (Fin f × Fin e) F)) : Set (GL (Fin f × Fin e) F)) =
      Φ ⁻¹' (generalLinearToLinContinuous ⁻¹'
        (L.unitFiltration 1 : Set (Module.End F (Fin n → F))ˣ)) := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe, hcoeC, hΦ, toLin_stdToGL]
    exact (stdToAut_mem_unitFiltration_one_iff L b hϖ he' x).symm
  have hJ0set : ((J0 F e f : Subgroup (GL (Fin f × Fin e) F)) : Set (GL (Fin f × Fin e) F)) =
      Φ ⁻¹' (generalLinearToLinContinuous ⁻¹'
        (L.unitFiltration 0 : Set (Module.End F (Fin n → F))ˣ)) := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe, hcoeC, hΦ, toLin_stdToGL]
    exact (stdToAut_mem_unitFiltration_zero_iff L b hϖ he' x).symm
  have hopen : IsOpen ((J1 F e f : Subgroup (GL (Fin f × Fin e) F)) :
      Set (GL (Fin f × Fin e) F)) := by
    rw [hJ1set]
    exact ((isOpen_unitFiltration L 1).preimage generalLinearToLinContinuous.continuous).preimage
      (continuous_stdToGL L b hϖ he')
  let K : OpenSubgroup (GL (Fin f × Fin e) F) := { J1 F e f with isOpen' := hopen }
  have hKJ : K.toSubgroup = J1 F e f := rfl
  have hK : IsCompact (K : Set (GL (Fin f × Fin e) F)) := by
    have h0 : IsCompact ((J0 F e f : Subgroup (GL (Fin f × Fin e) F)) :
        Set (GL (Fin f × Fin e) F)) := by
      rw [hJ0set]
      exact (stdToGLContinuous L b hϖ he').toHomeomorph.isCompact_preimage.mpr
        (generalLinearToLinContinuous.toHomeomorph.isCompact_preimage.mpr
          (isCompact_unitFiltration_zero L))
    exact h0.of_isClosed_subset K.isClosed (J1_le_J0 (F := F) (e := e) (f := f))
  have hπstd : IsSmooth πstd := isSmooth_comp _ (continuous_stdToGL L b hϖ he') π.isSmooth
  -- the standard theorem
  have hns := not_subsingleton_coinvariants_coarseN πstd hπstd K hK hϖ hepos hKJ ρstd hρ1' hcusp
    φstd hφ hφ0
  -- transport of the Jacquet module
  set B := twoBlockShape hf hfn
  set g := changeGL L b hϖ he' hn'
  refine ⟨B, g, twoBlockShape_parabolic_ne_top hf hfn, fun hsc => hns ?_⟩
  have hle : relations π.representation (B.conjugateUnipotent g) ≤
      relations πstd (coarseN F f hepos) := by
    rw [relations_eq_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨⟨y, hy⟩, v⟩, rfl⟩
    obtain ⟨x, hx, rfl⟩ :=
      exists_mem_coarseN_of_mem_conjugateUnipotent L b hϖ he' hn' hepos hf hfn hy
    exact sub_mem_relations πstd (coarseN F f hepos) ⟨x, hx⟩ v
  have hall : ∀ v : π, v ∈ relations πstd (coarseN F f hepos) := fun v =>
    hle ((mk_eq_zero _ _ v).mp (Subsingleton.elim _ _))
  refine ⟨fun z₁ z₂ => ?_⟩
  obtain ⟨v₁, rfl⟩ := mk_surjective πstd (coarseN F f hepos) z₁
  obtain ⟨v₂, rfl⟩ := mk_surjective πstd (coarseN F f hepos) z₂
  rw [(mk_eq_zero _ _ v₁).mpr (hall v₁), (mk_eq_zero _ _ v₂).mpr (hall v₂)]

end Langlands.BushnellKutzko.LevelZero
