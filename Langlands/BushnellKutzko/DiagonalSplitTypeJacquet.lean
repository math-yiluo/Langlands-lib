import Langlands.BushnellKutzko.IdempotentBlockShape
import Langlands.BushnellKutzko.GLSplitTypes
import Langlands.BushnellKutzko.TypeContainment
import Langlands.Representation.Jacquet.CharacterAveraging

/-! # Jacquet nonvanishing for a split type of level `(x, x)` in `GL_n(F)`

Transport of `SplitBlocks.SplitBlockData.not_le_relations_blockUnipotent` from `Aut_F(F^n)`
to the matrix group, for an irreducible admissible representation containing a split type of
level `(x, x)` with `x > 0` (Bushnell–Kutzko (8.2.5)(iv) in the case `x = y`).
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uπ uρ uW

/-! ### Relations along a group isomorphism -/

section Generic

variable {H G : Type*} [Group H] [Group G] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Coinvariant relations of a subgroup correspond along a group isomorphism. -/
theorem relations_comp_mulEquiv (e : H ≃* G) (ρ : Representation ℂ G W) (N : Subgroup H) :
    Jacquet.relations (ρ.comp e.toMonoidHom) N = Jacquet.relations ρ (N.map e.toMonoidHom) := by
  rw [Jacquet.relations_eq_span, Jacquet.relations_eq_span]
  congr 1
  ext v
  constructor
  · rintro ⟨⟨n, w⟩, rfl⟩
    exact ⟨⟨⟨e n, n, n.2, rfl⟩, w⟩, rfl⟩
  · rintro ⟨⟨⟨g, n, hn, rfl⟩, w⟩, rfl⟩
    exact ⟨⟨⟨n, hn⟩, w⟩, rfl⟩

end Generic

/-! ### Isotypic vectors of a compact subgroup are not relations of the kernel -/

section Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- For a smooth representation, a compact subgroup `K` and a character `ϑ` of `K` with open
kernel, a nonzero `ϑ`-isotypic vector is not a coinvariant relation of `ker ϑ`: the
`ϑ`-twisted average over `K` fixes the vector and kills these relations. -/
theorem not_mem_relations_ker {ρ : Representation ℂ G W} (hρ : IsSmooth ρ) {K : Subgroup G}
    (hK : IsCompact (K : Set G)) {ϑ : K →* ℂˣ} (hϑ : IsOpen (ϑ.ker : Set K)) {v : W}
    (hv : v ∈ characterSubspace ρ K ϑ) (hv0 : v ≠ 0) :
    v ∉ Jacquet.relations ρ (ϑ.ker.map K.subtype) := by
  intro hrel
  have hH : IsCompact ((⊤ : OpenSubgroup K) : Set K) := by
    simpa using isCompact_iff_isCompact_univ.mp hK
  let P := Jacquet.Localization.characterAverage hρ hϑ ⊤ hH
  have hkill : Jacquet.relations ρ (ϑ.ker.map K.subtype) ≤ LinearMap.ker P := by
    rw [Jacquet.relations_eq_span, Submodule.span_le]
    rintro _ ⟨⟨⟨g, k, hk, rfl⟩, w⟩, rfl⟩
    have h := Jacquet.Localization.characterAverage_relation hρ hϑ ⊤ hH
      (n := k) (by simp) w
    have hk1 : (ϑ k : ℂ) = 1 := by
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hk
      rw [hk, Units.val_one]
    rw [hk1, one_smul] at h
    exact h
  have hfix : P v = v := by
    apply Compact.averageMap_id
    rw [fixedVectors, Representation.mem_invariants]
    intro h
    change Jacquet.Localization.twistedRestriction ρ K ϑ (h : K) v = v
    rw [Jacquet.Localization.twistedRestriction_apply, hv (h : K), smul_smul,
      inv_mul_cancel₀ (Units.ne_zero _), one_smul]
  apply hv0
  rw [← hfix]
  exact hkill hrel

end Topology

/-! ### The matrix group -/

section MatrixGroup

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

local notation "GLn" => GeneralLinear n F
local notation "A" => Module.End F (Fin n → F)
local notation "Aut" => (Module.End F (Fin n → F))ˣ
local notation "toAut" => (Matrix.GeneralLinearGroup.toLin : GeneralLinear n F ≃* Aut)

/-- **BK93 (8.2.5)(iv), level `(x, x)`.** An admissible smooth representation of `GL_n(F)`
containing a split type of level `(x, x)` with `x > 0` on a compact open subgroup has a
nonzero Jacquet module for a conjugate of the unipotent radical of a proper standard
two-block parabolic subgroup. -/
theorem diagonalSplitType_jacquet_nonvanishing {ψF : AddChar F ℂ}
    (π : SmoothRep.{0, uF, uπ} ℂ GLn) (hadm : IsAdmissible π.representation)
    {K : Subgroup GLn} (ρ : SmoothRep.{0, uF, uρ} ℂ K) {x : ℚ}
    (hρ : IsDiagonalPositiveSplitType (V := Fin n → F) ψF x (glRepresentationToAut ρ))
    (hK : IsCompact (K : Set GLn)) (hKo : IsOpen (K : Set GLn)) (hc : ContainsType π ρ) :
    ∃ B : GeneralLinear.BlockShape n, B.parabolic F ≠ ⊤ ∧ ∃ g : GLn,
      ¬ Subsingleton (Jacquet.Coinvariants π.representation (B.conjugateUnipotent g)) := by
  classical
  obtain ⟨hψ, S, hn, hsplit, hcop, -, hiso⟩ := hρ
  -- the character `ψ_b` and its defining formula
  set χ := filtrationTraceCharacter S.chain ψF hψ (m := S.n.toNat) (by omega) (b := S.b) (by
    rw [Int.toNat_of_nonneg hn.le]
    exact PureApproximation.mem_endFiltration_of_le_valuation S.chain
      (by exact_mod_cast S.valuation_ge)) with hχdef
  have hχ : ∀ g, (χ g : ℂ) = elementCharacter (traceCharacter ψF) S.b g :=
    filtrationTraceCharacter_apply _ _ _ _ _
  have hm : ((S.n.toNat : ℕ) : ℤ) = S.n := Int.toNat_of_nonneg hn.le
  have hm1 : 1 ≤ S.n.toNat := by omega
  have hb : S.b ∈ S.chain.endFiltration (-S.n) :=
    PureApproximation.mem_endFiltration_of_le_valuation S.chain (by exact_mod_cast S.valuation_ge)
  -- the block data of the split stratum
  have hhens : HenselianRing 𝒪[F] (Ring.jacobson 𝒪[F]) := by
    let := IsTopologicalAddGroup.rightUniformSpace F
    have := isUniformAddGroup_of_addCommGroup (G := F)
    have : IsAdicComplete 𝓂[F] 𝒪[F] := inferInstance
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    infer_instance
  have hcop' : Nat.Coprime S.n.natAbs S.chain.period := by
    have : S.n.natAbs = S.n.toNat := by omega
    rw [this]
    exact hcop
  obtain ⟨D⟩ := nonempty_splitBlockData S hsplit hb hn hcop'
  -- the pair `(K, ρ)` as a character of `U^n(𝔄)`
  obtain ⟨hKU, ⟨E⟩⟩ := hiso
  let U := S.chain.unitFiltration S.n.toNat
  let toU : K →* U := ((MulEquiv.subgroupCongr hKU).toMonoidHom.comp
    (glSubgroupToAutEquiv K).toMonoidHom)
  have htoU : ∀ k : K, ((toU k : U) : Aut) = toAut k := fun k => rfl
  let ofU : U → K := fun u => (glSubgroupToAutEquiv K).symm ((MulEquiv.subgroupCongr hKU).symm u)
  have htoU_ofU : ∀ u : U, toU (ofU u) = u := fun u => by
    simp [toU, ofU]
  have hofU : ∀ u : U, ((ofU u : K) : GLn) = (toAut).symm u := fun u => by
    have h := congrArg (fun w : U => ((w : Aut))) (htoU_ofU u)
    simp only [htoU] at h
    rw [← h, MulEquiv.symm_apply_apply]
  let ϑ : K →* ℂˣ := χ.comp toU
  have hscalar : ∀ (k : K) (w : ρ), ρ.representation k w = (ϑ k : ℂ) • w := by
    intro k w
    apply E.injective
    have h := Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap (toU k) w
    have hk : (glRepresentationToAut ρ).comp
        (MulEquiv.subgroupCongr hKU).symm.toMonoidHom (toU k) = ρ.representation k := by
      simp [toU, glRepresentationToAut]
    rw [hk] at h
    rw [map_smul]
    exact h
  -- a nonzero isotypic vector
  obtain ⟨f, hf⟩ := hc
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, f w₀ ≠ 0 := by
    by_contra! h
    exact hf (Representation.IntertwiningMap.ext (LinearMap.ext h))
  have hw₀0 : w₀ ≠ 0 := fun h => hw₀ (by rw [h, map_zero])
  set v₀ := f w₀ with hv₀
  have hv₀K : v₀ ∈ characterSubspace π.representation K ϑ := by
    intro k
    rw [hv₀]
    erw [← Representation.IntertwiningMap.isIntertwining _ _ f k w₀]
    rw [hscalar, map_smul]
  -- the representation of `Aut_F(F^n)`
  let π' : Representation ℂ Aut π := π.representation.comp (toAut).symm.toMonoidHom
  have hiso' : ∀ v : π, v ∈ characterSubspace π' U χ ↔ v ∈ characterSubspace π.representation K ϑ := by
    intro v
    constructor
    · intro hv k
      have h := hv (toU k)
      change π.representation ((toAut).symm (toU k : Aut)) v = _ at h
      rw [htoU, MulEquiv.symm_apply_apply] at h
      exact h
    · intro hv u
      have h := hv (ofU u)
      rw [hofU] at h
      change π.representation ((toAut).symm (u : Aut)) v = _
      rw [h]
      change ((χ (toU (ofU u)) : ℂ)) • v = _
      rw [htoU_ofU]
  -- `ker ϑ` is open in `K`
  obtain ⟨L₀, hL₀⟩ := ρ.isSmooth w₀
  have hL₀ker : L₀.toSubgroup ≤ ϑ.ker := by
    intro l hl
    have h1 : ρ.representation l w₀ = w₀ := hL₀ ⟨l, hl⟩
    rw [hscalar] at h1
    rw [MonoidHom.mem_ker]
    apply Units.ext
    have h2 : ((ϑ l : ℂ) - 1) • w₀ = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    rw [Units.val_one, ← sub_eq_zero]
    exact (smul_eq_zero.mp h2).resolve_right hw₀0
  have hker : IsOpen (ϑ.ker : Set K) := Subgroup.isOpen_mono hL₀ker L₀.isOpen
  -- finite dimensionality from admissibility
  let L : OpenSubgroup GLn := ⟨L₀.toSubgroup.map K.subtype, by
    change IsOpen ((L₀.toSubgroup.map K.subtype : Subgroup GLn) : Set GLn)
    rw [Subgroup.coe_map]
    exact hKo.isOpenMap_subtype_val _ L₀.isOpen⟩
  have hfin : Module.Finite ℂ (fixedVectors π.representation L.toSubgroup) := hadm.2 L
  have hle : characterSubspace π' U χ ≤ fixedVectors π.representation L.toSubgroup := by
    intro v hv
    rw [fixedVectors, Representation.mem_invariants]
    rintro ⟨_, l, hl, rfl⟩
    have h := (hiso' v).mp hv l
    rw [MonoidHom.mem_ker.mp (hL₀ker hl), Units.val_one, one_smul] at h
    exact h
  have : FiniteDimensional ℂ (characterSubspace π' U χ) :=
    Submodule.finiteDimensional_of_le hle
  -- the starting level
  have h₀ : ¬ characterSubspace π' U χ ≤ Jacquet.relations π' (χ.ker.map U.subtype) := by
    intro h
    have hmem := h ((hiso' v₀).mpr hv₀K)
    rw [relations_comp_mulEquiv] at hmem
    refine not_mem_relations_ker π.isSmooth hK hker hv₀K hw₀ (Jacquet.relations_mono _ ?_ hmem)
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨ofU u, ?_, ?_⟩
    swap
    · change ((ofU u : K) : GLn) = (toAut).symm (u : Aut)
      exact hofU u
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hu ⊢
    change χ (toU (ofU u)) = 1
    rw [htoU_ofU, hu]
  have hmain := D.not_le_relations_blockUnipotent hm1 χ hχ hm hb hψ π' h₀
  obtain ⟨B, hB, g, hBg⟩ := exists_blockShape_conjugateUnipotent_le D.add_eq D.mul_eq
    D.e₂_mul_e₁ D.e₁_ne D.e₂_ne
  refine ⟨B, hB, g, Jacquet.not_subsingleton_of_not_le_relations π.representation _
    (P := characterSubspace π' U χ) fun h => hmain (h.trans ?_)⟩
  rw [relations_comp_mulEquiv]
  exact Jacquet.relations_mono _ hBg

end MatrixGroup

end Langlands.BushnellKutzko.SplitBlocks
