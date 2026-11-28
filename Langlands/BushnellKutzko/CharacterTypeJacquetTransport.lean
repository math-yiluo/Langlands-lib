import Langlands.BushnellKutzko.DiagonalSplitTypeJacquet

/-! # From `Aut_F(F^n)` to `GL_n(F)` for types given by a character

A pair `(K, ρ)` in `GL_n(F)` whose transport to `Aut_F(F^n)` is isomorphic to a character `ϑ`
of a subgroup `K'`, contained in an admissible representation `π`, gives a nonzero
finite-dimensional `ϑ`-isotypic subspace of `π` that is not contained in the relations of
`ker ϑ`. If no such subspace is contained in the relations of some block unipotent group
`1 + e₁ A e₂`, then `π` has a nonzero Jacquet module for a proper parabolic subgroup. -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uπ uρ

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

local notation "GLn" => GeneralLinear n F
local notation "A" => Module.End F (Fin n → F)
local notation "Aut" => (Module.End F (Fin n → F))ˣ
local notation "toAut" => (Matrix.GeneralLinearGroup.toLin : GeneralLinear n F ≃* Aut)

/-- **Jacquet nonvanishing from a character type.** Let `π` be an admissible smooth
representation of `GL_n(F)` containing a pair `(K, ρ)` on a compact open subgroup whose
transport to `Aut_F(F^n)` is isomorphic to a character `χ` of `K'`. Suppose that for every
representation `π'` of `Aut_F(F^n)` whose `χ`-isotypic subspace is finite-dimensional and not
contained in the relations of `ker χ`, there are complementary idempotents `e₁, e₂ ≠ 0` such
that this subspace is not contained in the relations of `1 + e₁ A e₂`. Then `π` has a
nonzero Jacquet module for a conjugate of the unipotent radical of a proper standard
parabolic subgroup. -/
abbrev CharacterTypeJacquetTransportStatement : Prop :=
  ∀ (π : SmoothRep.{0, uF, uπ} ℂ GLn) (_hadm : IsAdmissible π.representation)
    {K : Subgroup GLn} (ρ : SmoothRep.{0, uF, uρ} ℂ K) {K' : Subgroup Aut} (χ : K' →* ℂˣ)
    (_hiso : IsPairIsomorphic (glRepresentationToAut ρ) (characterRepresentation χ))
    (_hK : IsCompact (K : Set GLn)) (_hKo : IsOpen (K : Set GLn)) (_hc : ContainsType π ρ)
    (_hmain : ∀ (π' : Representation ℂ Aut π)
      [FiniteDimensional ℂ (characterSubspace π' K' χ)],
      ¬ characterSubspace π' K' χ ≤ Jacquet.relations π' (χ.ker.map K'.subtype) →
      ∃ (e₁ e₂ : A) (h₂₁ : e₂ * e₁ = 0), e₁ + e₂ = 1 ∧ e₁ * e₂ = 0 ∧ e₁ ≠ 0 ∧ e₂ ≠ 0 ∧
        ¬ characterSubspace π' K' χ ≤ Jacquet.relations π' (blockUnipotent e₁ e₂ h₂₁ ⊤)),
    ∃ B : GeneralLinear.BlockShape n, B.parabolic F ≠ ⊤ ∧ ∃ g : GLn,
      ¬ Subsingleton (Jacquet.Coinvariants π.representation (B.conjugateUnipotent g))

theorem jacquet_nonvanishing_of_characterType : CharacterTypeJacquetTransportStatement (F := F) (n := n) := by
  intro π hadm K ρ K' χ hiso hK hKo hc hmain
  classical
  obtain ⟨hKU, ⟨E⟩⟩ := hiso
  let U := K'
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
  have hiso' : ∀ v : π, v ∈ characterSubspace π' U χ ↔
      v ∈ characterSubspace π.representation K ϑ := by
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
  obtain ⟨e₁, e₂, h₂₁, hsum, h12, hne₁, hne₂, hmain'⟩ := hmain π' h₀
  obtain ⟨B, hB, g, hBg⟩ := exists_blockShape_conjugateUnipotent_le hsum h12 h₂₁ hne₁ hne₂
  refine ⟨B, hB, g, Jacquet.not_subsingleton_of_not_le_relations π.representation _
    (P := characterSubspace π' U χ) fun h => hmain' (h.trans ?_)⟩
  rw [relations_comp_mulEquiv]
  exact Jacquet.relations_mono _ hBg

end Langlands.BushnellKutzko.SplitBlocks
