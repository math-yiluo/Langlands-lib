import Langlands.BushnellKutzko.LatticeChainInsertion
import Langlands.BushnellKutzko.LevelZeroLayerReductionSurjective
import Langlands.Representation.Tensor.Finite

/-! # Refining a lattice chain at a non-cuspidal layer

Let `𝓛 = (L_j)` be an `𝔬_F`-lattice chain in `F^ι` of period `e`, with hereditary order `𝔄`,
and let `τ` be a complex representation of `Aut_F(F^ι)` on `W`. Choose `k_F`-bases of the
layers `L_i / L_{i+1}`, `0 ≤ i < e`, of dimensions `d_i`, and let `ρ_i` be complex
representations of `GL_{d_i}(k_F)` on nonzero spaces `Y_i`. Suppose that the external tensor
product `⊗_i Y_i` embeds in `W` compatibly, on restriction of `τ` to `U(𝔄)`, with the layer
reduction `U(𝔄) → ∏_i GL_{d_i}(k_F)`. If one factor `ρ_{i₀}` is not cuspidal, then there is a
lattice chain `𝓜` of strictly larger period and a nonzero vector of `W` fixed by `U^1(𝓜)`
(`LatticeChain.exists_refinement_of_not_isCuspidal`).

This is the refinement step in the proof of Bushnell–Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (8.1.5), printed p. 268 (PDF p. 280), following Bushnell,
*Hereditary orders, Gauss sums and supercuspidal representations of GL_N* (1987), proof of
Theorem 2′(i), printed p. 197 (PDF p. 14): a vector of `Y_{i₀}` fixed by the unipotent radical
of a proper parabolic subgroup of `GL(L_{i₀} / L_{i₀+1})` is fixed by `U^1(𝓜)`, where `𝓜` is
obtained from `𝓛` by inserting the preimage in `L_{i₀}` of a subspace of `L_{i₀} / L_{i₀+1}`
stable under that parabolic subgroup.
-/

noncomputable section

open IsLocalRing Module ValuativeRel

namespace Langlands.BushnellKutzko

universe u v uY uW

section BlockCriteria

variable {n : ℕ} (B : GeneralLinear.BlockShape n)

private theorem coordinateBlock_index' (i : Fin B.length) (a : Fin (B.size i)) :
    B.coordinateBlock (B.index i a) = i := by
  change (B.indexEquiv.symm (B.indexEquiv ⟨i, a⟩)).1 = i
  rw [Equiv.symm_apply_apply]

/-- A proper standard block parabolic subgroup separates two coordinates: some coordinate lies
in a strictly later block than another. -/
private theorem exists_coordinateBlock_lt {R : Type*} [CommRing R] (hB : B.parabolic R ≠ ⊤) :
    ∃ x y : Fin n, B.coordinateBlock y < B.coordinateBlock x := by
  by_contra h
  push Not at h
  apply hB
  rw [eq_top_iff]
  intro g _
  rw [GeneralLinear.BlockShape.mem_parabolic_iff]
  intro i j a c hji
  have hle := h (B.index i a) (B.index j c)
  rw [coordinateBlock_index', coordinateBlock_index'] at hle
  exact absurd hji (not_lt.mpr hle)

/-- A matrix whose entries in the blocks on and below the diagonal are those of the identity lies
in the unipotent radical of the standard block parabolic subgroup. -/
private theorem mem_unipotentSubgroup_of_entries {R : Type*} [CommRing R]
    (g : GeneralLinear n R)
    (h : ∀ a c : Fin n, B.coordinateBlock c ≤ B.coordinateBlock a →
      g a c = if a = c then 1 else 0) :
    g ∈ B.unipotentSubgroup R := by
  rw [GeneralLinear.BlockShape.mem_unipotentSubgroup_iff,
    GeneralLinear.BlockShape.mem_parabolic_iff]
  refine ⟨fun i j a c hji => ?_, fun i a c => ?_⟩
  · have hne : B.index i a ≠ B.index j c := by
      intro he
      have hb := congrArg B.coordinateBlock he
      rw [coordinateBlock_index', coordinateBlock_index'] at hb
      exact hji.ne hb.symm
    rw [h _ _ (by rw [coordinateBlock_index', coordinateBlock_index']; exact hji.le)]
    simp [hne]
  · rw [h _ _ (by simp only [coordinateBlock_index', le_refl])]
    simp only [EmbeddingLike.apply_eq_iff_eq]

end BlockCriteria

/-- A pure tensor of nonzero vectors of complex vector spaces is nonzero. -/
theorem tprod_ne_zero_of_forall_ne_zero {κ : Type*} [Fintype κ] {X : κ → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (v : ∀ i, X i) (hv : ∀ i, v i ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  classical
  let b (i : κ) := Module.Free.chooseBasis ℂ (X i)
  have h_i (i : κ) : ∃ j, (b i).repr (v i) j ≠ 0 := by
    by_contra! h
    apply hv i
    apply (b i).repr.injective
    exact Finsupp.ext fun j => by simpa using h j
  choose j hj using h_i
  intro h
  have he := congrArg (fun x => (Basis.piTensorProduct b).repr x j) h
  simp only [Basis.piTensorProduct_repr_tprod_apply, map_zero, Finsupp.zero_apply] at he
  exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hj i)) he

namespace LatticeChain

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ι : Type v}

/-- **Refinement at a non-cuspidal layer.** Let `τ` be a representation of `Aut_F(F^ι)` on
`W`, let `ρ_i` be representations of `GL_{d_i}(k_F)` on nonzero spaces `Y_i`, where `d_i` is the
dimension of `L_i / L_{i+1}` with basis `b_i`, and let `f : ⊗_i Y_i → W` be an injective linear
map carrying the external tensor product of the `ρ_i`, inflated along the layer reduction
`U(𝔄) → ∏_i GL_{d_i}(k_F)`, to the restriction of `τ` to `U(𝔄)`. If some `ρ_{i₀}` is not
cuspidal, there is a lattice chain `𝓜` of strictly larger period and a nonzero vector of `W`
fixed by `U^1(𝓜)`. -/
theorem exists_refinement_of_not_isCuspidal (𝓛 : LatticeChain 𝒪[F] F (ι → F))
    {d : Fin 𝓛.period → ℕ}
    (b : ∀ i, Module.Basis (Fin (d i)) (ResidueField 𝒪[F]) (𝓛.Layer (i : ℕ)))
    {Y : Fin 𝓛.period → Type uY} [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)]
    [∀ i, Nontrivial (Y i)]
    (ρ : ∀ i, Representation ℂ (GeneralLinear (d i) (ResidueField 𝒪[F])) (Y i))
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Module.End F (ι → F))ˣ W)
    (f : PiTensorProduct ℂ Y →ₗ[ℂ] W) (hf : Function.Injective f)
    (hfτ : ∀ (g : 𝓛.unitFiltration 0) (x : PiTensorProduct ℂ Y),
      f (FiniteTensor.external ρ (𝓛.layerReduction b g) x) = τ g (f x))
    (i₀ : Fin 𝓛.period) (hi₀ : ¬ FiniteGeneralLinear.IsCuspidal (ρ i₀)) :
    ∃ 𝓜 : LatticeChain 𝒪[F] F (ι → F), 𝓛.period < 𝓜.period ∧
      ∃ w : W, w ≠ 0 ∧ ∀ g ∈ 𝓜.unitFiltration 1, τ g w = w := by
  classical
  -- A nonzero vector of `Y_{i₀}` fixed by the unipotent radical of a proper parabolic.
  unfold FiniteGeneralLinear.IsCuspidal at hi₀
  push Not at hi₀
  obtain ⟨B, hB, z₀, hz₀, hz₀0⟩ := hi₀
  obtain ⟨x₀, y₀, hxy⟩ := exists_coordinateBlock_lt B hB
  -- The subspace of `L_{i₀} / L_{i₀+1}` spanned by the basis vectors in the blocks up to that
  -- of `y₀`, and its preimage `M` in `L_{i₀}`.
  let P : Set (Fin (d i₀)) := {x | B.coordinateBlock x ≤ B.coordinateBlock y₀}
  let S : Submodule (ResidueField 𝒪[F]) (𝓛.Layer (i₀ : ℕ)) :=
    Submodule.span (ResidueField 𝒪[F]) (b i₀ '' P)
  let M : Submodule 𝒪[F] (ι → F) :=
    ((S.restrictScalars 𝒪[F]).comap
      (𝓛.intervalSubmodule ((i₀ : ℕ) : ℤ) (((i₀ : ℕ) : ℤ) + 1)).mkQ).map
      (𝓛.lattice ((i₀ : ℕ) : ℤ)).subtype
  have hM : ∀ v : ι → F, v ∈ M ↔ ∃ hv : v ∈ 𝓛.lattice ((i₀ : ℕ) : ℤ),
      𝓛.intervalMk ((i₀ : ℕ) : ℤ) (((i₀ : ℕ) : ℤ) + 1) v hv ∈ S := by
    intro v
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hv, hS⟩
      exact ⟨⟨v, hv⟩, hS, rfl⟩
  have hyS : b i₀ y₀ ∈ S := Submodule.subset_span ⟨y₀, le_refl (B.coordinateBlock y₀), rfl⟩
  have hnotS : b i₀ x₀ ∉ S := by
    intro h
    have hsupp := (b i₀).mem_span_image.mp h
    rw [(b i₀).repr_self] at hsupp
    have hx : x₀ ∈ P := hsupp (by simp)
    exact absurd hx (not_le.mpr hxy)
  have h₁ : 𝓛.lattice (((i₀ : ℕ) : ℤ) + 1) < M := by
    refine IsConcreteLE.lt_iff_le_and_exists.mpr ⟨fun v hv => ?_, ?_⟩
    · have hv' : v ∈ 𝓛.lattice ((i₀ : ℕ) : ℤ) := 𝓛.antitone (by omega) hv
      refine (hM v).mpr ⟨hv', ?_⟩
      rw [(𝓛.intervalMk_eq_zero_iff hv').mpr hv]
      exact S.zero_mem
    · obtain ⟨v, hv, hvy⟩ := 𝓛.intervalMk_surjective _ (((i₀ : ℕ) : ℤ) + 1) (b i₀ y₀)
      refine ⟨v, (hM v).mpr ⟨hv, by rw [hvy]; exact hyS⟩, fun hv1 => ?_⟩
      have h0 := (𝓛.intervalMk_eq_zero_iff hv).mpr hv1
      rw [hvy] at h0
      exact (b i₀).ne_zero y₀ h0
  have h₂ : M < 𝓛.lattice ((i₀ : ℕ) : ℤ) := by
    refine IsConcreteLE.lt_iff_le_and_exists.mpr ⟨fun v hv => ((hM v).mp hv).1, ?_⟩
    obtain ⟨v, hv, hvx⟩ := 𝓛.intervalMk_surjective _ (((i₀ : ℕ) : ℤ) + 1) (b i₀ x₀)
    refine ⟨v, hv, fun hvM => hnotS ?_⟩
    obtain ⟨hv', hS⟩ := (hM v).mp hvM
    rw [← hvx]
    exact hS
  obtain ⟨𝓜, hper, h𝓜⟩ := 𝓛.exists_insertLattice h₁ h₂
  -- A pure tensor with `z₀` at `i₀` and nonzero vectors elsewhere.
  have hy : ∀ i, ∃ y : Y i, y ≠ 0 := fun i => exists_ne 0
  choose y hy using hy
  obtain ⟨z, hzi₀, hzne⟩ : ∃ z : ∀ i, Y i, z i₀ = z₀ ∧ ∀ i, z i ≠ 0 := by
    refine ⟨Function.update y i₀ z₀, Function.update_self i₀ z₀ y, fun i => ?_⟩
    by_cases h : i = i₀
    · rw [h, Function.update_self]
      exact hz₀0
    · rw [Function.update_of_ne h]
      exact hy i
  refine ⟨𝓜, hper, f (PiTensorProduct.tprod ℂ z),
    fun h0 => tprod_ne_zero_of_forall_ne_zero z hzne (hf (h0.trans (map_zero f).symm)), ?_⟩
  intro g hg
  obtain ⟨hg0, hwin, hpM, hMp⟩ := h𝓜 g hg
  let g' : 𝓛.unitFiltration 0 := ⟨g, hg0⟩
  -- `g` acts trivially on the layers other than `L_{i₀} / L_{i₀+1}`.
  have hred : ∀ i, i ≠ i₀ → 𝓛.layerReduction b g' i = 1 := by
    intro i hi
    refine 𝓛.layerReduction_apply_eq_one b g' i fun v hv => ?_
    have hi' := i.isLt
    have hi₀' := i₀.isLt
    refine hwin ((i : ℕ) : ℤ) ?_ ?_ ?_ v hv
    · intro h
      exact hi (Fin.ext (by exact_mod_cast h))
    · omega
    · omega
  -- On `L_{i₀} / L_{i₀+1}`, `g` lies in the unipotent radical of the parabolic.
  have hunip : 𝓛.layerReduction b g' i₀ ∈ B.unipotentSubgroup (ResidueField 𝒪[F]) := by
    apply mem_unipotentSubgroup_of_entries B
    intro a c hca
    obtain ⟨v, hv, hvc⟩ := 𝓛.intervalMk_surjective _ (((i₀ : ℕ) : ℤ) + 1) (b i₀ c)
    rw [𝓛.layerReduction_apply_entry b g' i₀ a c v hv hvc]
    have hgv : (g : Module.End F (ι → F)) v - v ∈ 𝓛.lattice ((i₀ : ℕ) : ℤ) :=
      sub_mem (𝓛.mem_order.mp g'.2.1 _ _ hv) hv
    have hsplit : 𝓛.intervalMk ((i₀ : ℕ) : ℤ) (((i₀ : ℕ) : ℤ) + 1)
        ((g'.1 : Module.End F (ι → F)) v) (𝓛.mem_order.mp g'.2.1 _ _ hv) =
        b i₀ c + 𝓛.intervalMk _ _ _ hgv := by
      rw [← hvc]
      simp only [LatticeChain.intervalMk, ← Submodule.Quotient.mk_add]
      congr 1
      ext
      simp [g']
    have hzero : (b i₀).repr (𝓛.intervalMk _ (((i₀ : ℕ) : ℤ) + 1) _ hgv) a = 0 := by
      by_cases hc : c ∈ P
      · have hvM : v ∈ M := (hM v).mpr ⟨hv, by rw [hvc]; exact Submodule.subset_span ⟨c, hc, rfl⟩⟩
        rw [(𝓛.intervalMk_eq_zero_iff hgv).mpr (hMp v hvM), map_zero, Finsupp.zero_apply]
      · have ha : a ∉ P := fun ha => hc (le_trans hca ha)
        obtain ⟨hgv', hS⟩ := (hM _).mp (hpM v hv)
        have hsupp := (b i₀).mem_span_image.mp hS
        exact Finsupp.notMem_support_iff.mp fun h => ha (hsupp h)
    rw [hsplit, map_add, Finsupp.add_apply, hzero, add_zero, (b i₀).repr_self,
      Finsupp.single_apply]
    by_cases hac : a = c
    · subst hac
      simp
    · simp [hac, Ne.symm hac]
  have hfix : FiniteTensor.external ρ (𝓛.layerReduction b g') (PiTensorProduct.tprod ℂ z) =
      PiTensorProduct.tprod ℂ z := by
    rw [FiniteTensor.external_tprod]
    congr 1
    funext i
    by_cases hi : i = i₀
    · rw [hi, hzi₀]
      exact hz₀ _ hunip
    · rw [hred i hi, map_one, Module.End.one_apply]
  calc τ g (f (PiTensorProduct.tprod ℂ z))
      = f (FiniteTensor.external ρ (𝓛.layerReduction b g') (PiTensorProduct.tprod ℂ z)) :=
        (hfτ g' _).symm
    _ = f (PiTensorProduct.tprod ℂ z) := by rw [hfix]

end LatticeChain

end Langlands.BushnellKutzko
