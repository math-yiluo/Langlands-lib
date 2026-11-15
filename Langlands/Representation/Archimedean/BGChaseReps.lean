import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Module.Submodule.Bilinear
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.FieldTheory.Finiteness

/-!
# Representations and integral weights: helpers for the Bernstein–Gelfand chase

Tensor products, `Hom` spaces and invariant subspaces of Lie algebra representations, and
the behaviour of integral weights under these constructions.
-/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Archimedean.BGChase

attribute [local instance 100] LieRing.ofAssociativeRing

section Lie

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  {W : Type*} [AddCommGroup W] [Module ℂ W] {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem endBracket (a b : Module.End ℂ W) : ⁅a, b⁆ = a * b - b * a := Ring.lie_def a b

/-- The tensor product `σ ⊗ 1 + 1 ⊗ τ` of two representations. -/
def tensorLie (σ : L →ₗ⁅ℂ⁆ Module.End ℂ W) (τ : L →ₗ⁅ℂ⁆ Module.End ℂ N) :
    L →ₗ⁅ℂ⁆ Module.End ℂ (W ⊗[ℂ] N) where
  toFun Y := LinearMap.rTensor N (σ Y) + LinearMap.lTensor W (τ Y)
  map_add' X Y := by
    simp only [map_add, LinearMap.rTensor_add, LinearMap.lTensor_add]; abel
  map_smul' c Y := by
    simp only [map_smul, LinearMap.rTensor_smul, LinearMap.lTensor_smul, RingHom.id_apply,
      smul_add]
  map_lie' {X Y} := by
    apply TensorProduct.ext'
    intro w x
    simp only [LieHom.map_lie, endBracket, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.sub_tmul,
      TensorProduct.tmul_sub, map_add]
    abel

theorem tensorLie_apply (σ : L →ₗ⁅ℂ⁆ Module.End ℂ W) (τ : L →ₗ⁅ℂ⁆ Module.End ℂ N) (Y : L) :
    tensorLie σ τ Y = LinearMap.rTensor N (σ Y) + LinearMap.lTensor W (τ Y) := rfl

theorem tensorLie_tmul (σ : L →ₗ⁅ℂ⁆ Module.End ℂ W) (τ : L →ₗ⁅ℂ⁆ Module.End ℂ N) (Y : L)
    (w : W) (x : N) : tensorLie σ τ Y (w ⊗ₜ x) = σ Y w ⊗ₜ x + w ⊗ₜ τ Y x := rfl

/-- The representation `ψ ↦ τ(Y) ∘ ψ - ψ ∘ σ(Y)` on `Hom(W, N)`. -/
def homLie (σ : L →ₗ⁅ℂ⁆ Module.End ℂ W) (τ : L →ₗ⁅ℂ⁆ Module.End ℂ N) :
    L →ₗ⁅ℂ⁆ Module.End ℂ (W →ₗ[ℂ] N) where
  toFun Y :=
    { toFun := fun ψ => τ Y ∘ₗ ψ - ψ ∘ₗ σ Y
      map_add' := fun ψ φ => by ext w; simp only [LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.add_apply, map_add]; abel
      map_smul' := fun c ψ => by ext w; simp [smul_sub] }
  map_add' X Y := by ext ψ w; simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply]; abel
  map_smul' c Y := by ext ψ w; simp [smul_sub]
  map_lie' {X Y} := by
    ext ψ w
    simp only [LieHom.map_lie, endBracket, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
      Module.End.mul_apply, LinearMap.comp_apply, map_sub]
    abel

theorem homLie_apply (σ : L →ₗ⁅ℂ⁆ Module.End ℂ W) (τ : L →ₗ⁅ℂ⁆ Module.End ℂ N) (Y : L)
    (ψ : W →ₗ[ℂ] N) (w : W) : homLie σ τ Y ψ w = τ Y (ψ w) - ψ (σ Y w) := rfl

/-- The restriction of a representation to an invariant subspace. -/
def restrictLie (σ : L →ₗ⁅ℂ⁆ Module.End ℂ W) (S : Submodule ℂ W)
    (hS : ∀ Y, ∀ s ∈ S, σ Y s ∈ S) : L →ₗ⁅ℂ⁆ Module.End ℂ S where
  toFun Y := (σ Y).restrict (hS Y)
  map_add' X Y := by ext s; simp [LinearMap.restrict_apply]
  map_smul' c Y := by ext s; simp [LinearMap.restrict_apply]
  map_lie' {X Y} := by
    ext s
    simp [LinearMap.restrict_apply, endBracket]

theorem restrictLie_apply (σ : L →ₗ⁅ℂ⁆ Module.End ℂ W) (S : Submodule ℂ W)
    (hS : ∀ Y, ∀ s ∈ S, σ Y s ∈ S) (Y : L) (s : S) :
    ((restrictLie σ S hS Y s : S) : W) = σ Y s := rfl

end Lie

/-! ## Integral weights -/

section Weights

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- `w` has weight `m` for the operators `H p`. -/
def IsWt (H : Fin n → Module.End ℂ W) (m : Fin n → ℤ) (w : W) : Prop :=
  ∀ p, H p w = (m p : ℂ) • w

/-- The weight space of weight `m`. -/
def wtSpace (H : Fin n → Module.End ℂ W) (m : Fin n → ℤ) : Submodule ℂ W where
  carrier := {w | IsWt H m w}
  add_mem' {a b} ha hb p := by rw [map_add, ha p, hb p, smul_add]
  zero_mem' p := by simp
  smul_mem' c a ha p := by rw [map_smul, ha p, smul_comm]

theorem mem_wtSpace {H : Fin n → Module.End ℂ W} {m : Fin n → ℤ} {w : W} :
    w ∈ wtSpace H m ↔ IsWt H m w := Iff.rfl

/-- The span of the vectors with integral weight. -/
def intSpan (H : Fin n → Module.End ℂ W) : Submodule ℂ W :=
  Submodule.span ℂ {w | ∃ m, IsWt H m w}

theorem intSpan_eq_iSup (H : Fin n → Module.End ℂ W) : intSpan H = ⨆ m, wtSpace H m := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨m, hm⟩
    exact Submodule.mem_iSup_of_mem m hm
  · exact iSup_le fun m w hw => Submodule.subset_span ⟨m, hw⟩

/-- Elimination of weight components: if a sum of weight vectors with distinct weights lies in
an `H`-invariant subspace `S`, so does every summand. -/
theorem mem_of_sum_mem (H : Fin n → Module.End ℂ W) (S : Submodule ℂ W)
    (hS : ∀ p, ∀ x ∈ S, H p x ∈ S) :
    ∀ (s : Finset (Fin n → ℤ)) (w : (Fin n → ℤ) → W), (∀ m ∈ s, IsWt H m (w m)) →
      (∑ m ∈ s, w m) ∈ S → ∀ m ∈ s, w m ∈ S := by
  classical
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro w hw hsum m hm
    by_cases hs : ∃ m' ∈ s, m' ≠ m
    · obtain ⟨m', hm', hne⟩ := hs
      obtain ⟨p, hp⟩ : ∃ p, m p ≠ m' p := by
        by_contra h
        push Not at h
        exact hne (funext h).symm
      set w' : (Fin n → ℤ) → W := fun k => (((k p : ℤ) : ℂ) - (m' p : ℂ)) • w k with hw'def
      have hw' : ∀ k ∈ s.erase m', IsWt H k (w' k) := by
        intro k hk q
        show H q ((((k p : ℤ) : ℂ) - (m' p : ℂ)) • w k) =
          ((k q : ℤ) : ℂ) • ((((k p : ℤ) : ℂ) - (m' p : ℂ)) • w k)
        rw [map_smul, hw k (Finset.mem_of_mem_erase hk) q, smul_comm]
      have hsum' : (∑ k ∈ s.erase m', w' k) ∈ S := by
        have h0 : w' m' = 0 := by simp [hw'def]
        rw [Finset.sum_erase _ h0]
        have : (∑ k ∈ s, w' k) = H p (∑ k ∈ s, w k) - (m' p : ℂ) • ∑ k ∈ s, w k := by
          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun k hk => ?_
          show (((k p : ℤ) : ℂ) - (m' p : ℂ)) • w k = H p (w k) - (m' p : ℂ) • w k
          rw [hw k hk p, sub_smul]
        rw [this]
        exact S.sub_mem (hS p _ hsum) (S.smul_mem _ hsum)
      have hmem := ih (s.erase m') (Finset.erase_ssubset hm') w' hw' hsum' m
        (Finset.mem_erase.2 ⟨hne.symm, hm⟩)
      have hc : ((m p : ℤ) : ℂ) - (m' p : ℂ) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast hp
      have := S.smul_mem (((m p : ℤ) : ℂ) - (m' p : ℂ))⁻¹ hmem
      simpa [hw'def, smul_smul, inv_mul_cancel₀ hc] using this
    · push Not at hs
      have : (∑ k ∈ s, w k) = w m :=
        Finset.sum_eq_single_of_mem m hm fun k hk hkm => absurd (hs k hk) hkm
      rwa [this] at hsum

/-- An `H`-invariant subspace of the integral span is spanned by its own weight vectors. -/
theorem mem_span_wt_of_mem (H : Fin n → Module.End ℂ W) (S : Submodule ℂ W)
    (hS : ∀ p, ∀ x ∈ S, H p x ∈ S) {x : W} (hxS : x ∈ S) (hx : x ∈ intSpan H) :
    x ∈ Submodule.span ℂ {w | w ∈ S ∧ ∃ m, IsWt H m w} := by
  classical
  rw [intSpan_eq_iSup] at hx
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx
  have hmem := mem_of_sum_mem H S hS f.support f (fun m _ => hf m) hxS
  rw [Finsupp.sum]
  exact Submodule.sum_mem _ fun m hm => Submodule.subset_span ⟨hmem m hm, m, hf m⟩

theorem intSpan_mono {H : Fin n → Module.End ℂ W} {S : Set W}
    (hS : ∀ w ∈ S, ∃ m, IsWt H m w) : Submodule.span ℂ S ≤ intSpan H :=
  Submodule.span_mono hS

theorem mem_intSpan_of_isWt {H : Fin n → Module.End ℂ W} {m : Fin n → ℤ} {w : W}
    (hw : IsWt H m w) : w ∈ intSpan H :=
  Submodule.subset_span ⟨m, hw⟩

end Weights

/-! ## Integral weights of representations of `𝔤𝔩_n` -/

section Gl

universe uW uN

variable {n : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W] {N : Type uN} [AddCommGroup N]
  [Module ℂ N]

/-- The diagonal operators `σ(E_pp)` of a representation `σ` of `𝔤𝔩_n`. -/
def diagOps (σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ W) : Fin n → Module.End ℂ W :=
  fun p => σ (Matrix.single p p 1)

theorem isWt_tmul {σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ W}
    {τ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ N} {m₁ m₂ : Fin n → ℤ} {w : W} {x : N}
    (hw : IsWt (diagOps σ) m₁ w) (hx : IsWt (diagOps τ) m₂ x) :
    IsWt (diagOps (tensorLie σ τ)) (m₁ + m₂) (w ⊗ₜ x) := by
  intro p
  change tensorLie σ τ _ (w ⊗ₜ x) = _
  rw [tensorLie_tmul]
  change diagOps σ p w ⊗ₜ x + w ⊗ₜ diagOps τ p x = _
  rw [hw p, hx p, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, ← add_smul]
  simp only [Pi.add_apply, Int.cast_add]

/-- Integral weights pass to tensor products. -/
theorem intSpan_tensorLie {σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ W}
    {τ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ N} (hσ : intSpan (diagOps σ) = ⊤)
    (hτ : intSpan (diagOps τ) = ⊤) : intSpan (diagOps (tensorLie σ τ)) = ⊤ := by
  rw [eq_top_iff]
  rintro t -
  induction t with
  | add a b ha hb => exact Submodule.add_mem _ ha hb
  | tmul w x =>
    have hw : w ∈ intSpan (diagOps σ) := hσ ▸ Submodule.mem_top
    have hx : x ∈ intSpan (diagOps τ) := hτ ▸ Submodule.mem_top
    have h := Submodule.apply_mem_map₂ (TensorProduct.mk ℂ W N) hw hx
    rw [intSpan, intSpan, Submodule.map₂_span_span] at h
    refine Submodule.span_le.2 ?_ h
    rintro _ ⟨a, ⟨m₁, ha⟩, b, ⟨m₂, hb⟩, rfl⟩
    exact mem_intSpan_of_isWt (isWt_tmul ha hb)

/-- A finite-dimensional representation with integral weights has a basis of weight vectors. -/
theorem exists_wtBasis [FiniteDimensional ℂ W] {H : Fin n → Module.End ℂ W}
    (hH : intSpan H = ⊤) :
    ∃ (ι : Type uW) (_ : Fintype ι) (b : Module.Basis ι ℂ W) (μ : ι → Fin n → ℤ),
      ∀ i, IsWt H (μ i) (b i) := by
  classical
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent ℂ {w : W | ∃ m, IsWt H m w}
  have hspan : ⊤ ≤ Submodule.span ℂ (Set.range (Subtype.val : s → W)) := by
    rw [Subtype.range_coe, hs_span]
    exact hH.ge
  let b := Module.Basis.mk hs_li hspan
  have hb : ∀ i, b i = (i : W) := fun i => by simp [b]
  have hwt : ∀ i : s, ∃ m, IsWt H m (b i) := fun i => by rw [hb]; exact hs_sub i.2
  exact ⟨s, FiniteDimensional.fintypeBasisIndex b, b, fun i => (hwt i).choose,
    fun i => (hwt i).choose_spec⟩

theorem coord_comp_of_isWt {ι : Type*} (b : Module.Basis ι ℂ W) {H : Fin n → Module.End ℂ W}
    {μ : ι → Fin n → ℤ} (hb : ∀ i, IsWt H (μ i) (b i)) (i : ι) (p : Fin n) :
    b.coord i ∘ₗ H p = ((μ i p : ℤ) : ℂ) • b.coord i := by
  classical
  refine b.ext fun j => ?_
  rw [LinearMap.comp_apply, hb j p, LinearMap.smul_apply, map_smul]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem eq_sum_coord_smulRight {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ W)
    (ψ : W →ₗ[ℂ] N) : ψ = ∑ i, (b.coord i).smulRight (ψ (b i)) := by
  classical
  refine b.ext fun j => ?_
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_eq_single j (fun i _ hij => by simp [Ne.symm hij]) (by simp)]
  simp

/-- Integral weights pass to `Hom` spaces with finite-dimensional source. -/
theorem intSpan_homLie [FiniteDimensional ℂ W]
    {σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ W}
    {τ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ N} (hσ : intSpan (diagOps σ) = ⊤)
    (hτ : intSpan (diagOps τ) = ⊤) : intSpan (diagOps (homLie σ τ)) = ⊤ := by
  obtain ⟨ι, _, b, μ, hb⟩ := exists_wtBasis hσ
  rw [eq_top_iff]
  intro ψ _
  rw [eq_sum_coord_smulRight b ψ]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hx : ψ (b i) ∈ intSpan (diagOps τ) := hτ ▸ Submodule.mem_top
  have h := Submodule.mem_map_of_mem (f := LinearMap.smulRightₗ (b.coord i)) hx
  rw [intSpan, Submodule.map_span] at h
  refine Submodule.span_le.2 ?_ h
  rintro _ ⟨x, ⟨ν, hν⟩, rfl⟩
  refine mem_intSpan_of_isWt (m := ν - μ i) fun p => ?_
  ext w
  change τ _ ((b.coord i) w • x) - (b.coord i) (σ _ w) • x = _
  have hc := LinearMap.congr_fun (coord_comp_of_isWt b hb i p) w
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hc
  change (b.coord i) (diagOps σ p w) = _ at hc
  rw [map_smul]
  change (b.coord i) w • diagOps τ p x - (b.coord i) (diagOps σ p w) • x = _
  rw [hν p, hc, LinearMap.smul_apply, LinearMap.smulRightₗ_apply, LinearMap.smulRight_apply,
    smul_comm, smul_smul, ← sub_smul]
  rw [smul_eq_mul, smul_smul]
  congr 1
  simp only [Pi.sub_apply, Int.cast_sub]
  ring

/-- The trivial one-dimensional representation has integral weights. -/
theorem intSpan_trivial :
    intSpan (diagOps (0 : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ ℂ)) = ⊤ := by
  rw [eq_top_iff]
  intro c _
  have h1 : (1 : ℂ) ∈ intSpan (diagOps (0 : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ ℂ)) :=
    mem_intSpan_of_isWt (m := 0) fun _ => by simp [diagOps]
  simpa using Submodule.smul_mem _ c h1

/-- The restriction to an invariant subspace spanned by its weight vectors has integral
weights. -/
theorem intSpan_restrictLie {σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ W}
    (S : Submodule ℂ W) (hS : ∀ Y, ∀ s ∈ S, σ Y s ∈ S)
    (hspan : S ≤ Submodule.span ℂ {w | w ∈ S ∧ ∃ m, IsWt (diagOps σ) m w}) :
    intSpan (diagOps (restrictLie σ S hS)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  have hx := hspan x.2
  have hset : {w | w ∈ S ∧ ∃ m, IsWt (diagOps σ) m w} =
      S.subtype '' {y : S | ∃ m, IsWt (diagOps (restrictLie σ S hS)) m y} := by
    ext w
    constructor
    · rintro ⟨hwS, m, hm⟩
      exact ⟨⟨w, hwS⟩, ⟨m, fun p => Subtype.ext (hm p)⟩, rfl⟩
    · rintro ⟨y, ⟨m, hm⟩, rfl⟩
      exact ⟨y.2, m, fun p => congrArg Subtype.val (hm p)⟩
  rw [hset, ← Submodule.map_span] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

/-- An invariant subspace of a representation inside the integral span: the restriction has
integral weights. -/
theorem intSpan_restrictLie_of_le {σ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ W}
    (S : Submodule ℂ W) (hS : ∀ Y, ∀ s ∈ S, σ Y s ∈ S) (hle : S ≤ intSpan (diagOps σ)) :
    intSpan (diagOps (restrictLie σ S hS)) = ⊤ :=
  intSpan_restrictLie S hS fun _ hx =>
    mem_span_wt_of_mem (diagOps σ) S (fun _ y hy => hS _ y hy) hx (hle hx)

end Gl

end Langlands.Archimedean.BGChase
