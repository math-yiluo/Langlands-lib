import Langlands.Representation.FiniteGeneralLinear.HarishChandraMackeyMatching

/-! # Vanishing of Harish-Chandra Mackey terms along a lower corner -/

noncomputable section

open Module Representation

namespace Langlands.BushnellKutzko.SplitTypeJacquet

open Langlands.FiniteGeneralLinear Langlands.GeneralLinear Langlands.Geometric
  Langlands.CuspidalSupport Langlands.FiniteRep

variable {k : Type*} [Field k] {n : ℕ}

/-- The coordinates lying in the first `j` blocks of a block shape. -/
def InFirst (B : BlockShape n) (j : ℕ) : Fin n → Prop := fun a => (blockIndex B a : ℕ) < j

instance (B : BlockShape n) (j : ℕ) : DecidablePred (InFirst B j) :=
  fun _ => Nat.decLt _ _

theorem index_blockIndex (B : BlockShape n) (a : Fin n) :
    B.index (blockIndex B a) (B.indexEquiv.symm a).2 = a :=
  B.indexEquiv.apply_symm_apply a

/-- The entries of a standard upper block parabolic below the block diagonal vanish. -/
theorem parabolic_apply_eq_zero {B : BlockShape n} {g : GeneralLinear n k}
    (hg : g ∈ B.parabolic k) {a b : Fin n} (h : blockIndex B b < blockIndex B a) :
    g a b = 0 := by
  have := (B.mem_parabolic_iff k g).mp hg (blockIndex B a) (blockIndex B b)
    (B.indexEquiv.symm a).2 (B.indexEquiv.symm b).2 h
  rwa [index_blockIndex, index_blockIndex] at this

/-- The two-block function of the coarse decomposition: `0` on the first `j` blocks. -/
def coarseBlock (B : BlockShape n) (j : ℕ) (a : Fin n) : ℕ :=
  if InFirst B j a then 0 else 1

theorem coarseBlock_lt_iff (B : BlockShape n) (j : ℕ) (a b : Fin n) :
    coarseBlock B j b < coarseBlock B j a ↔ InFirst B j b ∧ ¬ InFirst B j a := by
  unfold coarseBlock
  split_ifs <;> simp_all

/-- Standard block parabolics are upper triangular for the coarse decomposition. -/
theorem blockTriangular_of_mem_parabolic (B : BlockShape n) (j : ℕ) {g : GeneralLinear n k}
    (hg : g ∈ B.parabolic k) :
    Matrix.BlockTriangular (g : Matrix (Fin n) (Fin n) k) (coarseBlock B j) := by
  intro a b hab
  obtain ⟨hb, ha⟩ := (coarseBlock_lt_iff B j a b).mp hab
  exact parabolic_apply_eq_zero hg (by
    unfold InFirst at hb ha
    exact Fin.lt_def.mpr (by omega))

/-- A permutation preserving the first `j` blocks gives a coarse upper triangular matrix. -/
theorem blockTriangular_permutation (B : BlockShape n) (j : ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ a, InFirst B j (σ a) ↔ InFirst B j a) :
    Matrix.BlockTriangular (permutation n k σ : Matrix (Fin n) (Fin n) k) (coarseBlock B j) := by
  intro a b hab
  obtain ⟨hb, ha⟩ := (coarseBlock_lt_iff B j a b).mp hab
  rw [permutation_entry, ite_eq_right_iff]
  intro h
  exact absurd (h ▸ (hσ b).mpr hb) ha

/-- Matrices supported on the rows outside and the columns inside the first `j` blocks,
given by their corner entries. -/
abbrev Corner (B : BlockShape n) (j : ℕ) (k : Type*) :=
  {a // ¬ InFirst B j a} → {b // InFirst B j b} → k

/-- The matrix with the given lower corner and zero elsewhere. -/
def cornerMatrix {B : BlockShape n} {j : ℕ} (X : Corner B j k) : Matrix (Fin n) (Fin n) k :=
  Matrix.of fun a b =>
    if ha : InFirst B j a then 0 else if hb : InFirst B j b then X ⟨a, ha⟩ ⟨b, hb⟩ else 0

theorem cornerMatrix_apply {B : BlockShape n} {j : ℕ} (X : Corner B j k) (a b : Fin n) :
    cornerMatrix X a b =
      if ha : InFirst B j a then 0 else if hb : InFirst B j b then X ⟨a, ha⟩ ⟨b, hb⟩ else 0 :=
  rfl

theorem cornerMatrix_mul {B : BlockShape n} {j : ℕ} (X Y : Corner B j k) :
    cornerMatrix X * cornerMatrix Y = 0 := by
  ext a c
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [cornerMatrix_apply, cornerMatrix_apply]
  by_cases hb : InFirst B j b <;> simp [hb]

theorem cornerMatrix_add {B : BlockShape n} {j : ℕ} (X Y : Corner B j k) :
    cornerMatrix (X + Y) = cornerMatrix X + cornerMatrix Y := by
  ext a b
  simp only [Matrix.add_apply, cornerMatrix_apply]
  split_ifs <;> simp

theorem cornerMatrix_neg {B : BlockShape n} {j : ℕ} (X : Corner B j k) :
    cornerMatrix (-X) = -cornerMatrix X := by
  ext a b
  simp only [Matrix.neg_apply, cornerMatrix_apply]
  split_ifs <;> simp

theorem cornerMatrix_zero {B : BlockShape n} {j : ℕ} :
    cornerMatrix (0 : Corner B j k) = 0 := by
  ext a b
  simp only [Matrix.zero_apply, cornerMatrix_apply]
  split_ifs <;> simp

/-- The lower corner unipotent matrix `1 + X`. -/
def lowerUnip {B : BlockShape n} {j : ℕ} (X : Corner B j k) : GeneralLinear n k where
  val := 1 + cornerMatrix X
  inv := 1 - cornerMatrix X
  val_inv := by
    rw [mul_sub, mul_one, add_mul, one_mul, cornerMatrix_mul, add_zero, add_sub_cancel_right]
  inv_val := by
    rw [sub_mul, one_mul, mul_add, mul_one, cornerMatrix_mul, add_zero, add_sub_cancel_right]

@[simp] theorem coe_lowerUnip {B : BlockShape n} {j : ℕ} (X : Corner B j k) :
    (lowerUnip X : Matrix (Fin n) (Fin n) k) = 1 + cornerMatrix X := rfl

theorem lowerUnip_mul {B : BlockShape n} {j : ℕ} (X Y : Corner B j k) :
    lowerUnip X * lowerUnip Y = lowerUnip (X + Y) := by
  apply Units.ext
  simp only [Units.val_mul, coe_lowerUnip, cornerMatrix_add, mul_add, add_mul, one_mul, mul_one,
    cornerMatrix_mul, add_zero]
  abel

theorem lowerUnip_zero {B : BlockShape n} {j : ℕ} : lowerUnip (0 : Corner B j k) = 1 := by
  apply Units.ext
  simp [cornerMatrix_zero]

theorem lowerUnip_inv {B : BlockShape n} {j : ℕ} (X : Corner B j k) :
    (lowerUnip X)⁻¹ = lowerUnip (-X) := by
  rw [inv_eq_iff_mul_eq_one, lowerUnip_mul, add_neg_cancel, lowerUnip_zero]

/-- A lower corner unipotent matrix that is coarse upper triangular is the identity. -/
theorem eq_zero_of_blockTriangular_lowerUnip {B : BlockShape n} {j : ℕ} (X : Corner B j k)
    (h : Matrix.BlockTriangular (lowerUnip X : Matrix (Fin n) (Fin n) k) (coarseBlock B j)) :
    X = 0 := by
  funext a b
  have hab : coarseBlock B j b.val < coarseBlock B j a.val :=
    (coarseBlock_lt_iff B j a.val b.val).mpr ⟨b.property, a.property⟩
  have h' := h hab
  have hne : a.val ≠ b.val := fun e => a.property (e ▸ b.property)
  simp only [coe_lowerUnip, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add] at h'
  simpa [cornerMatrix_apply, a.property, b.property] using h'

variable [Finite k]

/-- The representation of a standard parabolic inflated from the Levi tensor of a datum. -/
abbrev parabolicRep (E : HarishChandraDatum n k) :
    Representation ℂ (E.shape.parabolic k) E.leviRep :=
  E.leviRep.ρ.comp (E.shape.leviProjection k)

/-- **Mackey vanishing along a lower corner.** Suppose that no block among the first `j`
carries the cuspidal label of a block after them. For a nontrivial lower corner unipotent
`x`, every linear map `T` with `T ∘ λ(q) = λ(x q x⁻¹) ∘ T` for all `q ∈ P ∩ x⁻¹ P x` is
zero. -/
theorem mackey_lowerCorner_eq_zero (E : HarishChandraDatum n k) (j : ℕ)
    (hdisj : ∀ i i' : Fin E.shape.length, (i : ℕ) < j → j ≤ (i' : ℕ) →
      E.blockLabel i ≠ E.blockLabel i')
    (X : Corner E.shape j k) (hX : X ≠ 0) (T : E.leviRep →ₗ[ℂ] E.leviRep)
    (hT : ∀ (q : E.shape.parabolic k)
      (hq : lowerUnip X * (q : GeneralLinear n k) * (lowerUnip X)⁻¹ ∈ E.shape.parabolic k)
      (v : E.leviRep), T (parabolicRep E q v) = parabolicRep E ⟨_, hq⟩ (T v)) :
    T = 0 := by
  classical
  by_contra hT0
  obtain ⟨w, hw⟩ := (parabolicDoubleCoset_bijective (k := k) E.shape E.shape).2
    (DoubleCoset.mk (E.shape.parabolic k) (E.shape.parabolic k) (lowerUnip X)⁻¹)
  obtain ⟨p₁, hp₁, p₂, hp₂, hx⟩ := DoubleCoset.eq.mp hw
  -- `hx : (lowerUnip X)⁻¹ = p₁ * w' * p₂` with `w' = (permutation w)⁻¹`
  have hxe : lowerUnip X = p₂⁻¹ * (permutation n k w.val) * p₁⁻¹ := by
    rw [← inv_inv (lowerUnip X), hx]
    group
  let ρ := parabolicRep E
  let P₁ : E.shape.parabolic k := ⟨p₁, hp₁⟩
  let P₂ : E.shape.parabolic k := ⟨p₂, hp₂⟩
  have hinv : ∀ (g : E.shape.parabolic k) (v : E.leviRep), ρ g (ρ g⁻¹ v) = v := by
    intro g v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hinv' : ∀ (g : E.shape.parabolic k) (v : E.leviRep), ρ g⁻¹ (ρ g v) = v := by
    intro g v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  -- the transported intertwiner at the minimal representative
  let T' : E.leviRep →ₗ[ℂ] E.leviRep := (ρ P₂) ∘ₗ T ∘ₗ (ρ P₁)
  have hT'0 : T' ≠ 0 := by
    intro h
    apply hT0
    ext v
    have hv : T' (ρ P₁⁻¹ v) = 0 := by rw [h]; rfl
    have e : T v = ρ P₂⁻¹ (T' (ρ P₁⁻¹ v)) := by
      change T v = ρ P₂⁻¹ (ρ P₂ (T (ρ P₁ (ρ P₁⁻¹ v))))
      rw [hinv, hinv']
    rw [e, hv, map_zero, LinearMap.zero_apply]
  have hcomm : ∀ q : orbitStabilizer (E.shape.parabolic k) (E.shape.parabolic k)
      (permutation n k w.val)⁻¹, ∀ v : E.leviRep,
      T' (ρ q.val v) = ρ (stabilizerToInducing (E.shape.parabolic k) (E.shape.parabolic k)
        (permutation n k w.val)⁻¹ q) (T' v) := by
    intro q v
    have hmem : (permutation n k w.val) * (q.val : GeneralLinear n k) *
        (permutation n k w.val)⁻¹ ∈ E.shape.parabolic k := by
      have := q.property
      change (MulAut.conj ((permutation n k w.val)⁻¹)⁻¹) (q.val : GeneralLinear n k) ∈
        E.shape.parabolic k at this
      rwa [MulAut.conj_apply, inv_inv] at this
    have hq₀ : lowerUnip X * (p₁ * (q.val : GeneralLinear n k) * p₁⁻¹) * (lowerUnip X)⁻¹ ∈
        E.shape.parabolic k := by
      have e : lowerUnip X * (p₁ * (q.val : GeneralLinear n k) * p₁⁻¹) * (lowerUnip X)⁻¹ =
          p₂⁻¹ * ((permutation n k w.val) * (q.val : GeneralLinear n k) *
            (permutation n k w.val)⁻¹) * p₂ := by
        rw [hxe]; group
      rw [e]
      exact (E.shape.parabolic k).mul_mem
        ((E.shape.parabolic k).mul_mem ((E.shape.parabolic k).inv_mem hp₂) hmem) hp₂
    let q₀ : E.shape.parabolic k := P₁ * q.val * P₁⁻¹
    have hT₀ := hT q₀ hq₀ (ρ P₁ v)
    have e₁ : ρ P₁ (ρ q.val v) = ρ q₀ (ρ P₁ v) := by
      simp only [q₀, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    have e₂ : (P₂ : E.shape.parabolic k) * ⟨_, hq₀⟩ =
        stabilizerToInducing (E.shape.parabolic k) (E.shape.parabolic k)
          (permutation n k w.val)⁻¹ q * P₂ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, stabilizerToInducing_apply, P₂, inv_inv]
      rw [hxe]; group
    calc T' (ρ q.val v) = ρ P₂ (T (ρ P₁ (ρ q.val v))) := rfl
      _ = ρ P₂ (T (ρ q₀ (ρ P₁ v))) := by rw [e₁]
      _ = ρ P₂ (ρ ⟨_, hq₀⟩ (T (ρ P₁ v))) := by rw [hT₀]; rfl
      _ = ρ (P₂ * ⟨_, hq₀⟩) (T (ρ P₁ v)) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ (stabilizerToInducing (E.shape.parabolic k) (E.shape.parabolic k)
            (permutation n k w.val)⁻¹ q * P₂) (T (ρ P₁ v)) := by rw [e₂]
      _ = _ := by rw [map_mul, Module.End.mul_apply]; rfl
  have hterm : harishChandraMackeyTerm E E w ≠ 0 := by
    let f : MackeyIntertwining (E.shape.parabolic k) (E.shape.parabolic k)
        (pullbackRep (E.shape.leviProjection k) E.leviRep)
        (pullbackRep (E.shape.leviProjection k) E.leviRep) (permutation n k w.val)⁻¹ :=
      { toLinearMap := T'
        isIntertwining' := fun q => by
          ext v
          exact hcomm q v }
    have hf : f ≠ 0 := by
      intro h
      apply hT'0
      ext v
      exact congrArg (fun g : MackeyIntertwining (E.shape.parabolic k) (E.shape.parabolic k)
        (pullbackRep (E.shape.leviProjection k) E.leviRep)
        (pullbackRep (E.shape.leviProjection k) E.leviRep) (permutation n k w.val)⁻¹ => g v) h
    change Module.finrank ℂ (MackeyIntertwining (E.shape.parabolic k) (E.shape.parabolic k)
      (pullbackRep (E.shape.leviProjection k) E.leviRep)
      (pullbackRep (E.shape.leviProjection k) E.leviRep) (permutation n k w.val)⁻¹) ≠ 0
    exact (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨f, hf⟩).ne'
  have hW := conjugatesLevi_of_mackeyTerm_ne_zero E E w hterm
  have hlab := harishChandraMackeyTerm_eq_ite E E w hW
  rw [hlab] at hterm
  have hmatch : ∀ i, E.blockLabel i = E.blockLabel (blockEquiv hW i) := by
    by_contra h
    exact hterm (ite_eq_right_iff.mpr fun h' => absurd h' h)
  -- the representative preserves the first `j` blocks
  have hpres : ∀ a, InFirst E.shape j (w.val a) ↔ InFirst E.shape j a := by
    intro a
    have hblk : blockIndex E.shape (w.val a) = blockEquiv hW (blockIndex E.shape a) :=
      blockIndex_apply_eq_blockMap hW a
    unfold InFirst
    rw [hblk]
    constructor
    · intro h
      by_contra h'
      exact hdisj _ _ h (Nat.le_of_not_lt h') (hmatch (blockIndex E.shape a)).symm
    · intro h
      by_contra h'
      exact hdisj _ _ h (Nat.le_of_not_lt h') (hmatch (blockIndex E.shape a))
  have hpres' : ∀ a, InFirst E.shape j (w.val⁻¹ a) ↔ InFirst E.shape j a := by
    intro a
    have := hpres (w.val⁻¹ a)
    rw [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at this
    exact this.symm
  have hw'tri : Matrix.BlockTriangular
      (((permutation n k w.val)⁻¹ : GeneralLinear n k) : Matrix (Fin n) (Fin n) k)
      (coarseBlock E.shape j) := by
    rw [permutation_inv]
    exact blockTriangular_permutation E.shape j _ hpres'
  have hxtri : Matrix.BlockTriangular
      (((lowerUnip X)⁻¹ : GeneralLinear n k) : Matrix (Fin n) (Fin n) k)
      (coarseBlock E.shape j) := by
    rw [hx]
    simp only [Units.val_mul]
    exact ((blockTriangular_of_mem_parabolic E.shape j hp₁).mul hw'tri).mul
      (blockTriangular_of_mem_parabolic E.shape j hp₂)
  rw [lowerUnip_inv] at hxtri
  exact hX (neg_eq_zero.mp (eq_zero_of_blockTriangular_lowerUnip (-X) hxtri))

section Retraction

variable {H : Type*} [Group H] [Finite H] {W X : Type*} [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

/-- **Maschke averaging.** An injective equivariant map between complex representations of
a finite group has an equivariant left inverse. -/
theorem exists_equivariant_leftInverse (σ : Representation ℂ H W) (τ : Representation ℂ H X)
    (f : W →ₗ[ℂ] X) (hf : ∀ h, f ∘ₗ σ h = τ h ∘ₗ f) (hinj : Function.Injective f) :
    ∃ ψ : X →ₗ[ℂ] W, (∀ h, ψ ∘ₗ τ h = σ h ∘ₗ ψ) ∧ ψ ∘ₗ f = LinearMap.id := by
  classical
  let := Fintype.ofFinite H
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.mpr hinj)
  let c : ℂ := (Fintype.card H : ℂ)⁻¹
  refine ⟨c • ∑ h : H, σ h⁻¹ ∘ₗ φ ∘ₗ τ h, ?_, ?_⟩
  · intro g
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply, map_smul,
      map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun h => ?_)
    simp only [Equiv.coe_mulRight, mul_inv_rev, map_mul, Module.End.mul_apply,
      Representation.self_inv_apply]
  · apply LinearMap.ext
    intro x
    have hterm : ∀ h : H, σ h⁻¹ (φ (τ h (f x))) = x := by
      intro h
      have e₁ : τ h (f x) = f (σ h x) := (LinearMap.congr_fun (hf h) x).symm
      have e₂ : φ (f (σ h x)) = σ h x := LinearMap.congr_fun hφ (σ h x)
      rw [e₁, e₂, Representation.inv_self_apply]
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      LinearMap.id_apply, hterm, Finset.sum_const, Finset.card_univ, c]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr
      Fintype.card_ne_zero), one_smul]

end Retraction

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- **Lower corner terms of a type retraction vanish.** Let `f` embed the inflated Levi
tensor `λ` of a cuspidal datum into a representation `τ` of `GL_n(k)`, equivariantly for the
standard parabolic `P`, and let `ψ` be a `P`-equivariant map back. If no block among the first
`j` carries the label of a later block, then `ψ ∘ τ(x) ∘ f = 0` for every nontrivial lower
corner unipotent `x`. -/
theorem retraction_lowerUnip_eq_zero (E : HarishChandraDatum n k) (j : ℕ)
    (hdisj : ∀ i i' : Fin E.shape.length, (i : ℕ) < j → j ≤ (i' : ℕ) →
      E.blockLabel i ≠ E.blockLabel i')
    (τ : Representation ℂ (GeneralLinear n k) X) (f : E.leviRep →ₗ[ℂ] X)
    (hf : ∀ q : E.shape.parabolic k, f ∘ₗ parabolicRep E q = τ q ∘ₗ f)
    (ψ : X →ₗ[ℂ] E.leviRep)
    (hψ : ∀ q : E.shape.parabolic k, ψ ∘ₗ τ q = parabolicRep E q ∘ₗ ψ)
    (Y : Corner E.shape j k) (hY : Y ≠ 0) :
    ψ ∘ₗ τ (lowerUnip Y) ∘ₗ f = 0 := by
  apply mackey_lowerCorner_eq_zero E j hdisj Y hY
  intro q hq v
  have e₁ : f (parabolicRep E q v) = τ q (f v) := LinearMap.congr_fun (hf q) v
  have e₂ : τ (lowerUnip Y) (τ q (f v)) =
      τ (lowerUnip Y * q * (lowerUnip Y)⁻¹) (τ (lowerUnip Y) (f v)) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  have e₃ := LinearMap.congr_fun (hψ ⟨_, hq⟩) (τ (lowerUnip Y) (f v))
  simp only [LinearMap.comp_apply] at e₃ ⊢
  rw [e₁, e₂]
  exact e₃

end Langlands.BushnellKutzko.SplitTypeJacquet
