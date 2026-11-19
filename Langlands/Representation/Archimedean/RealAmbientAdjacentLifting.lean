import Langlands.Representation.Archimedean.RealAdjacentRotationLifting

/-! # One-sided lifting on an ambient compact degree layer -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealAmbientAdjacentLifting

open Complex RealKTypeCount RealOrthogonalBlock RealOrthogonalUncertainty
open Polynomial (aeval)
open scoped Polynomial
open RealTailMultiplierPolynomial RealPolynomialFourierPropagation RealBlockJacquet

abbrev K (n : ℕ) := Matrix.unitaryGroup (Fin n) ℝ

variable {n a D : ℕ}

/-- The consecutive three-coordinate block embedding on orthogonal groups. -/
def compactBlock (ha : a + 3 ≤ n) : K 3 →* K n where
  toFun g := ⟨blockMat a ha (g : Matrix (Fin 3) (Fin 3) ℝ), by
    change blockMat a ha (g : Matrix (Fin 3) (Fin 3) ℝ) ∈ unitary (Matrix (Fin n) (Fin n) ℝ)
    obtain ⟨h₁, h₂⟩ := Unitary.mem_iff.mp (show
      (g : Matrix (Fin 3) (Fin 3) ℝ) ∈ unitary (Matrix (Fin 3) (Fin 3) ℝ) from g.property)
    rw [Unitary.mem_iff, star_blockMat, blockMat_mul, blockMat_mul, h₁, h₂, blockMat_one]
    exact ⟨rfl, rfl⟩⟩
  map_one' := Subtype.ext (blockMat_one a ha)
  map_mul' g h := Subtype.ext (blockMat_mul a ha _ _).symm

theorem toUnits_compactBlock (ha : a + 3 ≤ n) (g : K 3) :
    Unitary.toUnits (compactBlock ha g) = block a ha (Unitary.toUnits g) :=
  Units.ext rfl

private def blockAlgHom (ha : a + 3 ≤ n) : (K n → ℂ) →ₐ[ℂ] (K 3 → ℂ) :=
  AlgHom.pi fun g => Pi.evalAlgHom ℂ (fun _ : K n => ℂ) (compactBlock ha g)

private theorem entry_block_mem (ha : a + 3 ≤ n) (i j : Fin n) :
    (fun g : K 3 => ((blockMat a ha (g : Matrix (Fin 3) (Fin 3) ℝ) i j : ℝ) : ℂ)) ∈
      linearSpan 3 := by
  have hconst (i j : Fin n) :
      (fun _ : K 3 => (((1 : Matrix (Fin n) (Fin n) ℝ) i j : ℝ) : ℂ)) ∈ linearSpan 3 :=
    one_le_linearSpan (Submodule.mem_one.mpr ⟨_, rfl⟩)
  rcases mem_range_or a ha i with ⟨u, rfl⟩ | hi
  · rcases mem_range_or a ha j with ⟨v, rfl⟩ | hj
    · simp only [blockMat_apply_pos]
      exact entry_mem_linearSpan (n := 3) (u, v)
    · simpa only [blockMat_apply_right a ha _ _ hj] using hconst (pos a ha u) j
  · simpa only [blockMat_apply_left a ha _ hi] using hconst i j

private theorem map_block_linearSpan (ha : a + 3 ≤ n) :
    (linearSpan n).map (blockAlgHom ha).toLinearMap ≤ linearSpan 3 := by
  rw [linearSpan, Submodule.map_sup, Submodule.map_one, Submodule.map_span]
  refine sup_le one_le_linearSpan (Submodule.span_le.mpr ?_)
  rintro _ ⟨_, ⟨⟨i, j⟩, rfl⟩, rfl⟩
  exact entry_block_mem ha i j

private theorem slice_mem (ha : a + 3 ≤ n) (k : K n) (v : degreeLE n D) :
    (fun g : K 3 => (v : K n → ℂ) (compactBlock ha g * k)) ∈ degreeLE 3 D := by
  have h : (degreeLE n D).map (blockAlgHom ha).toLinearMap ≤ degreeLE 3 D := by
    change ((linearSpan n) ^ D).map (blockAlgHom ha).toLinearMap ≤ (linearSpan 3) ^ D
    rw [Submodule.map_pow]
    exact pow_le_pow_left' (map_block_linearSpan ha) D
  exact h ⟨fun x => (v : K n → ℂ) (x * k), right_mem_degreeLE v.property k, rfl⟩

/-- Restriction to a compact coset of the embedded three-coordinate block. -/
def slice (ha : a + 3 ≤ n) (k : K n) : degreeLE n D →ₗ[ℂ] degreeLE 3 D :=
  ((LinearMap.funLeft ℂ ℂ (fun g : K 3 => compactBlock ha g * k)).comp
    (degreeLE n D).subtype).codRestrict _ (slice_mem ha k)

@[simp] theorem slice_apply (ha : a + 3 ≤ n) (k : K n) (v : degreeLE n D) (g : K 3) :
    (slice ha k v : K 3 → ℂ) g = (v : K n → ℂ) (compactBlock ha g * k) := rfl

private theorem eq_of_slices (ha : a + 3 ≤ n) {v w : degreeLE n D}
    (h : ∀ k : K n, slice ha k v = slice ha k w) : v = w := by
  apply Subtype.ext
  funext k
  simpa only [slice_apply, map_one, one_mul] using
    congrArg (fun z : degreeLE 3 D => (z : K 3 → ℂ) 1) (h k)

private def localRight (g : K 3) : Module.End ℂ (degreeLE 3 D) :=
  (rightAlgHom g).toLinearMap.restrict (p := degreeLE 3 D) (q := degreeLE 3 D)
    fun _ hv => right_mem_degreeLE hv g

private theorem localRight_apply (g : K 3) (v : degreeLE 3 D) (x : K 3) :
    (localRight g v : K 3 → ℂ) x = (v : K 3 → ℂ) (x * g) := rfl

private theorem slice_move (ha : a + 3 ≤ n) (g : K 3) (k : K n) (v : degreeLE n D) :
    slice ha (compactBlock ha g * k) v = localRight g (slice ha k v) := by
  apply Subtype.ext
  funext x
  simp only [localRight_apply, slice_apply, map_mul, mul_assoc]

private def degreeEval {n : ℕ} (x : K n) : degreeLE n D →ₗ[ℂ] ℂ :=
  (LinearMap.proj x).comp (degreeLE n D).subtype

private theorem transfer_mem (ha : a + 3 ≤ n) (T : Module.End ℂ (degreeLE 3 D))
    (v : degreeLE n D) : (fun k => (T (slice ha k v) : K 3 → ℂ) 1) ∈ degreeLE n D := by
  let ℓ := (degreeEval (D := D) (1 : K 3)).comp T
  obtain ⟨m, g, b, hb⟩ := exists_sum_of_separating (degreeEval (n := 3) (D := D)) ⊤
    (fun s _ hs => Subtype.ext (funext fun x => hs x)) ℓ
  have heq : (fun k => (T (slice ha k v) : K 3 → ℂ) 1) =
      ∑ i : Fin m, b i • (fun k => (v : K n → ℂ) (compactBlock ha (g i) * k)) := by
    funext k
    simpa only [ℓ, degreeEval, LinearMap.comp_apply, LinearMap.proj_apply,
      Submodule.subtype_apply, slice_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      using hb (slice ha k v) Submodule.mem_top
  rw [heq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (left_mem_degreeLE v.property (compactBlock ha (g i)))

private def transfer (ha : a + 3 ≤ n) (T : Module.End ℂ (degreeLE 3 D)) :
    Module.End ℂ (degreeLE n D) :=
  (LinearMap.pi (fun k => (degreeEval (D := D) (1 : K 3)).comp
    (T.comp (slice ha k)))).codRestrict _ (transfer_mem ha T)

private theorem transfer_apply (ha : a + 3 ≤ n) (T : Module.End ℂ (degreeLE 3 D))
    (v : degreeLE n D) (k : K n) :
    (transfer ha T v : K n → ℂ) k = (T (slice ha k v) : K 3 → ℂ) 1 := rfl

private theorem slice_transfer (ha : a + 3 ≤ n) (T : Module.End ℂ (degreeLE 3 D))
    (hT : ∀ g v, T (localRight g v) = localRight g (T v)) (k : K n) (v : degreeLE n D) :
    slice ha k (transfer ha T v) = T (slice ha k v) := by
  apply Subtype.ext
  funext g
  simp only [slice_apply, transfer_apply, slice_move, hT, localRight_apply, one_mul]

private theorem proj_localRight {r : ℕ} (hr : r + 1 < 3) (j : ℤ) (g : K 3) (v : degreeLE 3 D) :
    proj D hr j (localRight g v) = localRight g (proj D hr j v) := by
  apply Subtype.ext
  funext k
  change projFun r j (fun x => (v : K 3 → ℂ) (x * g)) k =
    projFun r j (v : K 3 → ℂ) (k * g)
  have h : orb r (fun x => (v : K 3 → ℂ) (x * g)) k =
      orb r (v : K 3 → ℂ) (k * g) := by
    funext θ
    simp only [orb, mul_assoc]
  rw [projFun, projFun, h]

private theorem gen_localRight {r : ℕ} (hr : r + 1 < 3) (g : K 3) (v : degreeLE 3 D) :
    gen D hr (localRight g v) = localRight g (gen D hr v) := by
  simp only [gen, LinearMap.sum_apply, LinearMap.smul_apply, proj_localRight hr, map_sum, map_smul]

/-- A mode projection on the ambient compact degree layer. -/
def projection (ha : a + 3 ≤ n) {r : ℕ} (hr : r + 1 < 3) (j : ℤ) :
    Module.End ℂ (degreeLE n D) :=
  transfer ha (proj D hr j)

/-- An adjacent rotation generator on the ambient compact degree layer. -/
def generator (ha : a + 3 ≤ n) {r : ℕ} (hr : r + 1 < 3) :
    Module.End ℂ (degreeLE n D) :=
  transfer ha (gen D hr)

theorem slice_projection (ha : a + 3 ≤ n) {r : ℕ} (hr : r + 1 < 3) (j : ℤ)
    (k : K n) (v : degreeLE n D) :
    slice ha k (projection ha hr j v) = proj D hr j (slice ha k v) :=
  slice_transfer ha _ (proj_localRight hr j) k v

theorem slice_generator (ha : a + 3 ≤ n) {r : ℕ} (hr : r + 1 < 3)
    (k : K n) (v : degreeLE n D) :
    slice ha k (generator ha hr v) = gen D hr (slice ha k v) :=
  slice_transfer ha _ (gen_localRight hr) k v

/-- Restriction of the ambient projection is the normalized left block
Fourier coefficient on the compact group. -/
theorem projection_apply_restrict (ha : a + 3 ≤ n) {r : ℕ} (hr : r + 1 < 3) (j : ℤ)
    (f : Langlands.GeneralLinear n ℝ → ℂ) (hf : restrictLinear n f ∈ degreeLE n D) (k : K n) :
    (projection ha hr j (⟨restrictLinear n f, hf⟩ : degreeLE n D) : K n → ℂ) k =
      (2 * (Real.pi : ℂ))⁻¹ * blockFourierCoefficient n (a + r) j f (Unitary.toUnits k) := by
  rw [projection, transfer_apply]
  have heq : ((slice ha k (⟨restrictLinear n f, hf⟩ : degreeLE n D)) : K 3 → ℂ) =
      restrictLinear 3 (restrictCoset a ha (Unitary.toUnits k) f) := by
    funext y
    simp only [slice_apply, restrictLinear_apply, restrictCoset_apply, map_mul,
      toUnits_compactBlock]
  have hf' := heq ▸ (slice ha k (⟨restrictLinear n f, hf⟩ : degreeLE n D)).property
  rw [show slice ha k (⟨restrictLinear n f, hf⟩ : degreeLE n D) =
      ⟨restrictLinear 3 (restrictCoset a ha (Unitary.toUnits k) f), hf'⟩ from Subtype.ext heq]
  rw [proj_restrict_apply hr j hf', blockFourierCoefficient_restrictCoset a ha hr,
    map_one, map_one, one_mul]

theorem ambient_modes (ha : a + 3 ≤ n) {r : ℕ} (hr : r + 1 < 3) :
    IsModeDecomposition (generator (D := D) ha hr) (projection ha hr)
      (Finset.Icc (-(D : ℤ)) D) := by
  let hM := isModeDecomposition D hr
  constructor
  · intro v
    apply eq_of_slices ha
    intro k
    simp only [map_sum, slice_projection, hM.sum_apply]
  · intro j hj
    apply LinearMap.ext
    intro v
    apply eq_of_slices ha
    intro k
    simp only [LinearMap.zero_apply, map_zero, slice_projection, hM.eq_zero j hj]
  · intro j
    apply LinearMap.ext
    intro v
    apply eq_of_slices ha
    intro k
    simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul, slice_generator,
      slice_projection, hM.apply_proj]
  · intro i j
    apply LinearMap.ext
    intro v
    apply eq_of_slices ha
    intro k
    by_cases hij : i = j
    · subst j
      simp only [↓reduceIte, Module.End.mul_apply, slice_projection, hM.proj_apply_proj]
    · simp only [hij, ↓reduceIte, Module.End.mul_apply, slice_projection, hM.proj_apply_proj,
        LinearMap.zero_apply, map_zero]

/-- A block Fourier polynomial relation on compact values is the corresponding
operator equation on the ambient degree layer. -/
theorem aeval_of_coeff (ha : a + 3 ≤ n) {r : ℕ} (hr : r + 1 < 3)
    (Q : ℂ[X]) (f g : Langlands.GeneralLinear n ℝ → ℂ)
    (hf : restrictLinear n f ∈ degreeLE n D) (hg : restrictLinear n g ∈ degreeLE n D)
    (hfg : ∀ j : ℤ, ∀ k ∈ unitaryCompact ℝ n,
      blockFourierCoefficient n (a + r) j g k =
        Q.eval (j : ℂ) * blockFourierCoefficient n (a + r) j f k) :
    aeval (-I • generator ha hr) Q (⟨restrictLinear n f, hf⟩ : degreeLE n D) =
      (⟨restrictLinear n g, hg⟩ : degreeLE n D) := by
  let x : degreeLE n D := ⟨restrictLinear n f, hf⟩
  let y : degreeLE n D := ⟨restrictLinear n g, hg⟩
  let hM := ambient_modes (D := D) ha hr
  change aeval (-I • generator ha hr) Q x = y
  calc
    _ = ∑ j ∈ Finset.Icc (-(D : ℤ)) D, projection ha hr j (aeval (-I • generator ha hr) Q x) :=
      (hM.sum_apply _).symm
    _ = ∑ j ∈ Finset.Icc (-(D : ℤ)) D, projection ha hr j y := by
      apply Finset.sum_congr rfl
      intro j _
      rw [proj_aeval hM]
      apply Subtype.ext
      funext k
      change Q.eval (j : ℂ) * (projection ha hr j x : K n → ℂ) k =
        (projection ha hr j y : K n → ℂ) k
      dsimp only [x, y]
      rw [projection_apply_restrict, projection_apply_restrict,
        hfg j _ k.property, mul_left_comm]
    _ = y := hM.sum_apply _

theorem ambient_relations (ha : a + 3 ≤ n) {r s : ℕ}
    (hrs : r = 0 ∧ s = 1 ∨ r = 1 ∧ s = 0) (hr : r + 1 < 3) (hs : s + 1 < 3) :
    ∃ c : Module.End ℂ (degreeLE n D),
      generator ha hr * generator ha hs - generator ha hs * generator ha hr = c ∧
      generator ha hs * c - c * generator ha hs = generator ha hr ∧
      c * generator ha hr - generator ha hr * c = generator ha hs := by
  obtain ⟨c, hc, h₁, h₂⟩ := exists_relations D hrs hr hs
  let C := generator (D := D) ha hr * generator ha hs - generator ha hs * generator ha hr
  have hC (k : K n) (v : degreeLE n D) : slice ha k (C v) = c (slice ha k v) := by
    dsimp only [C]
    simp only [LinearMap.sub_apply, map_sub, Module.End.mul_apply, slice_generator]
    exact congrArg (fun T : Module.End ℂ (degreeLE 3 D) => T (slice ha k v)) hc
  refine ⟨C, rfl, ?_, ?_⟩
  · apply LinearMap.ext
    intro v
    apply eq_of_slices ha
    intro k
    simp only [LinearMap.sub_apply, map_sub, Module.End.mul_apply, slice_generator, hC]
    exact congrArg (fun T : Module.End ℂ (degreeLE 3 D) => T (slice ha k v)) h₁
  · apply LinearMap.ext
    intro v
    apply eq_of_slices ha
    intro k
    simp only [LinearMap.sub_apply, map_sub, Module.End.mul_apply, slice_generator, hC]
    exact congrArg (fun T : Module.End ℂ (degreeLE 3 D) => T (slice ha k v)) h₂

/-- The compact polynomial degree layer admits the one-sided lift for either
orientation of its two adjacent block rotations. -/
theorem exists_lift (ha : a + 3 ≤ n) {r s : ℕ}
    (hrs : r = 0 ∧ s = 1 ∨ r = 1 ∧ s = 0) (hr : r + 1 < 3) (hs : s + 1 < 3)
    {N : ℤ} (hN : 0 < N) (H : ℕ) (v : degreeLE n D)
    (hv : ∀ j : ℤ, N + H ≤ j →
      projection ha hr j (aeval (-I • generator ha hs) (tailPolynomial H) v) = 0) :
    ∃ w : degreeLE n D, aeval (-I • generator ha hs) (tailPolynomial H) w = 0 ∧
      ∀ j : ℤ, N ≤ j → projection ha hr j w = projection ha hr j v := by
  obtain ⟨c, hab, hbc, hca⟩ := ambient_relations (D := D) ha hrs hr hs
  exact RealAdjacentRotationLifting.exists_lift hab hbc hca (ambient_modes ha hr)
    (ambient_modes ha hs) hN H v hv

end Langlands.Archimedean.RealAmbientAdjacentLifting

namespace Langlands.Archimedean

open Complex RealTailMultiplierPolynomial RealAmbientAdjacentLifting
open Polynomial (aeval)

/-- The one-sided kernel lift for adjacent block rotations on every ambient
compact polynomial degree layer. -/
def RealAmbientAdjacentLiftingStatement : Prop :=
  ∀ (n a D : ℕ) (ha : a + 3 ≤ n) (r s : ℕ),
    (r = 0 ∧ s = 1 ∨ r = 1 ∧ s = 0) →
    ∀ (hr : r + 1 < 3) (hs : s + 1 < 3) (N : ℤ), 0 < N →
    ∀ (H : ℕ) (v : RealKTypeCount.degreeLE n D),
    (∀ j : ℤ, N + H ≤ j →
      projection ha hr j (aeval (-I • generator ha hs) (tailPolynomial H) v) = 0) →
    ∃ w : RealKTypeCount.degreeLE n D, aeval (-I • generator ha hs) (tailPolynomial H) w = 0 ∧
      ∀ j : ℤ, N ≤ j → projection ha hr j w = projection ha hr j v

theorem realAmbientAdjacentLifting : RealAmbientAdjacentLiftingStatement :=
  fun _ _ _ ha _ _ hrs hr hs _ hN H v => exists_lift ha hrs hr hs hN H v

end Langlands.Archimedean
