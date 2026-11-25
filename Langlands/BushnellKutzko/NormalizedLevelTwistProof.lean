import Langlands.BushnellKutzko.NormalizedLevelTwistStatement
import Langlands.BushnellKutzko.FundamentalStratumLevelProof
import Langlands.ClassFieldTheory.Local.UnitFiltrationConductor
import Langlands.Representation.Smooth.FixedVectors.OrderProof

/-! # Proof of L2: normalized level of a twist

Statement L2 (`NormalizedLevelTwistStatement`), with `k = a(χ) - 1`:
`ℓ(χπ) ≤ max (ℓ(π), k)`, with equality when `ℓ(π) ≠ k`.

* `normalizedLevel_twist_le_and_eq_of_lt` obtains the bound using the determinant on filtered
  unit groups and applies the bound to the inverse twist when `ℓ(π) > k`.
* `normalizedLevel_twist_eq_of_lt` applies `fundamentalStratumLevel` to a scalar stratum
  with an additive character adapted to `χ`.
* `normalizedLevelTwist` assembles the two.
-/

noncomputable section

open ValuativeRel Polynomial

namespace Langlands.BushnellKutzko

universe u uK uV

/-! ### Determinants of matrices that are nilpotent modulo a prime ideal -/

section DetAlgebra

variable {R : Type*} [CommRing R] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- If `N` is nilpotent modulo the prime ideal `I`, every coefficient of positive degree of
`det (1 + X • N)` lies in `I`. -/
theorem coeff_det_one_add_X_smul_mem {I : Ideal R} [I.IsPrime] {N : Matrix κ κ R}
    (hN : IsNilpotent (N.map (Ideal.Quotient.mk I))) {i : ℕ} (hi : i ≠ 0) :
    (Matrix.det (1 + (X : R[X]) • N.map C)).coeff i ∈ I := by
  have hP : (Matrix.det (1 + (X : R[X]) • N.map C)).map (Ideal.Quotient.mk I) =
      Matrix.charpolyRev (-(N.map (Ideal.Quotient.mk I))) := by
    rw [Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
    congr 1
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab]
  have hu := Matrix.isUnit_charpolyRev_of_isNilpotent hN.neg
  have h := (Polynomial.isUnit_iff_coeff_isUnit_isNilpotent.mp hu).2 i hi
  rw [← hP, Polynomial.coeff_map] at h
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact h.eq_zero

/-- If `N` is nilpotent modulo the prime ideal `I`, then `det (1 + t • N) = 1 + t r` with
`r ∈ I`. -/
theorem exists_det_one_add_smul_eq {I : Ideal R} [I.IsPrime] {N : Matrix κ κ R}
    (hN : IsNilpotent (N.map (Ideal.Quotient.mk I))) (t : R) :
    ∃ r ∈ I, Matrix.det (1 + t • N) = 1 + t * r := by
  set P := Matrix.det (1 + (X : R[X]) • N.map C) with hPdef
  have hev : Matrix.det (1 + t • N) = P.eval t := by
    rw [hPdef, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext a b
    by_cases hab : a = b
    · subst hab
      simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul,
        Matrix.map_apply, coe_evalRingHom, RingHom.mapMatrix_apply, eval_add, eval_one,
        eval_mul, eval_X, eval_C]
    · simp only [Matrix.add_apply, Matrix.one_apply_ne hab, Matrix.smul_apply, smul_eq_mul,
        Matrix.map_apply, coe_evalRingHom, RingHom.mapMatrix_apply, eval_add, eval_zero,
        eval_mul, eval_X, eval_C]
  have h0 : P.coeff 0 = 1 := by
    rw [hPdef, coeff_zero_eq_eval_zero, eval_det_add_X_smul, Matrix.det_one, eval_one]
  refine ⟨P.divX.eval t, ?_, ?_⟩
  · rw [eval_eq_sum_range]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [coeff_divX]
    exact Ideal.mul_mem_right _ _ (coeff_det_one_add_X_smul_mem hN (by omega))
  · rw [hev]
    conv_lhs => rw [← divX_mul_X_add P]
    rw [eval_add, eval_mul, eval_X, eval_C, h0]
    ring

end DetAlgebra

/-! ### Lattice chains over a nonarchimedean local field -/

section Lattice

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

namespace LatticeChain

variable {ι : Type*} (𝓛 : LatticeChain 𝒪[F] F (ι → F))

/-- Multiplication by `ϖ^t` shifts the endomorphism filtration by `e t`. -/
private theorem zpow_smul_mem_endFiltration_iff {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    (t : ℤ) {j : ℤ} {x : Module.End F (ι → F)} :
    (ϖ : F) ^ t • x ∈ 𝓛.endFiltration j ↔ x ∈ 𝓛.endFiltration (j - 𝓛.period * t) := by
  simp only [𝓛.mem_endFiltration, LinearMap.smul_apply, 𝓛.zpow_smul_mem_iff hϖ t, add_sub_assoc]

/-- `ϖ^{-k} 𝔓^{j+ek} ⊆ 𝔓^j`. -/
private theorem inv_pow_smul_mem_endFiltration {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (k : ℕ) {j : ℤ}
    {x : Module.End F (ι → F)} (hx : x ∈ 𝓛.endFiltration (j + 𝓛.period * k)) :
    ((ϖ : F) ^ k)⁻¹ • x ∈ 𝓛.endFiltration j := by
  rw [← zpow_natCast, ← zpow_neg, 𝓛.zpow_smul_mem_endFiltration_iff hϖ, mul_neg, sub_neg_eq_add]
  exact hx

/-- `ϖ^k 𝔓^j ⊆ 𝔓^{j+ek}`. -/
private theorem pow_smul_mem_endFiltration {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (k : ℕ) {j : ℤ}
    {x : Module.End F (ι → F)} (hx : x ∈ 𝓛.endFiltration j) :
    (ϖ : F) ^ k • x ∈ 𝓛.endFiltration (j + 𝓛.period * k) := by
  rw [← zpow_natCast, 𝓛.zpow_smul_mem_endFiltration_iff hϖ, add_sub_cancel_right]
  exact hx

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `𝔓^j 𝔓^{j'} ⊆ 𝔓^{j+j'}`, iterated. -/
theorem pow_mem_endFiltration {j : ℤ} {x : Module.End F (ι → F)} (hx : x ∈ 𝓛.endFiltration j)
    (r : ℕ) : x ^ r ∈ 𝓛.endFiltration (j * r) := by
  induction r with
  | zero =>
    simpa using (𝓛.mem_order_iff_mem_endFiltration).1 (one_mem 𝓛.order)
  | succ r ih =>
    rw [pow_succ]
    have h := 𝓛.mul_mem_endFiltration ih hx
    rwa [show j * (r : ℤ) + j = j * (r + 1 : ℕ) by push_cast; ring] at h

section Basis

/-- The index type of a chosen `𝒪_F`-basis of `L_0`. -/
abbrev BasisIndex := Fin (Module.finrank 𝒪[F] (𝓛.lattice 0))

/-- A chosen `𝒪_F`-basis of `L_0`. -/
def basisZero : Module.Basis 𝓛.BasisIndex 𝒪[F] (𝓛.lattice 0) :=
  Module.finBasis 𝒪[F] (𝓛.lattice 0)

/-- The `F`-basis of `F^ι` given by the chosen basis of `L_0`. -/
def basisF : Module.Basis 𝓛.BasisIndex F (ι → F) :=
  𝓛.basisZero.extendOfIsLattice F

theorem basisF_apply (a : 𝓛.BasisIndex) : 𝓛.basisF a = (𝓛.basisZero a : ι → F) :=
  Module.Basis.extendOfIsLattice_apply F _ a

/-- Coordinates of a vector of `L_0` in `basisF` are integral. -/
theorem basisF_repr_of_mem {w : ι → F} (hw : w ∈ 𝓛.lattice 0) (a : 𝓛.BasisIndex) :
    𝓛.basisF.repr w a = algebraMap 𝒪[F] F (𝓛.basisZero.repr ⟨w, hw⟩ a) := by
  have hsum : w = ∑ b, (algebraMap 𝒪[F] F (𝓛.basisZero.repr ⟨w, hw⟩ b)) • 𝓛.basisF b := by
    have h := congrArg (Subtype.val) (𝓛.basisZero.sum_repr ⟨w, hw⟩)
    rw [Submodule.coe_sum] at h
    change _ = w at h
    refine h.symm.trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [Submodule.coe_smul_of_tower, basisF_apply, algebraMap_smul]
  conv_lhs => rw [hsum]
  rw [Module.Basis.repr_sum_self]

/-- The integral matrix, in the chosen basis of `L_0`, of an endomorphism preserving `L_0`. -/
def intMatrix (x : Module.End F (ι → F)) (hx : ∀ v ∈ 𝓛.lattice 0, x v ∈ 𝓛.lattice 0) :
    Matrix 𝓛.BasisIndex 𝓛.BasisIndex 𝒪[F] :=
  Matrix.of fun a b => 𝓛.basisZero.repr ⟨x (𝓛.basisZero b), hx _ (𝓛.basisZero b).2⟩ a

theorem toMatrix_eq_map_intMatrix (x : Module.End F (ι → F))
    (hx : ∀ v ∈ 𝓛.lattice 0, x v ∈ 𝓛.lattice 0) :
    LinearMap.toMatrix 𝓛.basisF 𝓛.basisF x = (𝓛.intMatrix x hx).map (algebraMap 𝒪[F] F) := by
  ext a b
  rw [LinearMap.toMatrix_apply, basisF_apply, 𝓛.basisF_repr_of_mem (hx _ (𝓛.basisZero b).2)]
  rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem maps_lattice_zero_of_mem {j : ℤ} (hj : 0 ≤ j) {x : Module.End F (ι → F)}
    (hx : x ∈ 𝓛.endFiltration j) : ∀ v ∈ 𝓛.lattice 0, x v ∈ 𝓛.lattice 0 := by
  intro v hv
  exact 𝓛.antitone (by omega) (by simpa using hx 0 v hv)

/-- For `y ∈ 𝔓^1`, the integral matrix of `y` is nilpotent modulo `𝔭_F`. -/
theorem isNilpotent_intMatrix_map {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {y : Module.End F (ι → F)}
    (hy : y ∈ 𝓛.endFiltration 1) :
    IsNilpotent ((𝓛.intMatrix y (𝓛.maps_lattice_zero_of_mem zero_le_one hy)).map
      (Ideal.Quotient.mk 𝓂[F])) := by
  set e := 𝓛.period
  have hye : y ^ e ∈ 𝓛.endFiltration (0 + e * 1) := by
    simpa using 𝓛.pow_mem_endFiltration hy e
  have hz := 𝓛.inv_pow_smul_mem_endFiltration hϖ 1 hye
  rw [pow_one] at hz
  set z := ((ϖ : F))⁻¹ • y ^ e with hzdef
  have hne : (ϖ : F) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  have hyz : y ^ e = (ϖ : F) • z := by
    rw [hzdef, smul_smul, mul_inv_cancel₀ hne, one_smul]
  have hzl := 𝓛.maps_lattice_zero_of_mem le_rfl hz
  have hyl := 𝓛.maps_lattice_zero_of_mem zero_le_one hy
  have hmat : (𝓛.intMatrix y hyl) ^ e = ϖ • 𝓛.intMatrix z hzl := by
    apply Matrix.map_injective (f := algebraMap 𝒪[F] F) (FaithfulSMul.algebraMap_injective _ _)
    dsimp only
    rw [Matrix.map_pow, ← toMatrix_eq_map_intMatrix, LinearMap.toMatrix_pow, hyz,
      map_smul, toMatrix_eq_map_intMatrix]
    ext a b
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul]
    rfl
  refine ⟨e, ?_⟩
  rw [← Matrix.map_pow, hmat]
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.zero_apply]
  rw [(Ideal.Quotient.eq_zero_iff_mem).2 ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit),
    zero_mul]

/-- **Determinant lemma.** For `x ∈ 𝔓^{ek+1}`, `det (1 + x) = 1 + r` with `r ∈ 𝔭_F^{k+1}`. -/
theorem exists_det_one_add_eq (k : ℕ) {x : Module.End F (ι → F)}
    (hx : x ∈ 𝓛.endFiltration (𝓛.period * k + 1)) :
    ∃ r : 𝒪[F], r ∈ 𝓂[F] ^ (k + 1) ∧ LinearMap.det (1 + x) = 1 + (r : F) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hy := 𝓛.inv_pow_smul_mem_endFiltration hϖ k (j := 1) (by rwa [add_comm])
  set y := (((ϖ : F)) ^ k)⁻¹ • x with hydef
  have hne : (ϖ : F) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  have hxy : x = ((ϖ : F)) ^ k • y := by
    rw [hydef, smul_smul, mul_inv_cancel₀ (pow_ne_zero k hne), one_smul]
  have hyl := 𝓛.maps_lattice_zero_of_mem zero_le_one hy
  obtain ⟨s, hs, hdet⟩ := exists_det_one_add_smul_eq (𝓛.isNilpotent_intMatrix_map hϖ hy) (ϖ ^ k)
  refine ⟨ϖ ^ k * s, ?_, ?_⟩
  · rw [pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow ((IsLocalRing.mem_maximalIdeal _).2
      hϖ.not_isUnit) k) hs
  · rw [← LinearMap.det_toMatrix 𝓛.basisF, hxy, map_add, LinearMap.toMatrix_one,
      map_smul, toMatrix_eq_map_intMatrix _ _ hyl]
    have : (1 : Matrix 𝓛.BasisIndex 𝓛.BasisIndex F) +
        ((ϖ : F)) ^ k • (𝓛.intMatrix y hyl).map (algebraMap 𝒪[F] F) =
        (algebraMap 𝒪[F] F).mapMatrix (1 + ϖ ^ k • 𝓛.intMatrix y hyl) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, Matrix.map_apply,
          RingHom.mapMatrix_apply, smul_eq_mul, map_add, map_one, map_mul, map_pow]
        rfl
      · simp only [Matrix.add_apply, Matrix.one_apply_ne hab, Matrix.smul_apply,
          Matrix.map_apply, RingHom.mapMatrix_apply, smul_eq_mul, map_add, map_zero, map_mul,
          map_pow]
        rfl
    rw [this, ← RingHom.map_det, hdet, map_add, map_one]
    rfl

/-- **Determinant and trace.** For `z ∈ 𝔓^{ek}`, with `s = tr(ϖ^{-k} z) ∈ 𝔬_F`,
`det (1 + z) = 1 + ϖ^k (s + ϖ^k q)` for some `q ∈ 𝔬_F`. -/
theorem exists_det_one_add_eq_trace (k : ℕ) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {z : Module.End F (ι → F)} (hz : z ∈ 𝓛.endFiltration (𝓛.period * k)) :
    ∃ s q : 𝒪[F], LinearMap.trace F (ι → F) ((((ϖ : F)) ^ k)⁻¹ • z) = s ∧
      LinearMap.det (1 + z) = ((1 + ϖ ^ k * (s + ϖ ^ k * q) : 𝒪[F]) : F) := by
  have hy := 𝓛.inv_pow_smul_mem_endFiltration hϖ k (j := 0) (by rwa [zero_add])
  set y := (((ϖ : F)) ^ k)⁻¹ • z with hydef
  have hne : (ϖ : F) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  have hzy : z = ((ϖ : F)) ^ k • y := by
    rw [hydef, smul_smul, mul_inv_cancel₀ (pow_ne_zero k hne), one_smul]
  have hyl := 𝓛.maps_lattice_zero_of_mem le_rfl hy
  refine ⟨(𝓛.intMatrix y hyl).trace,
    (Matrix.det (1 + (X : 𝒪[F][X]) • (𝓛.intMatrix y hyl).map C)).divX.divX.eval (ϖ ^ k),
    ?_, ?_⟩
  · rw [LinearMap.trace_eq_matrix_trace F 𝓛.basisF, toMatrix_eq_map_intMatrix _ _ hyl]
    exact (AddMonoidHom.map_trace (algebraMap 𝒪[F] F) (𝓛.intMatrix y hyl)).symm
  · rw [← LinearMap.det_toMatrix 𝓛.basisF, hzy, map_add, LinearMap.toMatrix_one,
      map_smul, toMatrix_eq_map_intMatrix _ _ hyl]
    have : (1 : Matrix 𝓛.BasisIndex 𝓛.BasisIndex F) +
        ((ϖ : F)) ^ k • (𝓛.intMatrix y hyl).map (algebraMap 𝒪[F] F) =
        (algebraMap 𝒪[F] F).mapMatrix (1 + ϖ ^ k • 𝓛.intMatrix y hyl) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, Matrix.map_apply,
          RingHom.mapMatrix_apply, smul_eq_mul, map_add, map_one, map_mul, map_pow]
        rfl
      · simp only [Matrix.add_apply, Matrix.one_apply_ne hab, Matrix.smul_apply,
          Matrix.map_apply, RingHom.mapMatrix_apply, smul_eq_mul, map_add, map_zero, map_mul,
          map_pow]
        rfl
    rw [this, ← RingHom.map_det, Matrix.det_one_add_smul]
    rw [show ∀ t : 𝒪[F], algebraMap 𝒪[F] F t = (t : F) from fun _ => rfl]
    congr 1
    ring

/-- **The scalar stratum is fundamental.** For `y ∈ 𝔓^{1-ek}`, `ϖ^{-k} + y` is not nilpotent. -/
theorem not_isNilpotent_inv_pow_smul_add [Fintype ι] [Nonempty ι] (k : ℕ) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) {y : Module.End F (ι → F)}
    (hy : y ∈ 𝓛.endFiltration (1 - 𝓛.period * k)) :
    ¬ IsNilpotent ((((ϖ : F)) ^ k)⁻¹ • (1 : Module.End F (ι → F)) + y) := by
  rintro ⟨N, hN⟩
  have hne : (ϖ : F) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  have hw := 𝓛.pow_smul_mem_endFiltration hϖ k hy
  rw [sub_add_cancel] at hw
  have h1 : ((ϖ : F)) ^ k • ((((ϖ : F)) ^ k)⁻¹ • (1 : Module.End F (ι → F)) + y) =
      1 + ((ϖ : F)) ^ k • y := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ (pow_ne_zero k hne), one_smul]
  obtain ⟨r, hr, hdet⟩ := 𝓛.exists_det_one_add_eq 0 (x := ((ϖ : F)) ^ k • y) (by simpa using hw)
  have hzero : LinearMap.det (1 + ((ϖ : F)) ^ k • y) = 0 := by
    rw [← h1]
    have hpow : (((ϖ : F)) ^ k • ((((ϖ : F)) ^ k)⁻¹ • (1 : Module.End F (ι → F)) + y)) ^ N =
        0 := by
      rw [_root_.smul_pow, hN, smul_zero]
    have h2 := congrArg LinearMap.det hpow
    rw [map_pow, LinearMap.det_zero, Module.finrank_fintype_fun_eq_card,
      zero_pow Fintype.card_ne_zero] at h2
    exact IsReduced.eq_zero _ ⟨N, h2⟩
  rw [hdet] at hzero
  have hr1 : r ∈ 𝓂[F] := by simpa using hr
  have h0 : (1 + r : 𝒪[F]) = 0 := Subtype.ext (by simpa using hzero)
  have hone : (1 : 𝒪[F]) ∈ 𝓂[F] := by
    rw [eq_neg_of_add_eq_zero_left h0]
    exact neg_mem hr1
  exact (IsLocalRing.maximalIdeal.isMaximal 𝒪[F]).ne_top ((Ideal.eq_top_iff_one _).2 hone)

end Basis

end LatticeChain

end Lattice

/-! ### Fixed vectors under restriction and twisting -/

section FixedVectors

universe uR uG

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- A class with a vector fixed by `H'` has one fixed by every `H ≤ H'`. -/
private theorem hasFixedVector_of_le {H H' : Subgroup G} (hHH' : H ≤ H')
    {a : SmoothDualClass.{uR, uG, uV} (k := k) (G := G)}
    (ha : SmoothDualClass.HasFixedVector H' a) : SmoothDualClass.HasFixedVector H a := by
  induction a using Quotient.inductionOn with
  | h A =>
    change fixedVectors A.obj.representation H' ≠ ⊥ at ha
    change fixedVectors A.obj.representation H ≠ ⊥
    exact fun hbot => ha (eq_bot_iff.2 ((Langlands.fixedVectors_antitone _ hHH').trans hbot.le))

/-- Twisting by a character trivial on `H` preserves having an `H`-fixed vector. -/
private theorem hasFixedVector_twist_iff (χ : G →* kˣ) (hχ : IsOpen (χ.ker : Set G)) {H : Subgroup G}
    (hχH : ∀ h ∈ H, χ h = 1) (a : SmoothDualClass.{uR, uG, uV} (k := k) (G := G)) :
    SmoothDualClass.HasFixedVector H (SmoothDualClass.twist χ hχ a) ↔
      SmoothDualClass.HasFixedVector H a := by
  induction a using Quotient.inductionOn with
  | h A =>
    change fixedVectors (Langlands.twist χ A.obj.representation) H ≠ ⊥ ↔
      fixedVectors A.obj.representation H ≠ ⊥
    rw [fixedVectors_twist_eq_of_le_ker χ _ H hχH]

end FixedVectors

/-! ### Extending additive characters -/

section Extension

/-- `ℂˣ` is divisible: an `n`-th root of `z` is `exp (log z / n)`. -/
@[instance_reducible]
def divisibleByUnitsComplex : DivisibleBy (Additive ℂˣ) ℤ :=
  divisibleByOfSMulRightSurj (Additive ℂˣ) ℤ fun {n} hn x => by
    have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.2 hn
    refine ⟨Additive.ofMul (Units.mk0
      (Complex.exp (Complex.log ((Additive.toMul x : ℂˣ) : ℂ) / n)) (Complex.exp_ne_zero _)), ?_⟩
    show n • Additive.ofMul _ = x
    rw [← ofMul_zpow]
    apply Additive.toMul.injective
    rw [toMul_ofMul]
    ext
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← Complex.exp_int_mul,
      show (n : ℂ) * (Complex.log ((Additive.toMul x : ℂˣ) : ℂ) / n) =
        Complex.log ((Additive.toMul x : ℂˣ) : ℂ) by field_simp,
      Complex.exp_log (Units.ne_zero _)]

/-- A homomorphism from a subgroup into `ℂˣ` extends to an additive character of the whole
group (`ℂˣ` is divisible, hence an injective `ℤ`-module). -/
theorem exists_addChar_comp_eq {M N : Type*} [AddCommGroup M] [AddCommGroup N] (f : M →+ N)
    (hf : Function.Injective f) (g : M →+ Additive ℂˣ) :
    ∃ ψ : AddChar N ℂ, ∀ m, ψ (f m) = ((Additive.toMul (g m) : ℂˣ) : ℂ) := by
  obtain ⟨h, hh⟩ := (@Module.Baer.of_divisible (Additive ℂˣ) _
    divisibleByUnitsComplex).extension_property_addMonoidHom f hf g
  refine ⟨{ toFun := fun x => ((Additive.toMul (h x) : ℂˣ) : ℂ)
            map_zero_eq_one' := by simp
            map_add_eq_mul' := fun x y => by simp }, fun m => ?_⟩
  change ((Additive.toMul (h (f m)) : ℂˣ) : ℂ) = _
  rw [← hh]
  rfl

end Extension

/-! ### The upper bound -/

section Instances

local instance nlTwistTopologicalSpace {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance nlTwistValuativeRel {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance nlTwistLocalField {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

local instance nlTwistTopologicalSpaceGL {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

theorem unitSubgroup_antitone {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) {n : ℕ}
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin n → K.Carrier)) {i j : ℕ} (hij : i ≤ j) :
    unitSubgroup K 𝓛 j ≤ unitSubgroup K 𝓛 i := fun _ hg =>
  𝓛.unitFiltration_antitone hij hg

/-- `det U^{e k + 1}(𝔄) ⊆ U^{k+1}_K`. -/
theorem det_mem_principalUnits {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) {n : ℕ}
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin n → K.Carrier)) (k : ℕ)
    {g : GeneralLinear n K.Carrier} (hg : g ∈ unitSubgroup K 𝓛 (𝓛.period * k + 1)) :
    GeneralLinear.determinant g ∈ K.canonicalTopologicalData.principalUnits (k + 1) := by
  have hx : (Matrix.GeneralLinearGroup.toLin g : Module.End K.Carrier (Fin n → K.Carrier)) - 1 ∈
      𝓛.endFiltration ((𝓛.period : ℤ) * k + 1) := by
    have h := hg.2.2
    push_cast at h
    exact h
  obtain ⟨r, hr, hdet⟩ := 𝓛.exists_det_one_add_eq k hx
  rw [add_sub_cancel, Matrix.GeneralLinearGroup.coe_toLin, ← Matrix.toLin'_apply',
    LinearMap.det_toLin'] at hdet
  have hv := (K.canonicalTopologicalData.mem_maximalIdeal_pow_iff_discreteValuation_le
    (k + 1) r).1 hr
  have hlt : K.canonicalTopologicalData.discreteValuation (r : K.Carrier) < 1 :=
    lt_of_le_of_lt hv (by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega)
  refine ⟨?_, ?_⟩
  · change K.canonicalTopologicalData.discreteValuation ((g : Matrix (Fin n) (Fin n) K.Carrier).det) = 1
    rw [hdet]
    exact Valuation.map_one_add_of_lt _ hlt
  · change K.canonicalTopologicalData.discreteValuation ((g : Matrix (Fin n) (Fin n) K.Carrier).det - 1) ≤ _
    rw [hdet, add_sub_cancel_left]
    exact hv

/-- `χ ∘ det` is trivial on `U^{e k + 1}(𝔄)` when `k = a(χ) - 1`. -/
theorem determinantCharacter_eq_one {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) {n : ℕ}
    (χ : HarmonicAnalysis.Quasicharacter K.Carrier) {k : ℕ}
    (hk : k = K.canonicalTopologicalData.multiplicativeConductor χ - 1)
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin n → K.Carrier))
    {g : GeneralLinear n K.Carrier} (hg : g ∈ unitSubgroup K 𝓛 (𝓛.period * k + 1)) :
    (χ.toMonoidHom.comp (GeneralLinear.determinant (n := n))) g = 1 := by
  have htriv : K.canonicalTopologicalData.MultiplicativeTrivialAt χ (k + 1) :=
    (K.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le χ (k + 1)).2
      (by omega)
  exact htriv _ (det_mem_principalUnits K 𝓛 k hg)

/-- If `φ` is trivial on every `U^{e(𝓛) k + 1}(𝔄(𝓛))`, then for every normalized-level value
`x` of `a`, `max x k` is a normalized-level value of the twist of `a` by `φ`. -/
theorem max_mem_normalizedLevelValues_twist {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
    (n : ℕ) (φ : GeneralLinear n K.Carrier →* ℂˣ)
    (hφ : IsOpen (φ.ker : Set (GeneralLinear n K.Carrier))) (k : ℕ)
    (hφk : ∀ (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin n → K.Carrier)),
      ∀ g ∈ unitSubgroup K 𝓛 (𝓛.period * k + 1), φ g = 1)
    {a : SmoothDualClass.{0, uK, uV} (k := ℂ) (G := GeneralLinear n K.Carrier)} {x : ℚ}
    (hx : x ∈ normalizedLevelValues K n a) :
    max x (k : ℚ) ∈ normalizedLevelValues K n (SmoothDualClass.twist φ hφ a) := by
  obtain ⟨𝓛, m, rfl, hm⟩ := hx
  refine ⟨𝓛, max m (𝓛.period * k), ?_, ?_⟩
  · have he : (0 : ℚ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
    rw [Nat.cast_max, ← max_div_div_right he.le, Nat.cast_mul, mul_div_cancel_left₀ _ he.ne']
  · rw [hasFixedVector_twist_iff φ hφ
      (fun g hg => hφk 𝓛 g (unitSubgroup_antitone K 𝓛 (by omega) hg))]
    exact hasFixedVector_of_le (unitSubgroup_antitone K 𝓛 (by omega)) hm

/-- **Upper bound in L2.** With `k = a(χ) - 1`, normalized levels `x` of `a` and `y` of its
twist by `χ ∘ det` satisfy `y ≤ max x k`, and `y = x` when `x > k`. -/
theorem normalizedLevel_twist_le_and_eq_of_lt {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
    (n : ℕ) (χ : HarmonicAnalysis.Quasicharacter K.Carrier) (k : ℕ)
    (hk : k = K.canonicalTopologicalData.multiplicativeConductor χ - 1)
    (a : SmoothDualClass.{0, uK, uV} (k := ℂ) (G := GeneralLinear n K.Carrier)) (x y : ℚ)
    (hx : IsNormalizedLevel K n a x)
    (hy : IsNormalizedLevel K n
      (SmoothDualClass.twist (χ.toMonoidHom.comp (GeneralLinear.determinant (n := n)))
        (isOpen_ker_determinantCharacter K n χ) a) y) :
    y ≤ max x (k : ℚ) ∧ ((k : ℚ) < x → y = x) := by
  set φ := χ.toMonoidHom.comp (GeneralLinear.determinant (n := n)) with hφdef
  have hφ := isOpen_ker_determinantCharacter K n χ
  have h1 : ∀ (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin n → K.Carrier)),
      ∀ g ∈ unitSubgroup K 𝓛 (𝓛.period * k + 1), φ g = 1 := fun 𝓛 g hg =>
    determinantCharacter_eq_one K χ hk 𝓛 hg
  have hle := hy.2 (max_mem_normalizedLevelValues_twist K n φ hφ k h1 hx.1)
  refine ⟨hle, fun hkx => ?_⟩
  have hker : ((φ⁻¹).ker : Set (GeneralLinear n K.Carrier)) = φ.ker := by
    ext g
    simp [MonoidHom.mem_ker]
  have hφinv : IsOpen ((φ⁻¹).ker : Set (GeneralLinear n K.Carrier)) := by
    rw [hker]
    exact hφ
  have h2 : ∀ (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin n → K.Carrier)),
      ∀ g ∈ unitSubgroup K 𝓛 (𝓛.period * k + 1), φ⁻¹ g = 1 := fun 𝓛 g hg => by
    rw [MonoidHom.inv_apply, h1 𝓛 g hg, inv_one]
  have hone : φ⁻¹ * φ = 1 := by
    ext g
    simp
  have hback : ∀ h : IsOpen ((φ⁻¹ * φ).ker : Set (GeneralLinear n K.Carrier)),
      SmoothDualClass.twist (φ⁻¹ * φ) h a = a := by
    rw [hone]
    intro h
    exact SmoothDualClass.twist_one h a
  have hmem := max_mem_normalizedLevelValues_twist K n φ⁻¹ hφinv k h2 hy.1
  have hφφ : IsOpen ((φ⁻¹ * φ).ker : Set (GeneralLinear n K.Carrier)) := by
    rw [hone]
    simp
  rw [SmoothDualClass.twist_twist φ⁻¹ φ hφinv hφ hφφ, hback] at hmem
  have hx' := hx.2 hmem
  rw [max_eq_left hkx.le] at hle
  rcases le_max_iff.1 hx' with h | h
  · exact le_antisymm hle h
  · exact absurd h (not_le.2 hkx)

/-! ### The case `ℓ(π) < sw(χ)`: reduction to L1 -/

/-- For `r ∈ 𝔭^j` with `j ≥ 1`, `1 + r` has valuation `1`. -/
theorem discreteValuation_coe_one_add {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) {j : ℕ}
    (hj : 1 ≤ j) {r : 𝒪[K.Carrier]} (hr : r ∈ 𝓂[K.Carrier] ^ j) :
    K.canonicalTopologicalData.discreteValuation ((1 + r : 𝒪[K.Carrier]) : K.Carrier) = 1 := by
  have hv := (K.canonicalTopologicalData.mem_maximalIdeal_pow_iff_discreteValuation_le j r).1 hr
  have hlt : K.canonicalTopologicalData.discreteValuation (r : K.Carrier) < 1 :=
    lt_of_le_of_lt hv (by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega)
  push_cast
  exact Valuation.map_one_add_of_lt _ hlt

/-- If `u, u'` have valuation `1`, `v(u' - u) ≤ q^{-j}` and `χ` is trivial on `U^j_K`, then
`χ u' = χ u`. -/
theorem quasicharacter_eq_of_sub {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
    (χ : HarmonicAnalysis.Quasicharacter K.Carrier) {j : ℕ}
    (hχ : K.canonicalTopologicalData.MultiplicativeTrivialAt χ j) {u u' : K.Carrierˣ}
    (hu : K.canonicalTopologicalData.discreteValuation (u : K.Carrier) = 1)
    (hu' : K.canonicalTopologicalData.discreteValuation (u' : K.Carrier) = 1)
    (hd : K.canonicalTopologicalData.discreteValuation ((u' : K.Carrier) - u) ≤
      WithZero.exp (-(j : ℤ))) :
    χ u' = χ u := by
  have hw : u⁻¹ * u' ∈ K.canonicalTopologicalData.principalUnits j := by
    rw [K.canonicalTopologicalData.mem_principalUnits, Units.val_mul, Units.val_inv_eq_inv_val]
    refine ⟨?_, ?_⟩
    · rw [map_mul, map_inv₀, hu, hu', inv_one, one_mul]
    · rw [show (u : K.Carrier)⁻¹ * u' - 1 = (u : K.Carrier)⁻¹ * ((u' : K.Carrier) - u) by
          rw [mul_sub, inv_mul_cancel₀ u.ne_zero],
        map_mul, map_inv₀, hu, inv_one, one_mul]
      exact hd
  have h := hχ _ hw
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  exact h.symm

/-- `ϖ^k s ∈ 𝔭^k`. -/
theorem pow_mul_mem_maximalIdeal_pow {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
    {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ) (k : ℕ) (s : 𝒪[K.Carrier]) :
    ϖ ^ k * s ∈ 𝓂[K.Carrier] ^ k :=
  Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ((IsLocalRing.mem_maximalIdeal _).2
    hϖ.not_isUnit) k)

/-- For `k ≥ 1` and `s ∈ 𝔬_K`, the unit `1 + ϖ^k s` of `K`. -/
def principalUnit {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) {ϖ : 𝒪[K.Carrier]}
    (hϖ : Irreducible ϖ) {k : ℕ} (hk : 1 ≤ k) (s : 𝒪[K.Carrier]) : K.Carrierˣ :=
  Units.mk0 ((1 + ϖ ^ k * s : 𝒪[K.Carrier]) : K.Carrier) fun h0 => by
    have h := discreteValuation_coe_one_add K hk (pow_mul_mem_maximalIdeal_pow K hϖ k s)
    rw [h0, map_zero] at h
    exact zero_ne_one h

theorem principalUnit_val {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) {ϖ : 𝒪[K.Carrier]}
    (hϖ : Irreducible ϖ) {k : ℕ} (hk : 1 ≤ k) (s : 𝒪[K.Carrier]) :
    (principalUnit K hϖ hk s : K.Carrier) = ((1 + ϖ ^ k * s : 𝒪[K.Carrier]) : K.Carrier) :=
  Units.val_mk0 _

theorem principalUnit_zero {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) {ϖ : 𝒪[K.Carrier]}
    (hϖ : Irreducible ϖ) {k : ℕ} (hk : 1 ≤ k) : principalUnit K hϖ hk 0 = 1 :=
  Units.ext (by simp [principalUnit_val])

theorem principalUnit_mul {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) {ϖ : 𝒪[K.Carrier]}
    (hϖ : Irreducible ϖ) {k : ℕ} (hk : 1 ≤ k) (s s' : 𝒪[K.Carrier]) :
    principalUnit K hϖ hk s * principalUnit K hϖ hk s' =
      principalUnit K hϖ hk (s + s' + ϖ ^ k * (s * s')) := by
  apply Units.ext
  rw [Units.val_mul, principalUnit_val, principalUnit_val, principalUnit_val]
  push_cast
  ring

/-- If `χ` is trivial on `U^{k+1}_K` and `m ∈ 𝔭_K`, then `χ(1 + ϖ^k (s + m)) = χ(1 + ϖ^k s)`. -/
theorem quasicharacter_principalUnit_add {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
    (χ : HarmonicAnalysis.Quasicharacter K.Carrier) {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ)
    {k : ℕ} (hk : 1 ≤ k) (hχ : K.canonicalTopologicalData.MultiplicativeTrivialAt χ (k + 1))
    (s m : 𝒪[K.Carrier]) (hm : m ∈ 𝓂[K.Carrier]) :
    χ (principalUnit K hϖ hk (s + m)) = χ (principalUnit K hϖ hk s) := by
  have hmem : ϖ ^ k * m ∈ 𝓂[K.Carrier] ^ (k + 1) := by
    rw [pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow ((IsLocalRing.mem_maximalIdeal _).2
      hϖ.not_isUnit) k) hm
  refine quasicharacter_eq_of_sub K χ hχ ?_ ?_ ?_
  · rw [principalUnit_val]
    exact discreteValuation_coe_one_add K hk (pow_mul_mem_maximalIdeal_pow K hϖ k s)
  · rw [principalUnit_val]
    exact discreteValuation_coe_one_add K hk (pow_mul_mem_maximalIdeal_pow K hϖ k (s + m))
  · rw [principalUnit_val, principalUnit_val,
      show ((1 + ϖ ^ k * (s + m) : 𝒪[K.Carrier]) : K.Carrier) -
          ((1 + ϖ ^ k * s : 𝒪[K.Carrier]) : K.Carrier) =
        ((ϖ ^ k * m : 𝒪[K.Carrier]) : K.Carrier) by push_cast; ring]
    exact (K.canonicalTopologicalData.mem_maximalIdeal_pow_iff_discreteValuation_le (k + 1)
      _).1 hmem

/-- `s ↦ χ(1 + ϖ^k s)` is a homomorphism `𝔬_K → ℂˣ` when `χ` is trivial on `U^{k+1}_K`. -/
theorem quasicharacter_principalUnit_add_eq_mul {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
    (χ : HarmonicAnalysis.Quasicharacter K.Carrier) {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ)
    {k : ℕ} (hk : 1 ≤ k) (hχ : K.canonicalTopologicalData.MultiplicativeTrivialAt χ (k + 1))
    (s s' : 𝒪[K.Carrier]) :
    χ (principalUnit K hϖ hk (s + s')) =
      χ (principalUnit K hϖ hk s) * χ (principalUnit K hϖ hk s') := by
  have hm : ϖ ^ k * (s * s') ∈ 𝓂[K.Carrier] :=
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2
      hϖ.not_isUnit) k hk)
  rw [← map_mul, principalUnit_mul, quasicharacter_principalUnit_add K χ hϖ hk hχ _ _ hm]

/-- The homomorphism `s ↦ χ(1 + ϖ^k s)⁻¹` from `𝔬_K` to `ℂˣ`. -/
def quasicharacterAddHom {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
    (χ : HarmonicAnalysis.Quasicharacter K.Carrier) {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ)
    {k : ℕ} (hk : 1 ≤ k) (hχ : K.canonicalTopologicalData.MultiplicativeTrivialAt χ (k + 1)) :
    𝒪[K.Carrier] →+ Additive ℂˣ where
  toFun s := Additive.ofMul (χ (principalUnit K hϖ hk s))⁻¹
  map_zero' := by
    rw [principalUnit_zero, map_one, inv_one, ofMul_one]
  map_add' s s' := by
    rw [quasicharacter_principalUnit_add_eq_mul K χ hϖ hk hχ s s', mul_inv, ofMul_mul]

/-- **An additive character adapted to `χ`.** If `a(χ) = k + 1` with `k ≥ 1`, there is a
level-one additive character `ψ` of `K` with `ψ(s) = χ(1 + ϖ^k s)⁻¹` for all `s ∈ 𝔬_K`. -/
theorem exists_isLevelOne_adapted {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
    (χ : HarmonicAnalysis.Quasicharacter K.Carrier) {k : ℕ} (hk : 1 ≤ k)
    (hχ : K.canonicalTopologicalData.multiplicativeConductor χ = k + 1) {ϖ : 𝒪[K.Carrier]}
    (hϖ : Irreducible ϖ) :
    ∃ ψ : AddChar K.Carrier ℂ, IsLevelOne K ψ ∧ ∀ s : 𝒪[K.Carrier],
      ψ (s : K.Carrier) = (((χ (principalUnit K hϖ hk s))⁻¹ : ℂˣ) : ℂ) := by
  have htriv : K.canonicalTopologicalData.MultiplicativeTrivialAt χ (k + 1) :=
    (K.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le χ (k + 1)).2 hχ.le
  obtain ⟨ψ, hψ⟩ := exists_addChar_comp_eq (𝒪[K.Carrier]).subtype.toAddMonoidHom
    Subtype.val_injective (quasicharacterAddHom K χ hϖ hk htriv)
  have hψ' : ∀ s : 𝒪[K.Carrier],
      ψ (s : K.Carrier) = (((χ (principalUnit K hϖ hk s))⁻¹ : ℂˣ) : ℂ) := fun s => hψ s
  refine ⟨ψ, ⟨fun a ha => ?_, ?_⟩, hψ'⟩
  · have h := quasicharacter_principalUnit_add K χ hϖ hk htriv 0 a ha
    rw [zero_add] at h
    rw [hψ', h, principalUnit_zero, map_one, inv_one, Units.val_one]
  · obtain ⟨u, hu, hχu⟩ :=
      K.canonicalTopologicalData.exists_nontrivial_below_multiplicativeConductor χ k (by omega)
    have hu2 := ((K.canonicalTopologicalData.mem_principalUnits k u).1 hu).2
    have hint : (u : K.Carrier) - 1 ∈ 𝒪[K.Carrier] :=
      (K.canonicalTopologicalData.mem_integers_iff_discreteValuation_le_one _).2
        (hu2.trans (by
          rw [← WithZero.exp_zero, WithZero.exp_le_exp]
          omega))
    let r : 𝒪[K.Carrier] := ⟨(u : K.Carrier) - 1, hint⟩
    have hr : r ∈ 𝓂[K.Carrier] ^ k :=
      (K.canonicalTopologicalData.mem_maximalIdeal_pow_iff_discreteValuation_le k r).2 hu2
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton'] at hr
    obtain ⟨s, hs⟩ := hr
    refine ⟨s, ?_⟩
    have hsr : ϖ ^ k * s = r := by rw [mul_comm]; exact hs
    have hus : principalUnit K hϖ hk s = u := by
      apply Units.ext
      rw [principalUnit_val, hsr]
      show (1 : K.Carrier) + ((u : K.Carrier) - 1) = u
      ring
    rw [hψ', hus]
    intro h
    exact hχu (inv_eq_one.1 (Units.val_eq_one.1 h))

/-- **Case `x < k` of L2, from L1.** With `k = a(χ) - 1`, if the normalized level `x` of `a`
is below `k`, the normalized level of the twist of `a` by `χ ∘ det` is `k`. -/
theorem normalizedLevel_twist_eq_of_lt {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) (n : ℕ) (hn : 1 ≤ n)
    (χ : HarmonicAnalysis.Quasicharacter K.Carrier) (k : ℕ)
    (hk : k = K.canonicalTopologicalData.multiplicativeConductor χ - 1)
    (a : SmoothDualClass.{0, uK, uV} (k := ℂ) (G := GeneralLinear n K.Carrier)) (x y : ℚ)
    (hx : IsNormalizedLevel K n a x)
    (hy : IsNormalizedLevel K n
      (SmoothDualClass.twist (χ.toMonoidHom.comp (GeneralLinear.determinant (n := n)))
        (isOpen_ker_determinantCharacter K n χ) a) y)
    (hxk : x < (k : ℚ)) : y = (k : ℚ) := by
  have hle := (normalizedLevel_twist_le_and_eq_of_lt K n χ k hk a x y hx hy).1
  rw [max_eq_right hxk.le] at hle
  -- `x ≥ 0`, so `k ≥ 1` and `a(χ) = k + 1`.
  have hx0 : (0 : ℚ) ≤ x := by
    obtain ⟨𝓛, m, hxm, -⟩ := hx.1
    rw [hxm]
    positivity
  have hk1 : 1 ≤ k := by
    have h : (0 : ℚ) < k := lt_of_le_of_lt hx0 hxk
    exact_mod_cast h
  have hcond : K.canonicalTopologicalData.multiplicativeConductor χ = k + 1 := by omega
  have htriv : K.canonicalTopologicalData.MultiplicativeTrivialAt χ (k + 1) :=
    (K.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le χ (k + 1)).2 hcond.le
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K.Carrier]
  obtain ⟨ψ, hψ1, hψ⟩ := exists_isLevelOne_adapted K χ hk1 hcond hϖ
  by_contra hne
  have hlt : y < k := lt_of_le_of_ne hle hne
  -- A chain witnessing the level `y < k` of the twist.
  obtain ⟨𝓛, m, hym, hfix⟩ := hy.1
  have he0 : 0 < 𝓛.period := 𝓛.period_pos
  have hmk : m + 1 ≤ 𝓛.period * k := by
    rw [hym, div_lt_iff₀ (by exact_mod_cast he0)] at hlt
    have h2 : m < 𝓛.period * k := by
      rw [mul_comm]
      exact_mod_cast hlt
    exact h2
  have hfix' := hasFixedVector_of_le (unitSubgroup_antitone K 𝓛 hmk) hfix
  obtain ⟨A, rfl⟩ := Quotient.exists_rep a
  have hfv : fixedVectors (Langlands.twist (χ.toMonoidHom.comp
      (GeneralLinear.determinant (n := n))) A.obj.representation)
      (unitSubgroup K 𝓛 (𝓛.period * k)) ≠ ⊥ := hfix'
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hfv
  -- The scalar stratum `[𝔄(𝓛), e k, e k - 1, ϖ^{-k}]`.
  set b : Module.End K.Carrier (Fin n → K.Carrier) :=
    (((ϖ : K.Carrier)) ^ k)⁻¹ • (1 : Module.End K.Carrier (Fin n → K.Carrier)) with hb
  have hb_mem : b ∈ 𝓛.endFiltration (-((𝓛.period * k : ℕ) : ℤ)) := by
    apply 𝓛.inv_pow_smul_mem_endFiltration hϖ k
    rw [show -((𝓛.period * k : ℕ) : ℤ) + 𝓛.period * k = 0 by push_cast; ring]
    exact (𝓛.mem_order_iff_mem_endFiltration).1 (one_mem 𝓛.order)
  have hfund : ∀ z ∈ 𝓛.endFiltration (1 - ((𝓛.period * k : ℕ) : ℤ)),
      ¬ IsNilpotent (b + z) := by
    intro z hz
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    apply 𝓛.not_isNilpotent_inv_pow_smul_add k hϖ
    push_cast at hz
    exact hz
  have hcont : ContainsStratum K n ψ (Quotient.mk _ A) 𝓛 (𝓛.period * k) b := by
    refine ⟨Nat.mul_pos he0 (by omega), hb_mem, A, rfl, v, hv0, fun g hg => ?_⟩
    have hz : (Matrix.GeneralLinearGroup.toLin g : Module.End K.Carrier (Fin n → K.Carrier)) -
        1 ∈ 𝓛.endFiltration ((𝓛.period : ℤ) * k) := by
      have h := hg.2.2
      push_cast at h
      exact h
    obtain ⟨s, q, htr, hdet⟩ := 𝓛.exists_det_one_add_eq_trace k hϖ hz
    rw [add_sub_cancel, Matrix.GeneralLinearGroup.coe_toLin, ← Matrix.toLin'_apply',
      LinearMap.det_toLin'] at hdet
    have hdetu : GeneralLinear.determinant g = principalUnit K hϖ hk1 (s + ϖ ^ k * q) := by
      apply Units.ext
      rw [principalUnit_val]
      exact hdet
    have hq : ϖ ^ k * q ∈ 𝓂[K.Carrier] :=
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2
        hϖ.not_isUnit) k hk1)
    have hφg : (χ.toMonoidHom.comp (GeneralLinear.determinant (n := n))) g =
        χ (principalUnit K hϖ hk1 s) := by
      change χ (GeneralLinear.determinant g) = _
      rw [hdetu, quasicharacter_principalUnit_add K χ hϖ hk1 htriv s _ hq]
    have hgv := hv ⟨g, hg⟩
    change ((((χ.toMonoidHom.comp (GeneralLinear.determinant (n := n))) g : ℂˣ) : ℂ) •
      A.obj.representation g) v = v at hgv
    rw [LinearMap.smul_apply, hφg] at hgv
    have hbz : b * ((Matrix.GeneralLinearGroup.toLin g :
          Module.End K.Carrier (Fin n → K.Carrier)) - 1) =
        (((ϖ : K.Carrier)) ^ k)⁻¹ • ((Matrix.GeneralLinearGroup.toLin g :
          Module.End K.Carrier (Fin n → K.Carrier)) - 1) := by
      rw [hb, smul_mul_assoc, one_mul]
    rw [elementCharacter_apply, traceCharacter_apply, hbz, htr, hψ]
    conv_rhs => rw [← hgv]
    rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hlev := fundamentalStratumLevel p K n hn ψ hψ1 (Quotient.mk _ A) 𝓛
    (𝓛.period * k) b
    (Nat.mul_pos he0 (by omega)) hb_mem hfund hcont
  rw [Nat.cast_mul, mul_div_cancel_left₀ _ (by exact_mod_cast he0.ne')] at hlev
  exact absurd (hx.unique hlev) (ne_of_lt hxk)

/-- **L2** (operator route note, Lemma `lem:level`(ii)). -/
theorem normalizedLevelTwist : NormalizedLevelTwistStatement.{uK, uV} := by
  intro p _ K n hn χ k hk a x y hx hy
  have h := normalizedLevel_twist_le_and_eq_of_lt K n χ k hk a x y hx hy
  refine ⟨h.1, fun hne => ?_⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [max_eq_right hlt.le]
    exact normalizedLevel_twist_eq_of_lt K n hn χ k hk a x y hx hy hlt
  · rw [max_eq_left hgt.le]
    exact h.2 hgt

end Instances

end Langlands.BushnellKutzko
