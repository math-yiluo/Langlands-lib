import Langlands.Algebra.UnitaryInvolutionStatements
import Langlands.LinearAlgebra.UnitaryTwistedDescent
import Langlands.Algebra.MatrixAlgEquivInnerProof
import Langlands.LinearAlgebra.SpecialLinearConjugationScalars
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! # Twisted projective lifts of an algebra with unitary involution -/

noncomputable section

universe u v

open Matrix
open scoped TensorProduct

namespace Langlands.UnitaryDiscriminant

open LinearAlgebra.UnitaryTwistedDescent
open LinearAlgebra.SpecialLinearConjugation (exists_unit_scalar_of_conjugation_eq_conjugation)

section Center

variable (F L M : Type u) [Field F] [Field L] [Field M] [Algebra F M] [Algebra L M]

/-- The automorphisms of `M` over `F` that fix the image of `L` pointwise. -/
def centerFixing : Subgroup (M ≃ₐ[F] M) where
  carrier := {g | ∀ l : L, g (algebraMap L M l) = algebraMap L M l}
  mul_mem' {g h} hg hh l := by
    change g (h (algebraMap L M l)) = algebraMap L M l
    rw [hh l, hg l]
  one_mem' _ := rfl
  inv_mem' {g} hg l := by
    change g.symm (algebraMap L M l) = algebraMap L M l
    exact (AlgEquiv.symm_apply_eq g).2 (hg l).symm

variable {F L M}

theorem mem_centerFixing {g : M ≃ₐ[F] M} :
    g ∈ centerFixing F L M ↔ ∀ l : L, g (algebraMap L M l) = algebraMap L M l := Iff.rfl

variable [Algebra F L] [IsScalarTower F L M] [Algebra.IsQuadraticExtension F L]

/-- An `F`-algebra map from the quadratic extension `L` to `M` is the structure map or its
composite with the nontrivial automorphism `ι`. -/
theorem algHom_eq_or_eq (ι : L ≃ₐ[F] L) (hι : ι ≠ 1) (φ : L →ₐ[F] M) :
    φ = IsScalarTower.toAlgHom F L M ∨
      φ = (IsScalarTower.toAlgHom F L M).comp ι.toAlgHom := by
  have : FiniteDimensional F L := Module.finite_of_finrank_pos (by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two]; norm_num)
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2⟩ := hne
  set φ₁ := IsScalarTower.toAlgHom F L M with hφ₁
  set φ₂ := φ₁.comp ι.toAlgHom with hφ₂
  have h12 : φ₁ ≠ φ₂ := by
    intro h
    apply hι
    ext l
    have hl := congrArg (fun ψ : L →ₐ[F] M => ψ l) h
    simp only [hφ₂, hφ₁, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at hl
    exact ((algebraMap L M).injective hl).symm
  let f : Fin 3 → (L →ₐ[F] M) := ![φ₁, φ₂, φ]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, eq_comm]
  have hcard := Nat.card_le_card_of_injective f hf
  have hle := card_algHom_le_finrank F L M
  rw [Algebra.IsQuadraticExtension.finrank_eq_two] at hle
  have h3 : Nat.card (Fin 3) = 3 := by simp
  omega

variable {ι : L ≃ₐ[F] L}

omit [Algebra F M] [IsScalarTower F L M] [Algebra.IsQuadraticExtension F L] in
theorem false_of_algebraMap_eq (hι : ι ≠ 1)
    (h : ∀ l : L, algebraMap L M (ι l) = algebraMap L M l) : False := by
  apply hι
  ext l
  exact (algebraMap L M).injective (h l)

/-- The nontrivial automorphism of a quadratic extension is an involution. -/
theorem apply_apply_of_ne_one (hι : ι ≠ 1) (l : L) : ι (ι l) = l := by
  rcases algHom_eq_or_eq (M := L) ι hι
      ((IsScalarTower.toAlgHom F L L).comp (ι.toAlgHom.comp ι.toAlgHom)) with h | h
  · have hl := congrArg (fun ψ : L →ₐ[F] L => ψ l) h
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at hl
    exact (algebraMap L L).injective hl
  · exfalso
    apply false_of_algebraMap_eq (M := L) hι
    intro l'
    have hl := congrArg (fun ψ : L →ₐ[F] L => ψ (ι.symm l')) h
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply] at hl
    simpa using hl

/-- An automorphism of `M/F` not fixing `L` acts on `L` through `ι`. -/
theorem apply_algebraMap_of_not_mem (hι : ι ≠ 1) {g : M ≃ₐ[F] M}
    (hg : g ∉ centerFixing F L M) (l : L) :
    g (algebraMap L M l) = algebraMap L M (ι l) := by
  rcases algHom_eq_or_eq ι hι (g.toAlgHom.comp (IsScalarTower.toAlgHom F L M)) with h | h
  · exfalso
    apply hg
    intro l'
    have hl := congrArg (fun ψ : L →ₐ[F] M => ψ l') h
    simpa using hl
  · have hl := congrArg (fun ψ : L →ₐ[F] M => ψ l) h
    simpa using hl

/-- A product lies in the subgroup fixing `L` exactly when both or neither factor does. -/
theorem mul_mem_centerFixing_iff (hι : ι ≠ 1) (g h : M ≃ₐ[F] M) :
    g * h ∈ centerFixing F L M ↔ (g ∈ centerFixing F L M ↔ h ∈ centerFixing F L M) := by
  by_cases hg : g ∈ centerFixing F L M <;> by_cases hh : h ∈ centerFixing F L M
  · exact iff_of_true (mul_mem hg hh) (iff_of_true hg hh)
  · refine iff_of_false (fun hgh => ?_) (fun hiff => hh (hiff.1 hg))
    apply false_of_algebraMap_eq (M := M) hι
    intro l
    have := hgh l
    rw [AlgEquiv.mul_apply, apply_algebraMap_of_not_mem hι hh, hg] at this
    exact this
  · refine iff_of_false (fun hgh => ?_) (fun hiff => hg (hiff.2 hh))
    apply false_of_algebraMap_eq (M := M) hι
    intro l
    have := hgh l
    rw [AlgEquiv.mul_apply, hh, apply_algebraMap_of_not_mem hι hg] at this
    exact this
  · refine iff_of_true (fun l => ?_) (iff_of_false hg hh)
    rw [AlgEquiv.mul_apply, apply_algebraMap_of_not_mem hι hh,
      apply_algebraMap_of_not_mem hι hg, apply_apply_of_ne_one hι]

end Center

section Matrices

variable {R : Type*} [CommRing R] {I : Type*} [Fintype I] [DecidableEq I]

/-- The inverse transpose, as a group endomorphism of the invertible matrices. -/
def invTranspose : GL I R →* GL I R where
  toFun X := ⟨((X⁻¹ : GL I R) : Matrix I I R)ᵀ, (X : Matrix I I R)ᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  map_one' := by
    ext : 1
    simp
  map_mul' X Y := by
    ext : 1
    simp [_root_.mul_inv_rev, transpose_mul]

@[simp] theorem coe_invTranspose (X : GL I R) :
    ((invTranspose X : GL I R) : Matrix I I R) = ((X⁻¹ : GL I R) : Matrix I I R)ᵀ := rfl

@[simp] theorem coe_invTranspose_inv (X : GL I R) :
    (((invTranspose X)⁻¹ : GL I R) : Matrix I I R) = (X : Matrix I I R)ᵀ := rfl

theorem invTranspose_invTranspose (X : GL I R) : invTranspose (invTranspose X) = X := by
  ext : 1
  rw [coe_invTranspose, coe_invTranspose_inv, transpose_transpose]

theorem invTranspose_map {S : Type*} [CommRing S] (f : R →+* S) (X : GL I R) :
    invTranspose (GeneralLinearGroup.map f X) = GeneralLinearGroup.map f (invTranspose X) := by
  ext : 1
  rw [coe_invTranspose, ← map_inv]
  ext i j
  rfl

theorem det_invTranspose (X : GL I R) :
    GeneralLinearGroup.det (invTranspose X) = (GeneralLinearGroup.det X)⁻¹ := by
  ext
  simp

theorem invTranspose_scalar (c : Rˣ) :
    invTranspose (GeneralLinearGroup.scalar I c) = GeneralLinearGroup.scalar I c⁻¹ := by
  ext : 1
  simp [← map_inv]

/-- Every algebra endomorphism of a full matrix algebra over a field is conjugation by an
invertible matrix (matrix Skolem–Noether, with bijectivity from simplicity). -/
theorem exists_unit_conj_of_algHom {k : Type*} [Field k]
    (Φ : Matrix I I k →ₐ[k] Matrix I I k) :
    ∃ U : GL I k, ∀ N : Matrix I I k,
      Φ N = (U : Matrix I I k) * N * ((U⁻¹ : GL I k) : Matrix I I k) := by
  have hinj : Function.Injective Φ := by
    cases isEmpty_or_nonempty I with
    | inl hI => exact fun x y _ => Subsingleton.elim x y
    | inr hI => exact RingHom.injective Φ.toRingHom
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective (f := Φ.toLinearMap)).mp hinj
  exact MatrixAlgebra.exists_unit_conj_of_algEquiv (AlgEquiv.ofBijective Φ ⟨hinj, hsurj⟩)

end Matrices

section Twist

variable {F M : Type u} [Field F] [Field M] [Algebra F M]
  (H : Subgroup (M ≃ₐ[F] M)) {I : Type} [Fintype I] [DecidableEq I]

open Classical in
/-- Entrywise action of `g` on a matrix, followed by transposition when `g ∉ H`. -/
def coeffTwist (g : M ≃ₐ[F] M) (N : Matrix I I M) : Matrix I I M :=
  if g ∈ H then N.map g else (N.map g)ᵀ

open Classical in
/-- The action of `g` on invertible matrices matching `coeffTwist` under conjugation: the
entrywise image when `g ∈ H`, and its inverse transpose when `g ∉ H`. -/
def twistGL (g : M ≃ₐ[F] M) (X : GL I M) : GL I M :=
  if g ∈ H then GeneralLinearGroup.map (g : M →+* M) X
  else invTranspose (GeneralLinearGroup.map (g : M →+* M) X)

open Classical in
/-- The action of `g` on units matching `twistGL` on scalar matrices: `g` itself when `g ∈ H`,
and `g` followed by inversion when `g ∉ H`. -/
def twistUnit (g : M ≃ₐ[F] M) (a : Mˣ) : Mˣ :=
  if g ∈ H then g • a else (g • a)⁻¹

variable {H}

omit [Fintype I] [DecidableEq I] in
theorem coeffTwist_of_mem {g : M ≃ₐ[F] M} (hg : g ∈ H) (N : Matrix I I M) :
    coeffTwist H g N = N.map g := by
  simp [coeffTwist, hg]

omit [Fintype I] [DecidableEq I] in
theorem coeffTwist_of_not_mem {g : M ≃ₐ[F] M} (hg : g ∉ H) (N : Matrix I I M) :
    coeffTwist H g N = (N.map g)ᵀ := by
  simp [coeffTwist, hg]

theorem twistGL_of_mem {g : M ≃ₐ[F] M} (hg : g ∈ H) (X : GL I M) :
    twistGL H g X = GeneralLinearGroup.map (g : M →+* M) X := by
  simp [twistGL, hg]

theorem twistGL_of_not_mem {g : M ≃ₐ[F] M} (hg : g ∉ H) (X : GL I M) :
    twistGL H g X = invTranspose (GeneralLinearGroup.map (g : M →+* M) X) := by
  simp [twistGL, hg]

theorem twistUnit_of_mem {g : M ≃ₐ[F] M} (hg : g ∈ H) (a : Mˣ) : twistUnit H g a = g • a := by
  simp [twistUnit, hg]

theorem twistUnit_of_not_mem {g : M ≃ₐ[F] M} (hg : g ∉ H) (a : Mˣ) :
    twistUnit H g a = (g • a)⁻¹ := by
  simp [twistUnit, hg]

theorem coe_map_alg (g : M ≃ₐ[F] M) (X : GL I M) :
    ((GeneralLinearGroup.map (g : M →+* M) X : GL I M) : Matrix I I M) =
      (X : Matrix I I M).map g := rfl

theorem twistedAct_eq (x : (M ≃ₐ[F] M) → GL I M) (g : M ≃ₐ[F] M) (N : Matrix I I M) :
    twistedAct H x g N =
      (x g : Matrix I I M) * coeffTwist H g N * ((x g)⁻¹ : GL I M) := by
  by_cases hg : g ∈ H
  · rw [twistedAct_of_mem hg, coeffTwist_of_mem hg]
  · rw [twistedAct_of_not_mem hg, coeffTwist_of_not_mem hg]

theorem twistGL_mul (g : M ≃ₐ[F] M) (X Y : GL I M) :
    twistGL H g (X * Y) = twistGL H g X * twistGL H g Y := by
  by_cases hg : g ∈ H
  · simp only [twistGL_of_mem hg, map_mul]
  · simp only [twistGL_of_not_mem hg, map_mul]

theorem twistGL_inv (g : M ≃ₐ[F] M) (X : GL I M) :
    twistGL H g X⁻¹ = (twistGL H g X)⁻¹ := by
  by_cases hg : g ∈ H
  · simp only [twistGL_of_mem hg, map_inv]
  · simp only [twistGL_of_not_mem hg, map_inv]

theorem coeffTwist_conj (g : M ≃ₐ[F] M) (Y : GL I M) (A : Matrix I I M) :
    coeffTwist H g ((Y : Matrix I I M) * A * ((Y⁻¹ : GL I M) : Matrix I I M)) =
      (twistGL H g Y : Matrix I I M) * coeffTwist H g A *
        (((twistGL H g Y)⁻¹ : GL I M) : Matrix I I M) := by
  by_cases hg : g ∈ H
  · rw [coeffTwist_of_mem hg, coeffTwist_of_mem hg, twistGL_of_mem hg, ← map_inv,
      coe_map_alg, coe_map_alg]
    simp only [Matrix.map_mul]
  · rw [coeffTwist_of_not_mem hg, coeffTwist_of_not_mem hg, twistGL_of_not_mem hg,
      coe_invTranspose, coe_invTranspose_inv, ← map_inv, coe_map_alg, coe_map_alg]
    simp only [Matrix.map_mul, transpose_mul, Matrix.mul_assoc]

omit [Fintype I] [DecidableEq I] in
theorem coeffTwist_add (g : M ≃ₐ[F] M) (N N' : Matrix I I M) :
    coeffTwist H g (N + N') = coeffTwist H g N + coeffTwist H g N' := by
  by_cases hg : g ∈ H
  · simp only [coeffTwist_of_mem hg, Matrix.map_add _ (map_add g)]
  · simp only [coeffTwist_of_not_mem hg, Matrix.map_add _ (map_add g), transpose_add]

omit [Fintype I] [DecidableEq I] in
theorem coeffTwist_smul (g : M ≃ₐ[F] M) (c : M) (N : Matrix I I M) :
    coeffTwist H g (c • N) = g c • coeffTwist H g N := by
  have h : (c • N).map g = g c • N.map g := by
    ext i j
    simp
  by_cases hg : g ∈ H
  · simp only [coeffTwist_of_mem hg, h]
  · simp only [coeffTwist_of_not_mem hg, h, transpose_smul]

theorem twistedAct_smul (x : (M ≃ₐ[F] M) → GL I M) (g : M ≃ₐ[F] M) (c : M)
    (N : Matrix I I M) : twistedAct H x g (c • N) = g c • twistedAct H x g N := by
  rw [twistedAct_eq, twistedAct_eq, coeffTwist_smul, mul_smul_comm, smul_mul_assoc]

theorem twistedAct_zero (x : (M ≃ₐ[F] M) → GL I M) (g : M ≃ₐ[F] M) :
    twistedAct H x g 0 = 0 := by
  simpa using twistedAct_smul x g 0 0

variable (hmul : ∀ g h : M ≃ₐ[F] M, g * h ∈ H ↔ (g ∈ H ↔ h ∈ H))
include hmul

omit [Fintype I] [DecidableEq I] in
theorem coeffTwist_coeffTwist (g h : M ≃ₐ[F] M) (N : Matrix I I M) :
    coeffTwist H g (coeffTwist H h N) = coeffTwist H (g * h) N := by
  by_cases hg : g ∈ H <;> by_cases hh : h ∈ H
  · rw [coeffTwist_of_mem hg, coeffTwist_of_mem hh,
      coeffTwist_of_mem ((hmul g h).2 (iff_of_true hg hh)), map_map_mul]
  · rw [coeffTwist_of_mem hg, coeffTwist_of_not_mem hh,
      coeffTwist_of_not_mem (fun h' => hh (((hmul g h).1 h').1 hg)), transpose_map,
      map_map_mul]
  · rw [coeffTwist_of_not_mem hg, coeffTwist_of_mem hh,
      coeffTwist_of_not_mem (fun h' => hg (((hmul g h).1 h').2 hh)), map_map_mul]
  · rw [coeffTwist_of_not_mem hg, coeffTwist_of_not_mem hh,
      coeffTwist_of_mem ((hmul g h).2 (iff_of_false hg hh)), ← transpose_map,
      transpose_transpose, map_map_mul]

theorem twistGL_twistGL (g h : M ≃ₐ[F] M) (X : GL I M) :
    twistGL H g (twistGL H h X) = twistGL H (g * h) X := by
  have hcomp : GeneralLinearGroup.map (g : M →+* M)
      (GeneralLinearGroup.map (h : M →+* M) X) =
      GeneralLinearGroup.map ((g * h : M ≃ₐ[F] M) : M →+* M) X := by
    ext : 1
    rw [coe_map_alg, coe_map_alg, coe_map_alg, map_map_mul]
  by_cases hg : g ∈ H <;> by_cases hh : h ∈ H
  · rw [twistGL_of_mem hg, twistGL_of_mem hh,
      twistGL_of_mem ((hmul g h).2 (iff_of_true hg hh)), hcomp]
  · rw [twistGL_of_mem hg, twistGL_of_not_mem hh,
      twistGL_of_not_mem (fun h' => hh (((hmul g h).1 h').1 hg)), ← invTranspose_map, hcomp]
  · rw [twistGL_of_not_mem hg, twistGL_of_mem hh,
      twistGL_of_not_mem (fun h' => hg (((hmul g h).1 h').2 hh)), hcomp]
  · rw [twistGL_of_not_mem hg, twistGL_of_not_mem hh,
      twistGL_of_mem ((hmul g h).2 (iff_of_false hg hh)), ← invTranspose_map,
      invTranspose_invTranspose, hcomp]

omit hmul in
theorem twistGL_scalar (g : M ≃ₐ[F] M) (a : Mˣ) :
    twistGL H g (GeneralLinearGroup.scalar I a) =
      GeneralLinearGroup.scalar I (twistUnit H g a) := by
  have h : GeneralLinearGroup.map (g : M →+* M) (GeneralLinearGroup.scalar I a) =
      GeneralLinearGroup.scalar I (g • a) := by
    rw [GeneralLinearGroup.map_scalar]
    rfl
  by_cases hg : g ∈ H
  · rw [twistGL_of_mem hg, twistUnit_of_mem hg, h]
  · rw [twistGL_of_not_mem hg, twistUnit_of_not_mem hg, h, invTranspose_scalar]

omit hmul in
theorem det_twistGL (g : M ≃ₐ[F] M) (X : GL I M) :
    GeneralLinearGroup.det (twistGL H g X) = twistUnit H g (GeneralLinearGroup.det X) := by
  have h : GeneralLinearGroup.det (GeneralLinearGroup.map (g : M →+* M) X) =
      g • GeneralLinearGroup.det X := by
    rw [GeneralLinearGroup.map_det]
    rfl
  by_cases hg : g ∈ H
  · rw [twistGL_of_mem hg, twistUnit_of_mem hg, h]
  · rw [twistGL_of_not_mem hg, twistUnit_of_not_mem hg, det_invTranspose, h]

omit hmul [Fintype I] [DecidableEq I] in
theorem coeffTwist_surjective (g : M ≃ₐ[F] M) :
    Function.Surjective (coeffTwist (I := I) H g) := by
  intro Z
  by_cases hg : g ∈ H
  · refine ⟨Z.map g.symm, ?_⟩
    rw [coeffTwist_of_mem hg]
    ext i j
    simp
  · refine ⟨Zᵀ.map g.symm, ?_⟩
    rw [coeffTwist_of_not_mem hg]
    ext i j
    simp

/-- If the twisted actions of a family of invertible matrices compose, then the family is a
twisted projective cocycle: `x g · twistGL g (x h)` is a unit multiple of `x (g h)`. -/
theorem exists_twistGL_mul_eq (x : (M ≃ₐ[F] M) → GL I M)
    (hact : ∀ (g h : M ≃ₐ[F] M) (N : Matrix I I M),
      twistedAct H x (g * h) N = twistedAct H x g (twistedAct H x h N))
    (g h : M ≃ₐ[F] M) :
    ∃ c : Mˣ, x g * twistGL H g (x h) = GeneralLinearGroup.scalar I c * x (g * h) := by
  obtain ⟨c, hc⟩ :=
    exists_unit_scalar_of_conjugation_eq_conjugation
      (x g * twistGL H g (x h)) (x (g * h)) (fun s => by
        apply Units.ext
        obtain ⟨N, hN⟩ := coeffTwist_surjective (H := H) (g * h) (s : Matrix I I M)
        have he := hact g h N
        rw [twistedAct_eq, twistedAct_eq, twistedAct_eq, coeffTwist_conj,
          coeffTwist_coeffTwist hmul, hN] at he
        simp only [Units.val_mul, _root_.mul_inv_rev, Matrix.mul_assoc,
          SpecialLinearGroup.coe_GL_coe_matrix] at he ⊢
        exact he.symm)
  exact ⟨c, hc.trans (GeneralLinearGroup.scalar_commute c (x (g * h))).symm⟩

omit hmul in
/-- Two families with the same twisted action of `g` differ at `g` by a unit scalar. -/
theorem exists_scalar_of_twistedAct_eq (x y : (M ≃ₐ[F] M) → GL I M) (g : M ≃ₐ[F] M)
    (h : ∀ N : Matrix I I M, twistedAct H x g N = twistedAct H y g N) :
    ∃ b : Mˣ, x g = GeneralLinearGroup.scalar I b * y g := by
  obtain ⟨b, hb⟩ :=
    exists_unit_scalar_of_conjugation_eq_conjugation
      (x g) (y g) (fun s => by
        apply Units.ext
        obtain ⟨N, hN⟩ := coeffTwist_surjective (H := H) g (s : Matrix I I M)
        have he := h N
        rw [twistedAct_eq, twistedAct_eq, hN] at he
        simpa only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix] using he)
  exact ⟨b, hb.trans (GeneralLinearGroup.scalar_commute b (y g)).symm⟩

omit hmul in
/-- The scalar factors of a twisted projective cocycle satisfy the twisted two-cocycle
identity, for the action `twistUnit` of the Galois group on units. -/
theorem twisted_cocycle [Nonempty I] (x : (M ≃ₐ[F] M) → GL I M)
    (c : (M ≃ₐ[F] M) → (M ≃ₐ[F] M) → Mˣ)
    (hc : ∀ g h, x g * twistGL H g (x h) = GeneralLinearGroup.scalar I (c g h) * x (g * h))
    (htw : ∀ (g h : M ≃ₐ[F] M) (X : GL I M), twistGL H g (twistGL H h X) = twistGL H (g * h) X)
    (g h k : M ≃ₐ[F] M) :
    c g h * c (g * h) k = twistUnit H g (c h k) * c g (h * k) := by
  have hinj : Function.Injective (GeneralLinearGroup.scalar I : Mˣ →* GL I M) := by
    intro a b hab
    apply Units.ext
    let p : I := Classical.choice inferInstance
    have he := congrArg (fun X : GL I M => (X : Matrix I I M) p p) hab
    simpa only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      using he
  have hcentral (a : Mˣ) (X : GL I M) :
      GeneralLinearGroup.scalar I a * X = X * GeneralLinearGroup.scalar I a :=
    GeneralLinearGroup.scalar_commute a X
  apply hinj
  apply mul_right_cancel (b := x (g * (h * k)))
  simp only [map_mul]
  calc
    GeneralLinearGroup.scalar I (c g h) * GeneralLinearGroup.scalar I (c (g * h) k) *
        x (g * (h * k)) =
        GeneralLinearGroup.scalar I (c g h) * (x (g * h) * twistGL H (g * h) (x k)) := by
      rw [← mul_assoc g h k, mul_assoc, ← hc (g * h) k]
    _ = (x g * twistGL H g (x h)) * twistGL H (g * h) (x k) := by
      rw [← mul_assoc, ← hc g h]
    _ = x g * twistGL H g (x h * twistGL H h (x k)) := by
      rw [twistGL_mul, htw, mul_assoc]
    _ = x g * twistGL H g (GeneralLinearGroup.scalar I (c h k) * x (h * k)) := by
      rw [hc h k]
    _ = GeneralLinearGroup.scalar I (twistUnit H g (c h k)) * (x g * twistGL H g (x (h * k))) := by
      rw [twistGL_mul, twistGL_scalar, ← mul_assoc, ← mul_assoc, hcentral]
    _ = GeneralLinearGroup.scalar I (twistUnit H g (c h k)) *
        GeneralLinearGroup.scalar I (c g (h * k)) * x (g * (h * k)) := by
      rw [hc g (h * k), mul_assoc]

end Twist

section Chart

variable {F L M : Type u} [Field F] [Field L] [Field M] [Algebra F M] [Algebra L M]
  {B : Type v} [Ring B] [Algebra L B] {n : ℕ}

/-- The `L`-algebra map `b ↦ e (1 ⊗ b)` of a matrix splitting chart `e` of `B`. -/
def chartMap (e : M ⊗[L] B ≃ₐ[M] Matrix (Fin n) (Fin n) M) :
    B →ₐ[L] Matrix (Fin n) (Fin n) M :=
  (e.toAlgHom.restrictScalars L).comp Algebra.TensorProduct.includeRight

theorem chartMap_apply (e : M ⊗[L] B ≃ₐ[M] Matrix (Fin n) (Fin n) M) (b : B) :
    chartMap e b = e (1 ⊗ₜ b) := rfl

/-- The `M`-multiples of the chart images span the matrix algebra additively. -/
theorem chart_induction (e : M ⊗[L] B ≃ₐ[M] Matrix (Fin n) (Fin n) M)
    {P : Matrix (Fin n) (Fin n) M → Prop}
    (hadd : ∀ x y, P x → P y → P (x + y)) (hgen : ∀ (c : M) (b : B), P (c • chartMap e b))
    (N : Matrix (Fin n) (Fin n) M) : P N := by
  obtain ⟨x, rfl⟩ := e.surjective N
  induction x using TensorProduct.inductionOn with
  | tmul c b =>
    have hx : c ⊗ₜ[L] b = c • ((1 : M) ⊗ₜ[L] b) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hx, map_smul]
    exact hgen c b
  | add x y hx hy =>
    rw [map_add]
    exact hadd _ _ hx hy

/-- Every `L`-algebra map `B → M_n(M)` is conjugate to the chart map (Skolem–Noether through
the chart). -/
theorem exists_conj_chartMap (e : M ⊗[L] B ≃ₐ[M] Matrix (Fin n) (Fin n) M)
    (ψ : B →ₐ[L] Matrix (Fin n) (Fin n) M) :
    ∃ U : GL (Fin n) M, ∀ b : B, ψ b =
      (U : Matrix (Fin n) (Fin n) M) * chartMap e b *
        ((U⁻¹ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) := by
  let Ψ : M ⊗[L] B →ₐ[M] Matrix (Fin n) (Fin n) M :=
    Algebra.TensorProduct.lift (Algebra.ofId M _) ψ
      (fun x y => Algebra.commute_algebraMap_left x (ψ y))
  obtain ⟨U, hU⟩ := exists_unit_conj_of_algHom (Ψ.comp e.symm.toAlgHom)
  refine ⟨U, fun b => ?_⟩
  have h := hU (chartMap e b)
  rw [chartMap_apply] at h ⊢
  change Ψ (e.symm (e (1 ⊗ₜ b))) = _ at h
  have hΨ : Ψ (1 ⊗ₜ b) = ψ b := by
    simp only [Ψ]
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
  rw [AlgEquiv.symm_apply_apply, hΨ] at h
  exact h

/-- For `g` fixing `L`, the chart map followed by entrywise `g⁻¹`, as an `L`-algebra map. -/
def innerTarget (e : M ⊗[L] B ≃ₐ[M] Matrix (Fin n) (Fin n) M) (g : M ≃ₐ[F] M)
    (hg : g ∈ centerFixing F L M) : B →ₐ[L] Matrix (Fin n) (Fin n) M where
  toRingHom := ((g.symm : M →+* M).mapMatrix).comp (chartMap e).toRingHom
  commutes' l := by
    change ((chartMap e) (algebraMap L B l)).map g.symm = algebraMap L _ l
    rw [AlgHom.commutes]
    ext i j
    simp only [Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    split_ifs
    · exact (centerFixing F L M).inv_mem hg l
    · exact map_zero _

theorem innerTarget_apply (e : M ⊗[L] B ≃ₐ[M] Matrix (Fin n) (Fin n) M) (g : M ≃ₐ[F] M)
    (hg : g ∈ centerFixing F L M) (b : B) :
    innerTarget e g hg b = (chartMap e b).map g.symm := rfl

/-- For `g` acting on `L` through `ι`, the map `b ↦ g⁻¹(e(1 ⊗ τ b)ᵀ)`, an `L`-algebra map
because `τ` reverses products and acts on `L` through `ι`. -/
def outerTarget [Algebra F L] (e : M ⊗[L] B ≃ₐ[M] Matrix (Fin n) (Fin n) M)
    {ι : L ≃ₐ[F] L} {τ : B → B} (hτ : IsUnitaryInvolution ι τ) (g : M ≃ₐ[F] M)
    (hg : ∀ l : L, g (algebraMap L M l) = algebraMap L M (ι l)) :
    B →ₐ[L] Matrix (Fin n) (Fin n) M where
  toFun b := (g.symm : M →+* M).mapMatrix (chartMap e (τ b))ᵀ
  map_one' := by
    have h1 : τ 1 = 1 := by simpa using hτ.2.2.2 1
    rw [h1, map_one, transpose_one, map_one]
  map_mul' x y := by
    rw [hτ.2.1, map_mul, transpose_mul, map_mul]
  map_zero' := by
    have h0 : τ 0 = 0 := by simpa using hτ.2.2.2 0
    rw [h0, map_zero, transpose_zero, map_zero]
  map_add' x y := by
    rw [hτ.1, map_add, transpose_add, map_add]
  commutes' l := by
    change ((chartMap e (τ (algebraMap L B l)))ᵀ).map g.symm = algebraMap L _ l
    rw [hτ.2.2.2, AlgHom.commutes]
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.algebraMap_matrix_apply]
    split_ifs with hij hji hji
    · exact (AlgEquiv.symm_apply_eq g).2 (hg l).symm
    · exact absurd hij.symm hji
    · exact absurd hji.symm hij
    · exact map_zero _

theorem outerTarget_apply [Algebra F L] (e : M ⊗[L] B ≃ₐ[M] Matrix (Fin n) (Fin n) M)
    {ι : L ≃ₐ[F] L}
    {τ : B → B} (hτ : IsUnitaryInvolution ι τ) (g : M ≃ₐ[F] M)
    (hg : ∀ l : L, g (algebraMap L M l) = algebraMap L M (ι l)) (b : B) :
    outerTarget e hτ g hg b = ((chartMap e (τ b))ᵀ).map g.symm := rfl

theorem map_symm_map (g : M ≃ₐ[F] M) (N : Matrix (Fin n) (Fin n) M) :
    (N.map g.symm).map g = N := by
  ext i j
  simp

/-- An automorphism fixing `L` has a lift `P` with `P g(e(1 ⊗ b)) P⁻¹ = e(1 ⊗ b)`. -/
theorem exists_lift_of_mem (e : M ⊗[L] B ≃ₐ[M] Matrix (Fin n) (Fin n) M) {g : M ≃ₐ[F] M}
    (hg : g ∈ centerFixing F L M) :
    ∃ P : GL (Fin n) M, ∀ b : B,
      (P : Matrix (Fin n) (Fin n) M) * (chartMap e b).map g *
        ((P⁻¹ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) = chartMap e b := by
  obtain ⟨U, hU⟩ := exists_conj_chartMap e (innerTarget e g hg)
  refine ⟨GeneralLinearGroup.map (g : M →+* M) U, fun b => ?_⟩
  have h := congrArg (fun N : Matrix (Fin n) (Fin n) M => N.map g) (hU b)
  simp only [innerTarget_apply, map_symm_map, Matrix.map_mul] at h
  rw [← map_inv, coe_map_alg, coe_map_alg]
  exact h.symm

/-- An automorphism acting on `L` through `ι` has a lift `P` with
`P g(e(1 ⊗ b))ᵀ P⁻¹ = e(1 ⊗ τ b)`. -/
theorem exists_lift_of_not_mem [Algebra F L] (e : M ⊗[L] B ≃ₐ[M] Matrix (Fin n) (Fin n) M)
    {ι : L ≃ₐ[F] L} {τ : B → B} (hτ : IsUnitaryInvolution ι τ) {g : M ≃ₐ[F] M}
    (hg : ∀ l : L, g (algebraMap L M l) = algebraMap L M (ι l)) :
    ∃ P : GL (Fin n) M, ∀ b : B,
      (P : Matrix (Fin n) (Fin n) M) * ((chartMap e b).map g)ᵀ *
        ((P⁻¹ : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) = chartMap e (τ b) := by
  obtain ⟨U, hU⟩ := exists_conj_chartMap e (outerTarget e hτ g hg)
  refine ⟨invTranspose (GeneralLinearGroup.map (g : M →+* M) U), fun b => ?_⟩
  have h := congrArg (fun N : Matrix (Fin n) (Fin n) M => (N.map g)ᵀ) (hU b)
  simp only [outerTarget_apply, map_symm_map, transpose_transpose, Matrix.map_mul,
    transpose_mul] at h
  rw [coe_invTranspose, coe_invTranspose_inv, ← map_inv, coe_map_alg, coe_map_alg,
    Matrix.mul_assoc]
  exact h.symm

/-- Two families of invertible matrices whose twisted actions of `g` agree on the chart
images have the same twisted action of `g` on all matrices. -/
theorem twistedAct_eq_of_chartMap (e : M ⊗[L] B ≃ₐ[M] Matrix (Fin n) (Fin n) M)
    {H : Subgroup (M ≃ₐ[F] M)} (x y : (M ≃ₐ[F] M) → GL (Fin n) M) (g : M ≃ₐ[F] M)
    (h : ∀ b : B, twistedAct H x g (chartMap e b) = twistedAct H y g (chartMap e b))
    (N : Matrix (Fin n) (Fin n) M) : twistedAct H x g N = twistedAct H y g N := by
  refine chart_induction e (P := fun N => twistedAct H x g N = twistedAct H y g N)
    (fun N N' hN hN' => ?_) (fun c b => ?_) N
  · rw [twistedAct_add, twistedAct_add, hN, hN']
  · rw [twistedAct_smul, twistedAct_smul, h b]

end Chart

section ChosenLifts

variable {F L M : Type u} [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]
  [Algebra L M] [IsScalarTower F L M] [Algebra.IsQuadraticExtension F L]
  {B : Type v} [Ring B] [Algebra L B] {n : ℕ}
  {ι : L ≃ₐ[F] L} (hι : ι ≠ 1) {τ : B → B} (hτ : IsUnitaryInvolution ι τ)
  (e : M ⊗[L] B ≃ₐ[M] Matrix (Fin n) (Fin n) M)

open Classical in
/-- The chosen lift of `g ∈ Gal(M/F)` through the chart `e`: an invertible matrix `P` with
`P g(e(1 ⊗ b)) P⁻¹ = e(1 ⊗ b)` if `g` fixes `L`, and `P g(e(1 ⊗ b))ᵀ P⁻¹ = e(1 ⊗ τ b)`
otherwise. -/
def chartLift (g : M ≃ₐ[F] M) : GL (Fin n) M :=
  if hg : g ∈ centerFixing F L M then (exists_lift_of_mem e hg).choose
  else (exists_lift_of_not_mem e hτ (apply_algebraMap_of_not_mem hι hg)).choose

theorem twistedAct_chartLift_of_mem {g : M ≃ₐ[F] M} (hg : g ∈ centerFixing F L M) (b : B) :
    twistedAct (centerFixing F L M) (chartLift hι hτ e) g (chartMap e b) = chartMap e b := by
  rw [twistedAct_of_mem hg]
  have hP : chartLift hι hτ e g = (exists_lift_of_mem e hg).choose := by
    simp [chartLift, hg]
  rw [hP]
  exact (exists_lift_of_mem e hg).choose_spec b

theorem twistedAct_chartLift_of_not_mem {g : M ≃ₐ[F] M} (hg : g ∉ centerFixing F L M)
    (b : B) :
    twistedAct (centerFixing F L M) (chartLift hι hτ e) g (chartMap e b) =
      chartMap e (τ b) := by
  rw [twistedAct_of_not_mem hg]
  have hP : chartLift hι hτ e g =
      (exists_lift_of_not_mem e hτ (apply_algebraMap_of_not_mem hι hg)).choose := by
    simp [chartLift, hg]
  rw [hP]
  exact (exists_lift_of_not_mem e hτ (apply_algebraMap_of_not_mem hι hg)).choose_spec b

/-- The twisted actions of the chosen lifts compose: they form an action of `Gal(M/F)`. -/
theorem twistedAct_chartLift_mul (g h : M ≃ₐ[F] M) (N : Matrix (Fin n) (Fin n) M) :
    twistedAct (centerFixing F L M) (chartLift hι hτ e) (g * h) N =
      twistedAct (centerFixing F L M) (chartLift hι hτ e) g
        (twistedAct (centerFixing F L M) (chartLift hι hτ e) h N) := by
  refine chart_induction e (P := fun N =>
    twistedAct (centerFixing F L M) (chartLift hι hτ e) (g * h) N =
      twistedAct (centerFixing F L M) (chartLift hι hτ e) g
        (twistedAct (centerFixing F L M) (chartLift hι hτ e) h N))
    (fun x y hx hy => ?_) (fun c b => ?_) N
  · rw [twistedAct_add, hx, hy, twistedAct_add, twistedAct_add]
  · rw [twistedAct_smul, twistedAct_smul, twistedAct_smul, AlgEquiv.mul_apply]
    congr 1
    have hmul := mul_mem_centerFixing_iff (M := M) hι g h
    by_cases hg : g ∈ centerFixing F L M <;> by_cases hh : h ∈ centerFixing F L M
    · rw [twistedAct_chartLift_of_mem hι hτ e (hmul.2 (iff_of_true hg hh)),
        twistedAct_chartLift_of_mem hι hτ e hh, twistedAct_chartLift_of_mem hι hτ e hg]
    · rw [twistedAct_chartLift_of_not_mem hι hτ e (fun h' => hh ((hmul.1 h').1 hg)),
        twistedAct_chartLift_of_not_mem hι hτ e hh, twistedAct_chartLift_of_mem hι hτ e hg]
    · rw [twistedAct_chartLift_of_not_mem hι hτ e (fun h' => hg ((hmul.1 h').2 hh)),
        twistedAct_chartLift_of_mem hι hτ e hh, twistedAct_chartLift_of_not_mem hι hτ e hg]
    · rw [twistedAct_chartLift_of_mem hι hτ e (hmul.2 (iff_of_false hg hh)),
        twistedAct_chartLift_of_not_mem hι hτ e hh, twistedAct_chartLift_of_not_mem hι hτ e hg,
        hτ.2.2.1]

theorem exists_chartLift_mul (g h : M ≃ₐ[F] M) :
    ∃ c : Mˣ, chartLift hι hτ e g * twistGL (centerFixing F L M) g (chartLift hι hτ e h) =
      GeneralLinearGroup.scalar (Fin n) c * chartLift hι hτ e (g * h) :=
  exists_twistGL_mul_eq (mul_mem_centerFixing_iff hι) _ (twistedAct_chartLift_mul hι hτ e) g h

/-- The scalar factor set of the chosen lifts. -/
def chartFactor (g h : M ≃ₐ[F] M) : Mˣ :=
  (exists_chartLift_mul hι hτ e g h).choose

/-- The twisted projective cocycle law of the chosen lifts, in Serre's factor-set convention:
`P g · g⋆(P h) = λ(g, h) · P (g h)`. -/
theorem chartLift_mul (g h : M ≃ₐ[F] M) :
    chartLift hι hτ e g * twistGL (centerFixing F L M) g (chartLift hι hτ e h) =
      GeneralLinearGroup.scalar (Fin n) (chartFactor hι hτ e g h) *
        chartLift hι hτ e (g * h) :=
  (exists_chartLift_mul hι hτ e g h).choose_spec

end ChosenLifts

end Langlands.UnitaryDiscriminant
