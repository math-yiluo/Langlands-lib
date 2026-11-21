import Langlands.Automorphic.AutomorphicAdmissibilityStatement
import Langlands.Automorphic.CuspidalL2.Representation
import Langlands.Global.AdelicGLIwasawa
import Langlands.Global.GeneralLinearBlockUnipotentQuotient
import Langlands.Group.GL.RankMaps
import Mathlib.MeasureTheory.Group.Integral

/-! # Detecting cuspidality by constant terms restricted to standard Levis -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.GeneralLinear

variable {R : Type u} [CommRing R] {a b n : ℕ}

/-- The block diagonal map for a specified decomposition of the total rank. -/
def blockDiagonalEmbedding (h : a + b = n) :
    GeneralLinear a R × GeneralLinear b R →* GeneralLinear n R :=
  (reindex (finCongr h)).toMonoidHom.comp blockSum

/-- A triangular matrix factors into the block radical and the block diagonal group. -/
theorem exists_blockUnipotent_mul_blockDiagonalEmbedding (h : a + b = n)
    (g : GeneralLinear n R) (hg : g ∈ upperTriangularSubgroup n R) :
    ∃ X : Matrix (Fin a) (Fin b) R, ∃ z : GeneralLinear a R × GeneralLinear b R,
      g = blockUnipotent h X * blockDiagonalEmbedding h z := by
  classical
  let e := reindex (R := R) (finSumFinEquiv.trans (finCongr h))
  let M := (e.symm g).val
  have hz : M.toBlocks₂₁ = 0 := by
    ext i j
    change g ((finSumFinEquiv.trans (finCongr h)) (.inr i))
      ((finSumFinEquiv.trans (finCongr h)) (.inl j)) = 0
    apply (mem_upperTriangularSubgroup_iff g).mp hg
    simp only [Fin.lt_def, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_natAdd, Fin.val_castAdd]
    omega
  have hd := (Matrix.GeneralLinearGroup.det (e.symm g)).isUnit
  change IsUnit M.det at hd
  nth_rw 1 [← Matrix.fromBlocks_toBlocks M] at hd
  rw [hz, Matrix.det_fromBlocks_zero₂₁] at hd
  let A := Matrix.GeneralLinearGroup.mk'' M.toBlocks₁₁ (isUnit_of_mul_isUnit_left hd)
  let D := Matrix.GeneralLinearGroup.mk'' M.toBlocks₂₂ (isUnit_of_mul_isUnit_right hd)
  let X := M.toBlocks₁₂ * D⁻¹.val
  refine ⟨X, (A, D), ?_⟩
  have hD : X * D.val = M.toBlocks₁₂ := by
    dsimp only [X]
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  apply e.symm.injective
  rw [map_mul, show blockUnipotent h X = e (sumBlockUnipotent X) from rfl,
    MulEquiv.symm_apply_apply]
  apply Units.ext
  have hdiag : (e.symm (blockDiagonalEmbedding h (A, D))).val =
      Matrix.fromBlocks A.val 0 0 D.val := by
    ext i j
    change blockSum (A, D)
      ((finCongr h).symm ((finCongr h) (finSumFinEquiv i)))
      ((finCongr h).symm ((finCongr h) (finSumFinEquiv j))) = _
    simp only [Equiv.symm_apply_apply]
    cases i <;> cases j <;> simp
  rw [Units.val_mul, hdiag]
  change M = Matrix.fromBlocks 1 X 0 1 * Matrix.fromBlocks A.val 0 0 D.val
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hD]
  change M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂
  rw [← hz, Matrix.fromBlocks_toBlocks]

end Langlands.GeneralLinear

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear MeasureTheory ContinuousRationalFunctions
open Langlands.Global.PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local instance finiteLevelRestrictionRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance finiteLevelRestrictionContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance finiteLevelRestrictionSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance finiteLevelRestrictionFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _

variable [CompactSpace (AdeleQuotient F)]

/-- Left translation by the block unipotent group preserves its normalized constant term. -/
theorem constantTerm_blockUnipotent_mul {a b : ℕ} (h : a + b = n)
    (f : ContinuousRationalFunctions F n) (X : Matrix (Fin a) (Fin b) (Adeles F))
    (g : AdelicGL F n) :
    constantTerm F n h f (blockUnipotent h X * g) = constantTerm F n h f g := by
  let : MeasurableSpace (Matrix (Fin a) (Fin b) (AdeleQuotient F)) := borel _
  have : BorelSpace (Matrix (Fin a) (Fin b) (AdeleQuotient F)) := ⟨rfl⟩
  have := matrixQuotientHaar_isAddHaarMeasure F a b
  have htranslate (q : Matrix (Fin a) (Fin b) (AdeleQuotient F)) :
      constantTermIntegrand F n h f (blockUnipotent h X * g) q =
        constantTermIntegrand F n h f g (q + matrixQuotientMap X) := by
    rw [← matrixQuotientMap_matrixLift q,
      ← GeneralLinearBlockUnipotent.matrixQuotientMap_add,
      constantTermIntegrand_mk, constantTermIntegrand_mk, blockUnipotent_add, mul_assoc]
  simp only [constantTerm, htranslate]
  exact integral_add_right_eq_self _ _

private theorem constantTerm_automorphicFiniteRightAction {a b : ℕ} (h : a + b = n)
    (f : AutomorphicForms F n) (d : FiniteAdelicGL F n) (g : AdelicGL F n) :
    constantTerm F n h (automorphicToContinuous F n (automorphicFiniteRightAction F n d f)) g =
    constantTerm F n h (automorphicToContinuous F n f) (g * AdelicGL.ofFinite F n d) := by
  simp only [constantTerm, constantTermIntegrand, evaluate_automorphicFiniteRightAction, mul_assoc]

private theorem constantTerm_automorphicCompactRightAction {a b : ℕ} (h : a + b = n)
    (f : AutomorphicForms F n) (k : standardInfiniteCompact F n) (g : AdelicGL F n) :
    constantTerm F n h (automorphicToContinuous F n (automorphicCompactRightAction F n k f)) g =
    constantTerm F n h (automorphicToContinuous F n f) (g * AdelicGL.ofInfinite F n k.val) := by
  simp only [constantTerm, constantTermIntegrand, evaluate_automorphicCompactRightAction,
    mul_assoc]

/-- Block constant term on the embedded Levi followed by one fixed finite translation. -/
def blockConstantTermAt {a b : ℕ} (h : a + b = n) (d : FiniteAdelicGL F n) :
    AutomorphicForms F n →ₗ[ℂ] (AdelicGL F a × AdelicGL F b → ℂ) where
  toFun f z := constantTerm F n h (automorphicToContinuous F n f)
    (blockDiagonalEmbedding h z * AdelicGL.ofFinite F n d)
  map_add' f g := by
    funext z
    change constantTerm F n h (automorphicToContinuous F n (f + g)) _ = _
    rw [map_add, constantTerm_add]
    rfl
  map_smul' c f := by
    funext z
    change constantTerm F n h (automorphicToContinuous F n (c • f)) _ = _
    rw [map_smul, constantTerm_smul]
    rfl

/-- Positive ordered block sizes summing to the total rank. -/
abbrev MaximalBlockCut :=
  {p : ℕ × ℕ // p.1 + p.2 = n ∧ 0 < p.1 ∧ 0 < p.2}

instance : Finite (MaximalBlockCut n) := by
  let first (p : MaximalBlockCut n) : Fin n :=
    ⟨p.val.1, by have := p.property.1; have := p.property.2.2; omega⟩
  apply Finite.of_injective first
  intro p q h
  have hfirst := congrArg Fin.val h
  change p.val.1 = q.val.1 at hfirst
  have hp := p.property.1
  have hq := q.property.1
  exact Subtype.ext (Prod.ext hfirst (by omega))

variable {m : ℕ} (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ))
variable (J : Ideal (ArchimedeanGL.EnvelopingCenter F n)) (L : OpenSubgroup (FiniteAdelicGL F n))

/-- The joint restriction to the maximal Levis and the indicated finite translations. -/
def restrictMultiplicityToConstantTerms (t : Finset (FiniteAdelicGL F n)) :
    annihilatedFormMultiplicitySpace F n J L.toSubgroup σ →ₗ[ℂ]
      (∀ (p : MaximalBlockCut n) (_ : ↥t),
        (Fin m → ℂ) →ₗ[ℂ] (AdelicGL F p.val.1 × AdelicGL F p.val.2 → ℂ)) :=
  LinearMap.pi fun p => LinearMap.pi fun d =>
    (LinearMap.llcomp ℂ (Fin m → ℂ) _ _ (blockConstantTermAt F n p.property.1 d.val)).comp
      (annihilatedFormMultiplicitySpace F n J L.toSubgroup σ).subtype

omit [CompactSpace (AdeleQuotient F)] in
/-- A finite set of finite components covers the standard compact group modulo an open level. -/
theorem exists_constantTerm_finite_cover :
    ∃ t : Finset (FiniteAdelicGL F n), ∀ k ∈ standardCompact F n,
      ∃ d ∈ t, d⁻¹ * AdelicGL.finite F n k ∈ L :=
  OperatorRealization.exists_finite_level_cover L.toSubgroup L.isOpen _
    (isCompact_standardCompact F n)

/-- The kernel of joint restriction at any such cover consists of the cusp-valued maps. -/
theorem mem_ker_restrictMultiplicityToConstantTerms_iff
    (t : Finset (FiniteAdelicGL F n))
    (ht : ∀ k ∈ standardCompact F n, ∃ d ∈ t, d⁻¹ * AdelicGL.finite F n k ∈ L)
    (φ : annihilatedFormMultiplicitySpace F n J L.toSubgroup σ) :
    φ ∈ LinearMap.ker (restrictMultiplicityToConstantTerms F n σ J L t) ↔
      ∀ v, IsCuspidal F n (automorphicToContinuous F n (φ.val v)) := by
  constructor
  · intro hφ v a b h ha hb g
    have hfixed :
        (∀ v (l : L), automorphicFiniteRightAction F n l.val (φ.val v) = φ.val v) ∧
          ∀ k v, φ.val (σ k v) = automorphicCompactRightAction F n k (φ.val v) :=
      φ.property.1
    obtain ⟨β, k, hg, hβ, hk⟩ := exists_isStandardIwasawaFactorization F n g
    obtain ⟨X, z, hβeq⟩ := exists_blockUnipotent_mul_blockDiagonalEmbedding h β hβ
    obtain ⟨d, hd, hdl⟩ := ht k hk
    let p : MaximalBlockCut n := ⟨(a, b), h, ha, hb⟩
    let ki : standardInfiniteCompact F n :=
      ⟨AdelicGL.infinite F n k, ((mem_standardCompact_iff F n k).mp hk).1⟩
    let l : L := ⟨d⁻¹ * AdelicGL.finite F n k, hdl⟩
    have hk_eq : k = AdelicGL.ofFinite F n d * AdelicGL.ofInfinite F n ki.val *
        AdelicGL.ofFinite F n l.val := by
      apply (AdelicGL.split F n).injective
      simp only [map_mul]
      change (AdelicGL.infinite F n k, AdelicGL.finite F n k) =
        (AdelicGL.infinite F n (AdelicGL.ofFinite F n d),
          AdelicGL.finite F n (AdelicGL.ofFinite F n d)) *
        (AdelicGL.infinite F n (AdelicGL.ofInfinite F n ki.val),
          AdelicGL.finite F n (AdelicGL.ofInfinite F n ki.val)) *
        (AdelicGL.infinite F n (AdelicGL.ofFinite F n l.val),
          AdelicGL.finite F n (AdelicGL.ofFinite F n l.val))
      simp [AdelicGL.ofInfinite_eq_pair, AdelicGL.ofFinite_eq_pair, ki, l]
    rw [hg, hβeq, mul_assoc, constantTerm_blockUnipotent_mul, hk_eq, ← mul_assoc, ← mul_assoc,
      ← constantTerm_automorphicFiniteRightAction, hfixed.1 v l,
      ← constantTerm_automorphicCompactRightAction, ← hfixed.2]
    exact congrArg (fun φ' => φ' p ⟨d, hd⟩ (σ ki v) z) (LinearMap.mem_ker.mp hφ)
  · intro hφ
    apply LinearMap.mem_ker.mpr
    funext p d
    apply LinearMap.ext
    intro v
    funext z
    exact hφ v p.val.1 p.val.2 p.property.1 p.property.2.1 p.property.2.2 _

end Langlands.Automorphic
