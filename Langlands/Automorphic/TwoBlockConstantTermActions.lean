import Langlands.Automorphic.TwoBlockConstantTermCovariance
import Langlands.Global.AdelicGLInverseTranspose

/-! # Finite level and compact action on the two-block constant term -/

noncomputable section
universe u

set_option autoImplicit false

namespace Langlands.GeneralLinear

open scoped Matrix

/-- A block diagonal matrix is unitary if both blocks are unitary. -/
theorem blockDiagonalEmbedding_mem_unitary {R : Type u} [CommRing R] [StarRing R]
    {a b n : ℕ} (h : a + b = n) (A : GeneralLinear a R) (D : GeneralLinear b R)
    (hA : A.val ∈ Matrix.unitaryGroup (Fin a) R)
    (hD : D.val ∈ Matrix.unitaryGroup (Fin b) R) :
    (blockDiagonalEmbedding h (A, D)).val ∈ Matrix.unitaryGroup (Fin n) R := by
  let e := Matrix.reindexRingEquiv R (finSumFinEquiv.trans (finCongr h))
  have hval : (blockDiagonalEmbedding h (A, D)).val = e (Matrix.fromBlocks A.val 0 0 D.val) := rfl
  have hstar (M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R) :
      star (e M) = e (star M) := rfl
  have hA' : A.val * A.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hA
  have hD' : D.val * D.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hD
  rw [Matrix.mem_unitaryGroup_iff, hval, hstar, ← map_mul, Matrix.star_eq_conjTranspose,
    Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hA', hD',
    Matrix.fromBlocks_one, map_one]

end Langlands.GeneralLinear

namespace Langlands.Global

open Langlands.GeneralLinear NumberField

variable (F : Type u) [Field F] [NumberField F] {a b n : ℕ} (h : a + b = n)

theorem AdelicGL.rational_blockDiagonalEmbedding (x : RationalGL F a) (y : RationalGL F b) :
    AdelicGL.rational F n (blockDiagonalEmbedding h (x, y)) =
      blockDiagonalEmbedding h (AdelicGL.rational F a x, AdelicGL.rational F b y) :=
  map_blockDiagonalEmbedding h _ _

theorem AdelicGL.infinite_blockDiagonalEmbedding (z : AdelicGL F a × AdelicGL F b) :
    AdelicGL.infinite F n (blockDiagonalEmbedding h z) =
      blockDiagonalEmbedding h (AdelicGL.infinite F a z.1, AdelicGL.infinite F b z.2) :=
  map_blockDiagonalEmbedding h _ _

theorem AdelicGL.finite_blockDiagonalEmbedding (z : AdelicGL F a × AdelicGL F b) :
    AdelicGL.finite F n (blockDiagonalEmbedding h z) =
      blockDiagonalEmbedding h (AdelicGL.finite F a z.1, AdelicGL.finite F b z.2) :=
  map_blockDiagonalEmbedding h _ _

theorem AdelicGL.blockDiagonalEmbedding_ofFinite (x : FiniteAdelicGL F a)
    (y : FiniteAdelicGL F b) :
    blockDiagonalEmbedding h (AdelicGL.ofFinite F a x, AdelicGL.ofFinite F b y) =
      AdelicGL.ofFinite F n (blockDiagonalEmbedding h (x, y)) := by
  apply (AdelicGL.split F n).injective
  apply Prod.ext
  · change AdelicGL.infinite F n _ = AdelicGL.infinite F n _
    rw [AdelicGL.infinite_blockDiagonalEmbedding, AdelicGL.infinite_ofFinite,
      AdelicGL.infinite_ofFinite, AdelicGL.infinite_ofFinite]
    exact map_one _
  · change AdelicGL.finite F n _ = AdelicGL.finite F n _
    rw [AdelicGL.finite_blockDiagonalEmbedding, AdelicGL.finite_ofFinite,
      AdelicGL.finite_ofFinite, AdelicGL.finite_ofFinite]

theorem AdelicGL.blockDiagonalEmbedding_ofInfinite (x : InfiniteAdelicGL F a)
    (y : InfiniteAdelicGL F b) :
    blockDiagonalEmbedding h (AdelicGL.ofInfinite F a x, AdelicGL.ofInfinite F b y) =
      AdelicGL.ofInfinite F n (blockDiagonalEmbedding h (x, y)) := by
  apply (AdelicGL.split F n).injective
  apply Prod.ext
  · change AdelicGL.infinite F n _ = AdelicGL.infinite F n _
    rw [AdelicGL.infinite_blockDiagonalEmbedding, AdelicGL.infinite_ofInfinite,
      AdelicGL.infinite_ofInfinite, AdelicGL.infinite_ofInfinite]
  · change AdelicGL.finite F n _ = AdelicGL.finite F n _
    rw [AdelicGL.finite_blockDiagonalEmbedding, AdelicGL.finite_ofInfinite,
      AdelicGL.finite_ofInfinite, AdelicGL.finite_ofInfinite]
    exact map_one _

omit [NumberField F] in
/-- The block diagonal embedding takes standard infinite compact factors to the
standard infinite compact group of the larger rank. -/
theorem blockDiagonalEmbedding_mem_standardInfiniteCompact
    (x : InfiniteAdelicGL F a) (y : InfiniteAdelicGL F b)
    (hx : x ∈ standardInfiniteCompact F a) (hy : y ∈ standardInfiniteCompact F b) :
    blockDiagonalEmbedding h (x, y) ∈ standardInfiniteCompact F n := by
  rw [mem_standardInfiniteCompact_iff] at hx hy ⊢
  constructor
  · intro v
    let p := ((Pi.evalRingHom (fun _ : {v : InfinitePlace F // v.IsReal} => ℝ) v).comp
      (RingHom.fst _ _)).comp (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
    change (Matrix.GeneralLinearGroup.map p (blockDiagonalEmbedding h (x, y))).val ∈ _
    rw [map_blockDiagonalEmbedding]
    exact blockDiagonalEmbedding_mem_unitary h _ _ (hx.1 v) (hy.1 v)
  · intro v
    let p := ((Pi.evalRingHom (fun _ : {v : InfinitePlace F // v.IsComplex} => ℂ) v).comp
      (RingHom.snd _ _)).comp (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
    change (Matrix.GeneralLinearGroup.map p (blockDiagonalEmbedding h (x, y))).val ∈ _
    rw [map_blockDiagonalEmbedding]
    exact blockDiagonalEmbedding_mem_unitary h _ _ (hx.2 v) (hy.2 v)

omit [NumberField F] in
/-- The product of the standard infinite compact groups inside the larger one. -/
def twoBlockInfiniteCompact :
    standardInfiniteCompact F a × standardInfiniteCompact F b →* standardInfiniteCompact F n :=
  ((blockDiagonalEmbedding h).comp
    ((standardInfiniteCompact F a).subtype.prodMap (standardInfiniteCompact F b).subtype)).codRestrict _
      (fun k => blockDiagonalEmbedding_mem_standardInfiniteCompact F h _ _ k.1.property k.2.property)

end Langlands.Global

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear ContinuousRationalFunctions

variable (F : Type u) [Field F] [NumberField F] {a b n : ℕ} (h : a + b = n)

local instance (r : ℕ) : AddCommGroup (RationalInvariantFunctions F r) := Submodule.addCommGroup _
local instance (r : ℕ) : AddCommGroup (ContinuousRationalFunctions F r) := Submodule.addCommGroup _
local instance (r : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F r) := Submodule.addCommGroup _
local instance (r : ℕ) : AddCommGroup (AutomorphicForms F r) := Submodule.addCommGroup _

/-- The pullback of the conjugated ambient level to the finite two-block Levi. -/
def twoBlockConstantTermLevel (L : OpenSubgroup (FiniteAdelicGL F n)) (d : FiniteAdelicGL F n) :
    OpenSubgroup (FiniteAdelicGL F a × FiniteAdelicGL F b) :=
  L.comap ((MulAut.conj d⁻¹).toMonoidHom.comp (blockDiagonalEmbedding h)) (by
    change Continuous (fun z => d⁻¹ * blockDiagonalEmbedding h z * (d⁻¹)⁻¹)
    exact (continuous_const.mul (continuous_blockDiagonalEmbedding h)).mul continuous_const)

theorem mem_twoBlockConstantTermLevel (L : OpenSubgroup (FiniteAdelicGL F n))
    (d : FiniteAdelicGL F n) (z : FiniteAdelicGL F a × FiniteAdelicGL F b) :
    z ∈ twoBlockConstantTermLevel F h L d ↔ d⁻¹ * blockDiagonalEmbedding h z * d ∈ L := by
  rw [twoBlockConstantTermLevel, OpenSubgroup.mem_comap]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]

variable [CompactSpace (AdeleQuotient F)]

/-- Restricted constant terms are invariant under the rational points of the product Levi. -/
theorem blockConstantTermAt_mul_rational (d : FiniteAdelicGL F n) (f : AutomorphicForms F n)
    (z : AdelicGL F a × AdelicGL F b) (x : RationalGL F a × RationalGL F b) :
    blockConstantTermAt F n h d f ((AdelicGL.rational F a x.1, AdelicGL.rational F b x.2) * z) =
      blockConstantTermAt F n h d f z := by
  change constantTerm F n h (automorphicToContinuous F n f)
      (blockDiagonalEmbedding h ((AdelicGL.rational F a x.1, AdelicGL.rational F b x.2) * z) *
        AdelicGL.ofFinite F n d) =
    constantTerm F n h (automorphicToContinuous F n f)
      (blockDiagonalEmbedding h z * AdelicGL.ofFinite F n d)
  rw [map_mul, ← AdelicGL.rational_blockDiagonalEmbedding, mul_assoc,
    constantTerm_rational_blockDiagonalEmbedding]

/-- Restricted constant terms are jointly continuous in both Levi variables. -/
theorem continuous_blockConstantTermAt (d : FiniteAdelicGL F n) (f : AutomorphicForms F n) :
    Continuous (blockConstantTermAt F n h d f) :=
  (continuous_blockConstantTerm F h (automorphicToContinuous F n f)).comp
    ((continuous_blockDiagonalEmbedding h).mul continuous_const)

/-- The finite right translation through the Levi corresponds to its conjugate by
the given finite translation of the constant term. -/
theorem blockConstantTermAt_mul_finite (d : FiniteAdelicGL F n) (f : AutomorphicForms F n)
    (z : AdelicGL F a × AdelicGL F b) (x : FiniteAdelicGL F a × FiniteAdelicGL F b) :
    blockConstantTermAt F n h d f (z * (AdelicGL.ofFinite F a x.1, AdelicGL.ofFinite F b x.2)) =
      blockConstantTermAt F n h d
        (automorphicFiniteRightAction F n (d⁻¹ * blockDiagonalEmbedding h x * d) f) z := by
  change constantTerm F n h (automorphicToContinuous F n f)
      (blockDiagonalEmbedding h (z * (AdelicGL.ofFinite F a x.1, AdelicGL.ofFinite F b x.2)) *
        AdelicGL.ofFinite F n d) =
    constantTerm F n h (automorphicToContinuous F n
      (automorphicFiniteRightAction F n (d⁻¹ * blockDiagonalEmbedding h x * d) f))
        (blockDiagonalEmbedding h z * AdelicGL.ofFinite F n d)
  rw [automorphicToContinuous_finiteRightAction]
  change _ = constantTerm F n h (continuousRightAction F n
    (AdelicGL.ofFinite F n (d⁻¹ * blockDiagonalEmbedding h x * d))
      (automorphicToContinuous F n f)) _
  rw [constantTerm_rightAction, map_mul, AdelicGL.blockDiagonalEmbedding_ofFinite]
  congr 1
  simp only [← map_mul, mul_assoc, mul_inv_cancel_left]

/-- At every level fixing the source form, the induced open Levi level fixes
its restricted constant term. -/
theorem blockConstantTermAt_level_invariant (L : OpenSubgroup (FiniteAdelicGL F n))
    (d : FiniteAdelicGL F n) (f : AutomorphicForms F n)
    (hf : ∀ l : L, automorphicFiniteRightAction F n l.val f = f)
    (z : AdelicGL F a × AdelicGL F b) (x : twoBlockConstantTermLevel F h L d) :
    blockConstantTermAt F n h d f
      (z * (AdelicGL.ofFinite F a x.val.1, AdelicGL.ofFinite F b x.val.2)) =
        blockConstantTermAt F n h d f z := by
  rw [blockConstantTermAt_mul_finite]
  exact congrArg (fun f' => blockConstantTermAt F n h d f' z)
    (hf ⟨_, (mem_twoBlockConstantTermLevel F h L d x.val).mp x.property⟩)

/-- The infinite compact action is intertwined with the standard compact
inclusion of the two blocks. -/
theorem blockConstantTermAt_mul_compact (d : FiniteAdelicGL F n) (f : AutomorphicForms F n)
    (z : AdelicGL F a × AdelicGL F b)
    (k : standardInfiniteCompact F a × standardInfiniteCompact F b) :
    blockConstantTermAt F n h d f
      (z * (AdelicGL.ofInfinite F a k.1.val, AdelicGL.ofInfinite F b k.2.val)) =
        blockConstantTermAt F n h d
          (automorphicCompactRightAction F n (twoBlockInfiniteCompact F h k) f) z := by
  change constantTerm F n h (automorphicToContinuous F n f)
      (blockDiagonalEmbedding h (z * (AdelicGL.ofInfinite F a k.1.val, AdelicGL.ofInfinite F b k.2.val)) *
        AdelicGL.ofFinite F n d) =
    constantTerm F n h (automorphicToContinuous F n
      (automorphicCompactRightAction F n (twoBlockInfiniteCompact F h k) f))
        (blockDiagonalEmbedding h z * AdelicGL.ofFinite F n d)
  rw [automorphicToContinuous_compactRightAction]
  change _ = constantTerm F n h (continuousRightAction F n
    (AdelicGL.ofInfinite F n (blockDiagonalEmbedding h (k.1.val, k.2.val)))
      (automorphicToContinuous F n f)) _
  rw [constantTerm_rightAction, map_mul, AdelicGL.blockDiagonalEmbedding_ofInfinite, mul_assoc,
    ← (AdelicGL.ofFinite_commute_ofInfinite F n d (blockDiagonalEmbedding h (k.1.val, k.2.val))).eq,
    ← mul_assoc]

end Langlands.Automorphic
