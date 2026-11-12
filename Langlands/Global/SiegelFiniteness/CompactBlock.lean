import Langlands.Global.SiegelFiniteness.BlockMatrices
import Langlands.Global.AdelicGLStandardCompact

/-!
# Block structure of standard compact elements

An element of the standard compact subgroup is orthogonal or unitary at every infinite place.
If it vanishes in the lower-left block (rows `≥ s`, columns `< s`), its entries in the
upper-right block have zero archimedean component.
-/

noncomputable section

universe u

open NumberField

set_option autoImplicit false

namespace Langlands.Global.SiegelFiniteness

open PrimitiveAdelicHeight

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

/-- **Upper-right archimedean components vanish.** -/
theorem infinite_entry_eq_zero {m : AdelicGL F n} (hm : m ∈ standardCompact F n) {s : ℕ}
    (hblock : IsBlockUpper s (m : Matrix (Fin n) (Fin n) (Adeles F))) (a b : Fin n)
    (ha : a.val < s) (hb : s ≤ b.val) :
    ((m : Matrix (Fin n) (Fin n) (Adeles F)) a b).1 = 0 := by
  have hinf := ((mem_standardCompact_iff F n m).mp hm).1
  obtain ⟨hreal, hcomplex⟩ := (mem_standardInfiniteCompact_iff F n _).mp hinf
  funext w
  rcases NumberField.InfinitePlace.isReal_or_isComplex w with hw | hw
  · set v : {v : InfinitePlace F // InfinitePlace.IsReal v} := ⟨w, hw⟩
    have hU := hreal v
    have hblockU : IsBlockUpper s (ArchimedeanGL.realMatrix F n
        (archimedeanGLCoordinates F n (AdelicGL.infinite F n m)) v) := by
      intro i j hi hj
      have hz : ((AdelicGL.infinite F n m : InfiniteAdelicGL F n) :
          Matrix (Fin n) (Fin n) (InfiniteAdeleRing F)) i j = 0 := by
        rw [AdelicGL.infinite_apply, hblock i j hi hj]
        rfl
      change (archimedeanGLCoordinates F n (AdelicGL.infinite F n m) i j).1 v = 0
      rw [archimedeanGLCoordinates_apply, hz, map_zero]
      rfl
    have hzero := unitary_upperRight_eq_zero hU hblockU a b ha hb
    have hnorm := norm_realCoord ((m : Matrix (Fin n) (Fin n) (Adeles F)) a b).1 v
    have : realCoord v (InfiniteAdeleRing.ringEquiv_mixedSpace F
        ((m : Matrix (Fin n) (Fin n) (Adeles F)) a b).1) = 0 := hzero
    rw [this, norm_zero] at hnorm
    exact norm_eq_zero.mp hnorm.symm
  · set v : {v : InfinitePlace F // InfinitePlace.IsComplex v} := ⟨w, hw⟩
    have hU := hcomplex v
    have hblockU : IsBlockUpper s (ArchimedeanGL.complexMatrix F n
        (archimedeanGLCoordinates F n (AdelicGL.infinite F n m)) v) := by
      intro i j hi hj
      have hz : ((AdelicGL.infinite F n m : InfiniteAdelicGL F n) :
          Matrix (Fin n) (Fin n) (InfiniteAdeleRing F)) i j = 0 := by
        rw [AdelicGL.infinite_apply, hblock i j hi hj]
        rfl
      change (archimedeanGLCoordinates F n (AdelicGL.infinite F n m) i j).2 v = 0
      rw [archimedeanGLCoordinates_apply, hz, map_zero]
      rfl
    have hzero := unitary_upperRight_eq_zero hU hblockU a b ha hb
    have hnorm := norm_complexCoord ((m : Matrix (Fin n) (Fin n) (Adeles F)) a b).1 v
    have : complexCoord v (InfiniteAdeleRing.ringEquiv_mixedSpace F
        ((m : Matrix (Fin n) (Fin n) (Adeles F)) a b).1) = 0 := hzero
    rw [this, norm_zero] at hnorm
    exact norm_eq_zero.mp hnorm.symm

end Langlands.Global.SiegelFiniteness
