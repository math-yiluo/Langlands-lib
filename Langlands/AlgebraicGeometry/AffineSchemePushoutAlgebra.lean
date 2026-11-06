import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.RingTheory.Localization.Away.Basic

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace Langlands.AlgebraicGeometry.AffineSchemePushout

section Localization

variable {B C D B' C' D' : Type u}
  [CommRing B] [CommRing C] [CommRing D]
  [CommRing B'] [CommRing C'] [CommRing D']
  [Algebra B B'] [Algebra C C'] [Algebra D D']
  (f : B →+* D) (g : C →+* D) (f' : B' →+* D') (g' : C' →+* D')
  (hf : f'.comp (algebraMap B B') = (algebraMap D D').comp f)
  (hg : g'.comp (algebraMap C C') = (algebraMap D D').comp g)

/-- The map between explicit ring pullbacks induced by a commutative cube. -/
def pullbackMap : f.pullback g →+* f'.pullback g' :=
  ((algebraMap B B').prodMap (algebraMap C C')).comp (f.pullback g).subtype |>.codRestrict
    (f'.pullback g') (fun a => by
      change f' (algebraMap B B' a.1.1) = g' (algebraMap C C' a.1.2)
      calc
        _ = algebraMap D D' (f a.1.1) := DFunLike.congr_fun hf _
        _ = algebraMap D D' (g a.1.2) := congrArg (algebraMap D D') a.2
        _ = _ := (DFunLike.congr_fun hg _).symm)

@[simp]
lemma pullbackMap_fst (a : f.pullback g) :
    (pullbackMap f g f' g' hf hg a).1.1 = algebraMap B B' a.1.1 := rfl

@[simp]
lemma pullbackMap_snd (a : f.pullback g) :
    (pullbackMap f g f' g' hf hg a).1.2 = algebraMap C C' a.1.2 := rfl

/-- Localization at a compatible element commutes with a ring pullback. -/
theorem isLocalization_pullback (a : f.pullback g)
    [IsLocalization.Away a.1.1 B'] [IsLocalization.Away a.1.2 C']
    [IsLocalization.Away (f a.1.1) D'] :
    letI := (pullbackMap f g f' g' hf hg).toAlgebra
    IsLocalization.Away a (f'.pullback g') := by
  let := (pullbackMap f g f' g' hf hg).toAlgebra
  have hf_apply (b : B) : f' (algebraMap B B' b) = algebraMap D D' (f b) :=
    DFunLike.congr_fun hf b
  have hg_apply (c : C) : g' (algebraMap C C' c) = algebraMap D D' (g c) :=
    DFunLike.congr_fun hg c
  have ha : f a.1.1 = g a.1.2 := a.2
  refine IsLocalization.Away.mk a ?_ ?_ ?_
  · exact (RingHom.isUnit_pullback_mk_iff f' g' _).mpr
      ⟨IsLocalization.Away.algebraMap_isUnit a.1.1,
        IsLocalization.Away.algebraMap_isUnit a.1.2⟩
  · intro z
    obtain ⟨m, b, hb⟩ := IsLocalization.Away.surj a.1.1 z.1.1
    obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj a.1.2 z.1.2
    have he : algebraMap D D' (f (a.1.1 ^ n * b)) =
        algebraMap D D' (g (a.1.2 ^ m * c)) := by
      rw [← hf_apply, ← hg_apply]
      simp only [map_mul, map_pow]
      rw [← hb, ← hc, map_mul, map_mul, map_pow, map_pow,
        hf_apply, hg_apply, ha, show f' z.1.1 = g' z.1.2 from z.2]
      ring
    obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (f a.1.1) he
    let t : f.pullback g := ⟨(a.1.1 ^ (k + n) * b, a.1.2 ^ (k + m) * c), by
      change f (a.1.1 ^ (k + n) * b) = g (a.1.2 ^ (k + m) * c)
      simpa only [map_mul, map_pow, pow_add, mul_assoc, ha] using hk⟩
    refine ⟨k + m + n, t, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change z.1.1 * algebraMap B B' a.1.1 ^ (k + m + n) =
        algebraMap B B' (a.1.1 ^ (k + n) * b)
      simp only [map_mul, map_pow]
      calc
        _ = (algebraMap B B' a.1.1 ^ (k + n)) *
            (z.1.1 * algebraMap B B' a.1.1 ^ m) := by ring
        _ = _ := by rw [hb]
    · change z.1.2 * algebraMap C C' a.1.2 ^ (k + m + n) =
        algebraMap C C' (a.1.2 ^ (k + m) * c)
      simp only [map_mul, map_pow]
      calc
        _ = (algebraMap C C' a.1.2 ^ (k + m)) *
            (z.1.2 * algebraMap C C' a.1.2 ^ n) := by ring
        _ = _ := by rw [hc]
  · intro x y h
    have hB : algebraMap B B' x.1.1 = algebraMap B B' y.1.1 :=
      congrArg (fun z : f'.pullback g' => z.1.1) h
    have hC : algebraMap C C' x.1.2 = algebraMap C C' y.1.2 :=
      congrArg (fun z : f'.pullback g' => z.1.2) h
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq a.1.1 hB
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq a.1.2 hC
    refine ⟨m + n, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change a.1.1 ^ (m + n) * x.1.1 = a.1.1 ^ (m + n) * y.1.1
      calc
        _ = a.1.1 ^ n * (a.1.1 ^ m * x.1.1) := by ring
        _ = a.1.1 ^ n * (a.1.1 ^ m * y.1.1) := by rw [hm]
        _ = _ := by ring
    · change a.1.2 ^ (m + n) * x.1.2 = a.1.2 ^ (m + n) * y.1.2
      calc
        _ = a.1.2 ^ m * (a.1.2 ^ n * x.1.2) := by ring
        _ = a.1.2 ^ m * (a.1.2 ^ n * y.1.2) := by rw [hn]
        _ = _ := by ring

end Localization

end Langlands.AlgebraicGeometry.AffineSchemePushout
