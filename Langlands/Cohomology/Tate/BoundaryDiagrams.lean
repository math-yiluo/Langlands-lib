import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- A cycle representative determines a class in the actual homology object. -/
def cycleClass (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : K.X n) (hx : K.d n (n + 1) x = 0) : K.homology n :=
  K.homologyπ n (K.cyclesMk x (n + 1) (by simp) hx)

lemma cycleClass_surjective (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (c : K.homology n) :
    ∃ (x : K.X n) (hx : K.d n (n + 1) x = 0), cycleClass K n x hx = c := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance c
  have hz : K.d n (n + 1) (K.iCycles n z) = 0 := by
    exact ConcreteCategory.congr_hom (K.iCycles_d n (n + 1)) z
  refine ⟨K.iCycles n z, hz, ?_⟩
  unfold cycleClass
  apply congrArg (K.homologyπ n)
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  exact K.i_cyclesMk _ _ _ _

lemma cycleClass_neg (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : K.X n) (hx : K.d n (n + 1) x = 0) :
    cycleClass K n (-x) (by rw [map_neg, hx, neg_zero]) = -cycleClass K n x hx := by
  have hcycles :
      K.cyclesMk (-x) (n + 1) (by simp) (by
        change (K.d n (n + 1)).hom (-x) = 0
        exact (map_neg (K.d n (n + 1)).hom x).trans ((congrArg Neg.neg hx).trans neg_zero)) =
        -K.cyclesMk x (n + 1) (by simp) hx := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    calc
      _ = -x := K.i_cyclesMk _ _ _ _
      _ = _ := ((map_neg (K.iCycles n).hom _).trans
        (congrArg Neg.neg (K.i_cyclesMk x (n + 1) (by simp) hx))).symm
  exact (congrArg (K.homologyπ n) hcycles).trans (map_neg (K.homologyπ n).hom _)

/-- Compute the actual connecting map from a lift and its differential. -/
lemma delta_cycleClass {S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)}
    (hS : S.ShortExact) (n : ℤ) (z : S.X₃.X n) (hz : S.X₃.d n (n + 1) z = 0)
    (y : S.X₂.X n) (hy : S.g.f n y = z) (x : S.X₁.X (n + 1))
    (hx : S.f.f (n + 1) x = S.X₂.d n (n + 1) y) :
    hS.δ n (n + 1) rfl (cycleClass S.X₃ n z hz) =
      cycleClass S.X₁ (n + 1) x
        (hS.d_eq_zero_of_f_eq_d_apply n (n + 1) y x hx (n + 1 + 1)) :=
  hS.δ_apply n (n + 1) rfl z hz y hy x hx (n + 1 + 1) (by simp)

lemma complexMap_d_apply {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K ⟶ L) (i j : ℤ) (x : K.X i) :
    f.f j (K.d i j x) = L.d i j (f.f i x) :=
  (ConcreteCategory.congr_hom (f.comm i j) x).symm

lemma complexSquare_left_apply
    {S T : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)}
    (f : S ⟶ T) (n : ℤ) (x : S.X₁.X n) :
    f.τ₂.f n (S.f.f n x) = T.f.f n (f.τ₁.f n x) :=
  (ConcreteCategory.congr_hom (congrArg (fun a => a.f n) f.comm₁₂) x).symm

lemma complexSquare_right_apply
    {S T : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)}
    (f : S ⟶ T) (n : ℤ) (x : S.X₂.X n) :
    f.τ₃.f n (S.g.f n x) = T.g.f n (f.τ₂.f n x) :=
  (ConcreteCategory.congr_hom (congrArg (fun a => a.f n) f.comm₂₃) x).symm

end Langlands.Tate
