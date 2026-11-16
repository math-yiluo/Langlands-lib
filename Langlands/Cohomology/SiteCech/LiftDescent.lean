import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Correcting a local lift by a degree-one Hom boundary -/

noncomputable section

namespace Langlands.Cohomology.SiteCech

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {D : Type u} [Category.{v} D] [Abelian D]
variable (P : ChainComplex D ℕ) {A : D}
variable (ε : P.X 0 ⟶ A) (hε : P.d 1 0 ≫ ε = 0)
variable (S : ShortComplex D) (hS : S.Exact) [hMono : Mono S.f]
variable (s : A ⟶ S.X₃) (t : P.X 0 ⟶ S.X₂)
variable (ht : t ≫ S.g = ε ≫ s)

/-- The failure of a local lift to descend, as a morphism into the kernel
coefficient object. -/
def liftObstruction : P.X 1 ⟶ S.X₁ :=
  hS.lift (P.d 1 0 ≫ t) (by
    rw [Category.assoc, ht, ← Category.assoc, hε, zero_comp])

@[reassoc (attr := simp)]
theorem liftObstruction_f :
    liftObstruction P ε hε S hS s t ht ≫ S.f = P.d 1 0 ≫ t :=
  hS.lift_f _ _

/-- The obstruction is a degree-one cocycle in the Hom cochain complex. -/
theorem d_liftObstruction :
    P.d 2 1 ≫ liftObstruction P ε hε S hS s t ht = 0 := by
  apply (cancel_mono S.f).1
  simp only [Category.assoc, liftObstruction_f, zero_comp]
  rw [← Category.assoc, P.d_comp_d, zero_comp]

variable (R : Type w) [Ring R] [Linear R D]

include hε hS hMono t ht in
/-- Degree-one Hom exactness corrects the local lift so it is killed by the
first chain differential and still lifts the same target map. -/
theorem exists_correctedLocalLift
    (hHom : (P.linearYonedaObj R S.X₁).ExactAt 1) :
    ∃ t' : P.X 0 ⟶ S.X₂, P.d 1 0 ≫ t' = 0 ∧ t' ≫ S.g = ε ≫ s := by
  have h := (HomologicalComplex.exactAt_iff'
    (P.linearYonedaObj R S.X₁) 0 1 2 (by simp) (by simp)).1 hHom
  obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff _).1 h
    (liftObstruction P ε hε S hS s t ht)
    (d_liftObstruction P ε hε S hS s t ht)
  change P.X 0 ⟶ S.X₁ at b
  change P.d 1 0 ≫ b = liftObstruction P ε hε S hS s t ht at hb
  refine ⟨t - b ≫ S.f, ?_, ?_⟩
  · rw [Preadditive.comp_sub, ← Category.assoc, hb, liftObstruction_f, sub_self]
  · rw [Preadditive.sub_comp, Category.assoc, S.zero, comp_zero, sub_zero, ht]

variable [Epi ε]

/-- A local lift descends to a global lift when the augmented complex is
exact at degree zero and its coefficient Hom complex is exact at degree one. -/
def liftByCechExactness
    (hAug : (ShortComplex.mk (P.d 1 0) ε hε).Exact)
    (hHom : (P.linearYonedaObj R S.X₁).ExactAt 1) :
    {l : A ⟶ S.X₂ // l ≫ S.g = s} := by
  let h := exists_correctedLocalLift P ε hε S hS s t ht R hHom
  let t' := Classical.choose h
  have hd := (Classical.choose_spec h).1
  have hg := (Classical.choose_spec h).2
  refine ⟨hAug.desc t' hd, ?_⟩
  apply (cancel_epi ε).1
  rw [← Category.assoc, hAug.g_desc, hg]

end Langlands.Cohomology.SiteCech
