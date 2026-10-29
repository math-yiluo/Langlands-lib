import Langlands.CategoryTheory.Renard.SubobjectSimpleCokernelStatements

/-!
# Simple cokernels and covers of subobjects: proof

Proves `Langlands.Renard.SubobjectSimpleCokernelStatement C` for every abelian
category `C`, with independent object and Hom universes. This is a derived
internal bridge used for Renard 2026, Appendix A.VI.2(9) and A.VI.3, printed
page 263 / PDF page 269; the source does not state the criterion separately.
-/

namespace Langlands.Renard

open CategoryTheory CategoryTheory.Limits

universe u v

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual quotient `B/A` is a zero object exactly when `A = B`. -/
theorem isZero_cokernel_ofLE_iff {X : C} {A B : Subobject X} (h : A ≤ B) :
    IsZero (cokernel (Subobject.ofLE A B h)) ↔ A = B := by
  constructor
  · intro hz
    have : Epi (Subobject.ofLE A B h) :=
      Preadditive.epi_of_cokernel_zero (hz.eq_of_tgt _ _)
    have : IsIso (Subobject.ofLE A B h) := isIso_of_mono_of_epi _
    exact le_antisymm h (Subobject.le_of_comm (inv (Subobject.ofLE A B h)) (by simp))
  · rintro rfl
    have : IsIso (Subobject.ofLE A A h) := by
      rw [Subobject.ofLE_refl]
      infer_instance
    exact IsZero.of_epi_eq_zero _ (cokernel.π_of_epi _)

/-- If the actual quotient `B/A` is simple, then `B` covers `A`. -/
theorem covBy_of_simple_cokernel {X : C} {A B : Subobject X} (h : A ≤ B)
    (hs : Simple (cokernel (Subobject.ofLE A B h))) : A ⋖ B := by
  refine covBy_iff_lt_and_eq_or_eq.mpr ⟨lt_of_le_of_ne h fun hAB =>
    Simple.not_isZero _ ((isZero_cokernel_ofLE_iff h).mpr hAB), fun D hAD hDB => ?_⟩
  by_cases hz : Subobject.ofLE D B hDB ≫ cokernel.π (Subobject.ofLE A B h) = 0
  · -- The inclusion of `D` lands in the kernel `A` of the quotient map.
    left
    refine le_antisymm (Subobject.le_of_comm
      (Abelian.monoLift (Subobject.ofLE A B h) (Subobject.ofLE D B hDB) hz) ?_) hAD
    rw [← Subobject.ofLE_arrow h, Abelian.monoLift_comp_assoc, Subobject.ofLE_arrow]
  · -- A nonzero map to the simple quotient is an epimorphism, so `D = B`.
    right
    have hπ : Epi (Subobject.ofLE D B hDB ≫ cokernel.π (Subobject.ofLE A B h)) :=
      Preadditive.epi_of_cokernel_zero (cokernel_zero_of_nonzero_to_simple hz)
    have : Epi (Subobject.ofLE D B hDB) := Preadditive.epi_of_cancel_zero _ fun t ht => by
      have hft : Subobject.ofLE A B h ≫ t = 0 := by
        rw [← Subobject.ofLE_comp_ofLE A D B hAD hDB, Category.assoc, ht, comp_zero]
      have hd : cokernel.desc (Subobject.ofLE A B h) t hft = 0 := by
        rw [← cancel_epi (Subobject.ofLE D B hDB ≫ cokernel.π (Subobject.ofLE A B h)),
          comp_zero, Category.assoc, cokernel.π_desc, ht]
      rw [← cokernel.π_desc (Subobject.ofLE A B h) t hft, hd, comp_zero]
    have : IsIso (Subobject.ofLE D B hDB) := isIso_of_mono_of_epi _
    exact le_antisymm hDB (Subobject.le_of_comm (inv (Subobject.ofLE D B hDB)) (by simp))

/-- If `B` covers `A`, then the actual quotient `B/A` is simple. -/
theorem simple_cokernel_of_covBy {X : C} {A B : Subobject X} (h : A ≤ B) (hc : A ⋖ B) :
    Simple (cokernel (Subobject.ofLE A B h)) := by
  have hne : ¬ IsZero (cokernel (Subobject.ofLE A B h)) := fun hz =>
    hc.lt.ne ((isZero_cokernel_ofLE_iff h).mp hz)
  refine ⟨fun {Y} m _ => ⟨fun hiso hm => hne ?_, fun hm => ?_⟩⟩
  · -- A zero isomorphism onto the quotient would make the quotient zero.
    exact IsZero.of_epi_eq_zero m hm
  · -- Pull the subobject `m` of `B/A` back to a subobject `D` of `X` with `A ≤ D ≤ B`.
    have hAD : A ≤ Subobject.mk
        (pullback.snd m (cokernel.π (Subobject.ofLE A B h)) ≫ B.arrow) :=
      Subobject.le_mk_of_comm
        (pullback.lift (0 : (A : C) ⟶ Y) (Subobject.ofLE A B h)
          (by rw [zero_comp, cokernel.condition]))
        (by rw [pullback.lift_snd_assoc, Subobject.ofLE_arrow])
    have hDB : Subobject.mk
        (pullback.snd m (cokernel.π (Subobject.ofLE A B h)) ≫ B.arrow) ≤ B :=
      Subobject.mk_le_of_comm _ rfl
    rcases hc.eq_or_eq hAD hDB with hDA | hDB'
    · -- If `D = A`, the epimorphic projection to `Y` composed with `m` is zero.
      exfalso
      apply hm
      have hs : Subobject.ofMkLE _ A hDA.le ≫ Subobject.ofLE A B h =
          pullback.snd m (cokernel.π (Subobject.ofLE A B h)) := by
        rw [← cancel_mono B.arrow]
        simp
      rw [← cancel_epi (pullback.fst m (cokernel.π (Subobject.ofLE A B h))), comp_zero,
        pullback.condition, ← hs, Category.assoc, cokernel.condition, comp_zero]
    · -- If `D = B`, the quotient map factors through `m`, so `m` is an epimorphism.
      have ht : Subobject.ofLEMk B _ hDB'.ge ≫
          pullback.snd m (cokernel.π (Subobject.ofLE A B h)) = 𝟙 _ := by
        rw [← cancel_mono B.arrow]
        simp
      have hfac : (Subobject.ofLEMk B _ hDB'.ge ≫
          pullback.fst m (cokernel.π (Subobject.ofLE A B h))) ≫ m =
          cokernel.π (Subobject.ofLE A B h) := by
        rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
      have : Epi m := epi_of_epi_fac hfac
      exact isIso_of_mono_of_epi m

end

/-- Proof of `SubobjectSimpleCokernelStatement`: in every abelian category, the
actual quotient `B/A` of subobjects `A ≤ B` is simple exactly when `B` covers `A`. -/
theorem subobjectSimpleCokernelStatement (C : Type u) [Category.{v} C] [Abelian C] :
    SubobjectSimpleCokernelStatement C :=
  fun _ _ _ h => ⟨covBy_of_simple_cokernel h, simple_cokernel_of_covBy h⟩

end Langlands.Renard
