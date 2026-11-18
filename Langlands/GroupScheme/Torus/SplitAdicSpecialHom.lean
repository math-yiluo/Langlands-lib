import Langlands.GroupScheme.Torus.LocalAdicDiagonalizableModels
import Langlands.GroupScheme.HomScheme.AdicDiagonalizable
import Langlands.GroupScheme.Torus.SpecialFibreHomDescentAssembly

/-! # The formal special-fibre Hom comparison in the split case -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.AdicAffinePoints

namespace Langlands.GroupScheme.CompleteLocalDeformation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {A : Type u} [CommRing A]
  {H G : GroupScheme (Spec (CommRingCat.of A))}

/-- Stepwise bijective Hom restriction makes a compatible formal system
equivalent to its first homomorphism. -/
theorem formal_first_bijective (I : Ideal A)
    (hstep : ∀ n : ℕ, Function.Bijective
      (HomScheme.evaluate (H := H) (G := G) (transitionOver I n))) :
    Function.Bijective (fun f : HomScheme.Adic.System I H G => f.hom 0) := by
  constructor
  · intro f g h0
    apply HomScheme.Adic.System.ext
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      apply (hstep n).injective
      rw [f.compatible, g.compatible, ih]
  · intro f0
    exact HomScheme.Adic.System.exists_system_of_step_surjective I H G
      (fun n => (hstep n).surjective) f0

variable [IsLocalRing A] [IsAffine G.X.left] [Flat G.X.hom]

/-- The nilpotent diagonalizable models give bijective restriction between
every pair of successive adic quotients. -/
theorem adic_step_bijective_of_diagonalizable_special
    (hH : RelativeMultiplicativeType.IsDiagonalizable H)
    (hG : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange
        (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj G))
    (n : ℕ) :
    Function.Bijective (HomScheme.evaluate (H := H) (G := G)
      (transitionOver (IsLocalRing.maximalIdeal A) n)) := by
  exact evaluate_bijective_of_isDiagonalizable
    (A := LocalAdic.Ring A (n + 1)) (B := LocalAdic.Ring A n)
    (quotientMap (IsLocalRing.maximalIdeal A) (n + 1))
    (quotientMap (IsLocalRing.maximalIdeal A) n)
    (transition (IsLocalRing.maximalIdeal A) n)
    (transition_quotientMap (IsLocalRing.maximalIdeal A) n)
    (hH.baseChange _) (LocalAdic.isDiagonalizable A G hG (n + 1))

/-- Given adic effectivity, actual special-fibre Hom restriction is bijective
for a diagonalizable source and diagonalizable target special fibre. -/
theorem specialFibre_hom_bijective_of_adicComparison
    (hH : RelativeMultiplicativeType.IsDiagonalizable H)
    (hG : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange
        (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj G))
    (heff : Function.Bijective
      (HomScheme.Adic.System.restrict (IsLocalRing.maximalIdeal A) H G)) :
    Function.Bijective (fun f : H ⟶ G =>
      (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map f) := by
  have hformal := formal_first_bijective (H := H) (G := G) (IsLocalRing.maximalIdeal A)
    (adic_step_bijective_of_diagonalizable_special hH hG)
  have hc := hformal.comp heff
  change Function.Bijective (fun f : H ⟶ G =>
    (GroupScheme.baseChange (quotientMap (IsLocalRing.maximalIdeal A) 0)).map f) at hc
  let m := IsLocalRing.maximalIdeal A
  let r0 := Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.factor (show m ^ (0 + 1) ≤ m by simp)))
  have hr : r0 ≫ quotientMap m 0 = Spec.algebraMap A (IsLocalRing.ResidueField A) := by
    rw [quotientMap, Spec.algebraMap, ← Spec.map_comp]
    congr 1
  let a0 : Over.mk (Spec.algebraMap A (IsLocalRing.ResidueField A)) ⟶
      Over.mk (quotientMap m 0) := Over.homMk r0 hr
  have he := evaluate_bijective_of_isDiagonalizable
    (A := LocalAdic.Ring A 0) (B := IsLocalRing.ResidueField A)
    (quotientMap m 0) (Spec.algebraMap A (IsLocalRing.ResidueField A)) r0 hr
    (hH.baseChange _) (LocalAdic.isDiagonalizable A G hG 0)
  have hb := he.comp hc
  have heq : (fun f : H ⟶ G =>
      HomScheme.evaluate (H := H) (G := G) a0
        ((GroupScheme.baseChange (quotientMap m 0)).map f)) =
      (fun f : H ⟶ G =>
        (GroupScheme.baseChange
          (Spec.algebraMap A (IsLocalRing.ResidueField A))).map f) := by
    funext f
    exact HomScheme.evaluate_baseChange a0 f
  change Function.Bijective (fun f : H ⟶ G =>
    HomScheme.evaluate (H := H) (G := G) a0
      ((GroupScheme.baseChange (quotientMap m 0)).map f)) at hb
  rwa [heq] at hb

/-- In the split case, actual special-fibre Hom restriction is bijective.
This composition uses the published split adic-effectivity comparison. -/
theorem specialFibre_hom_bijective_of_diagonalizable
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hH : RelativeMultiplicativeType.IsDiagonalizable H)
    (hG : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange
        (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj G)) :
    Function.Bijective (fun f : H ⟶ G =>
      (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map f) := by
  have : IsAffineHom G.X.hom := inferInstance
  exact specialFibre_hom_bijective_of_adicComparison hH hG
    (HomScheme.AdicDiagonalizable.restrict_bijective_of_isDiagonalizable
      (IsLocalRing.maximalIdeal A) H G hH)

/-- Over a finite local splitting cover, the compiled split comparison and
an explicit descent-existence input give global special-fibre Hom bijectivity. -/
theorem specialFibre_hom_bijective_of_splitCover
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (d : LocalSplittingData A H)
    (hG : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange
        (Spec.algebraMap d.Carrier (IsLocalRing.ResidueField d.Carrier))).obj
          ((GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).obj G)))
    (hdesc : ∀ f₀ :
        (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj H ⟶
          (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj G,
      ∀ fB : (GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).obj H ⟶
          (GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).obj G,
        (GroupScheme.baseChange
          (Spec.algebraMap d.Carrier (IsLocalRing.ResidueField d.Carrier))).map fB =
          specialHomTransport (B := d.Carrier) f₀ →
        ∃ f : H ⟶ G,
          (GroupScheme.baseChange (Spec.algebraMap A d.Carrier)).map f = fB ∧
          (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map f = f₀) :
    Function.Bijective (fun f : H ⟶ G =>
      (GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map f) := by
  let B := d.Carrier
  let c := Spec.algebraMap A B
  have : IsAffine ((GroupScheme.baseChange c).obj G).X.left := by
    change IsAffine (CategoryTheory.Limits.pullback G.X.hom c)
    infer_instance
  have : Flat ((GroupScheme.baseChange c).obj G).X.hom := by
    change Flat (CategoryTheory.Limits.pullback.snd _ _)
    infer_instance
  exact specialFibre_hom_bijective_of_cover
    (specialFibre_hom_bijective_of_diagonalizable d.split hG) hdesc

end Langlands.GroupScheme.CompleteLocalDeformation
