import Langlands.Representation.Hecke.HomomorphismLeft
import Langlands.Representation.Hecke.HaarInversion

/-! # The right Hecke action and the remaining induction functors

Renard III.2.1, printed p.70 / PDF p.76. All actions are on the published
Haar Hecke algebra; inversion is the inversion of distributions.
-/

noncomputable section

open CategoryTheory MeasureTheory MulOpposite

namespace Langlands.Hecke.Homomorphism

open Langlands.Algebra

universe uG uH v

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] [T2Space H]
  [NonarchimedeanGroup H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  (μG : Measure G) [μG.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]
  (φ : H →* G) (hφ : Continuous φ)

/-- The right regular distribution representation, restricted along `φ`. -/
def rightRepresentation : Representation ℂ H (HeckeAlgebra μG) where
  toFun h := (haarInversion μG).toLinearMap ∘ₗ
    leftRepresentation μG φ h ∘ₗ (haarInversion μG).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro f
    change haarInversion μG (leftRepresentation μG φ 1 (haarInversion μG f)) = f
    rw [map_one, Module.End.one_apply, haarInversion_involution]
  map_mul' h k := by
    apply LinearMap.ext
    intro f
    change haarInversion μG
        (leftRepresentation μG φ (h * k) (haarInversion μG f)) =
      haarInversion μG (leftRepresentation μG φ h
        (haarInversion μG (haarInversion μG
          (leftRepresentation μG φ k (haarInversion μG f)))))
    rw [haarInversion_involution, map_mul, Module.End.mul_apply]

/-- Right translation of Haar distributions includes the modular density factor. -/
theorem rightRepresentation_apply (h : H) (f : HeckeAlgebra μG) (x : G) :
    rightRepresentation μG φ h f x = haarScale ((φ h)⁻¹) * f (x * φ h) := by
  change haarScale x *
    (haarScale ((φ h)⁻¹ * x⁻¹) * f (((φ h)⁻¹ * x⁻¹)⁻¹)) = _
  simp only [map_mul, mul_inv_rev, inv_inv]
  calc
    _ = (haarScale x * haarScale x⁻¹) *
        (haarScale ((φ h)⁻¹) * f (x * φ h)) := by ring
    _ = _ := by rw [haarScale_mul_inverse, one_mul]

include hφ in
theorem rightRepresentation_isSmooth : IsSmooth (rightRepresentation μG φ) := by
  intro f
  obtain ⟨K, hK⟩ := leftRepresentation_isSmooth μG φ hφ (haarInversion μG f)
  change ∀ k : K, leftRepresentation μG φ (k : H) (haarInversion μG f) =
    haarInversion μG f at hK
  refine ⟨K, ?_⟩
  intro k
  change haarInversion μG
    (leftRepresentation μG φ (k : H) (haarInversion μG f)) = f
  rw [hK k, haarInversion_involution]

/-- The canonical right `H(H)`-action obtained using distribution inversion. -/
abbrev rightModule : NonUnitalModule (HeckeAlgebra μH)ᵐᵒᵖ (HeckeAlgebra μG) := by
  letI := leftModule μG μH φ hφ
  exact
    { smul := fun a f =>
        haarInversion μG (haarInversion μH a.unop • haarInversion μG f)
      smul_zero := fun a => by
        change haarInversion μG (haarInversion μH a.unop • haarInversion μG 0) = 0
        rw [map_zero, smul_zero, map_zero]
      smul_add := fun a f g => by
        change haarInversion μG (haarInversion μH a.unop • haarInversion μG (f + g)) =
          haarInversion μG (haarInversion μH a.unop • haarInversion μG f) +
            haarInversion μG (haarInversion μH a.unop • haarInversion μG g)
        rw [map_add, smul_add, map_add]
      zero_smul := fun f => by
        change haarInversion μG (haarInversion μH 0 • haarInversion μG f) = 0
        rw [map_zero, NonUnitalModule.zero_smul, map_zero]
      add_smul := fun a b f => by
        change haarInversion μG
            (haarInversion μH (a.unop + b.unop) • haarInversion μG f) =
          haarInversion μG (haarInversion μH a.unop • haarInversion μG f) +
            haarInversion μG (haarInversion μH b.unop • haarInversion μG f)
        rw [map_add, NonUnitalModule.add_smul, map_add]
      mul_smul := fun a b f => by
        change haarInversion μG
            (haarInversion μH (b.unop * a.unop) • haarInversion μG f) =
          haarInversion μG (haarInversion μH a.unop •
            haarInversion μG (haarInversion μG
              (haarInversion μH b.unop • haarInversion μG f)))
        rw [haarInversion_mul, mul_smul, haarInversion_involution] }

theorem rightModule_apply (a : HeckeAlgebra μH) (f : HeckeAlgebra μG) :
    (letI := rightModule μG μH φ hφ; op a • f) =
      (letI := leftModule μG μH φ hφ
       haarInversion μG (haarInversion μH a • haarInversion μG f)) := rfl

/-- The distribution inversion intertwines the left and right regular actions. -/
def inversionIntertwiner :
    (leftRepresentation μG φ).IntertwiningMap (rightRepresentation μG φ) where
  toLinearMap := (haarInversion μG).toLinearMap
  isIntertwining' h := by
    apply LinearMap.ext
    intro f
    change haarInversion μG (leftRepresentation μG φ h f) =
      haarInversion μG
        (leftRepresentation μG φ h (haarInversion μG (haarInversion μG f)))
    rw [haarInversion_involution]

/-- Exactly the action prescribed in III.2.1: integrate `r`, then apply the
anti-involution of the subgroup Hecke algebra to turn it into a right action. -/
theorem rightModule_eq_integrated (a : HeckeAlgebra μH) (f : HeckeAlgebra μG) :
    (letI := rightModule μG μH φ hφ; op a • f) =
      heckeAction μH (rightRepresentation μG φ)
        (rightRepresentation_isSmooth μG φ hφ) (haarInversion μH a) f := by
  have hi := integratedAction_intertwiner μH
    (leftRepresentation_isSmooth μG φ hφ) (rightRepresentation_isSmooth μG φ hφ)
    (inversionIntertwiner μG φ) (haarInversion μH a) (haarInversion μG f)
  change haarInversion μG
    (integratedAction μH (leftRepresentation μG φ)
      (leftRepresentation_isSmooth μG φ hφ) (haarInversion μH a)
      (haarInversion μG f)) = _
  change haarInversion μG
    (integratedAction μH (leftRepresentation μG φ)
      (leftRepresentation_isSmooth μG φ hφ) (haarInversion μH a)
      (haarInversion μG f)) =
    integratedAction μH (rightRepresentation μG φ)
      (rightRepresentation_isSmooth μG φ hφ) (haarInversion μH a)
      (haarInversion μG (haarInversion μG f)) at hi
  rw [haarInversion_involution] at hi
  exact hi

theorem rightModule_isNondegenerate :
    letI := rightModule μG μH φ hφ
    IsRightNondegenerate (HeckeAlgebra μH) (HeckeAlgebra μG) := by
  letI := leftModule μG μH φ hφ
  intro f
  obtain ⟨e, he⟩ := leftModule_isNondegenerate μG μH φ hφ (haarInversion μG f)
  refine ⟨⟨op (haarInversion μH (e : HeckeAlgebra μH)), ?_⟩, ?_⟩
  · change op (haarInversion μH (e : HeckeAlgebra μH) *
      haarInversion μH (e : HeckeAlgebra μH)) =
        op (haarInversion μH (e : HeckeAlgebra μH))
    rw [← haarInversion_mul, e.property.eq]
  · change haarInversion μG
      (haarInversion μH (haarInversion μH (e : HeckeAlgebra μH)) •
        haarInversion μG f) = f
    rw [haarInversion_involution, he, haarInversion_involution]

/-- The right subgroup action commutes with left multiplication by `H(G)`. -/
theorem regular_commutes_right :
    letI := NonUnitalModule.regular (HeckeAlgebra μG)
    letI := rightModule μG μH φ hφ
    ActionsCommute (HeckeAlgebra μG) (HeckeAlgebra μH) (HeckeAlgebra μG) := by
  letI := leftModule μG μH φ hφ
  intro c a f
  change c * haarInversion μG (haarInversion μH a • haarInversion μG f) =
    haarInversion μG (haarInversion μH a • haarInversion μG (c * f))
  apply (haarInversion μG).injective
  rw [haarInversion_mul, haarInversion_involution, haarInversion_involution,
    haarInversion_mul]
  exact (left_commutes_regular μG μH φ hφ
    (haarInversion μH a) (haarInversion μG c) (haarInversion μG f)).symm

/-- Both subgroup actions commute, proved on the original algebra using its local units. -/
theorem left_commutes_right :
    letI := leftModule μG μH φ hφ
    letI := rightModule μG μH φ hφ
    ActionsCommute (HeckeAlgebra μH) (HeckeAlgebra μH) (HeckeAlgebra μG) := by
  classical
  let L := NonUnitalModule.toEndHom (leftModule μG μH φ hφ)
  let R := NonUnitalModule.toEndHom (rightModule μG μH φ hφ)
  intro a b f
  change L a (R (op b) f) = R (op b) (L a f)
  obtain ⟨K, hK, _, _, hfix⟩ :=
    HeckeAlgebra.finiteFamilyLocalUnits G μG {f, R (op b) f} ⊤
  let e := HeckeAlgebra.normalizedIndicator μG K hK
  have hef : e * f = f := (hfix f (by simp)).1
  have heRf : e * R (op b) f = R (op b) f := (hfix _ (by simp)).1
  have hL (c d : HeckeAlgebra μG) : L a (c * d) = L a c * d :=
    left_commutes_regular μG μH φ hφ a d c
  have hR (c d : HeckeAlgebra μG) : c * R (op b) d = R (op b) (c * d) :=
    regular_commutes_right μG μH φ hφ c b d
  calc
    L a (R (op b) f) = L a (e * R (op b) f) := congrArg (L a) heRf.symm
    _ = L a e * R (op b) f := hL _ _
    _ = R (op b) (L a e * f) := hR _ _
    _ = R (op b) (L a (e * f)) := congrArg (R (op b)) (hL e f).symm
    _ = R (op b) (L a f) := by rw [hef]

/-- The nondegenerate `H(H)` bimodule specified in III.2.1. -/
def bimodule : NonUnitalBimoduleCat (HeckeAlgebra μH) (HeckeAlgebra μH) := by
  letI := leftModule μG μH φ hφ
  letI := rightModule μG μH φ hφ
  exact NonUnitalBimoduleCat.of _ _ (HeckeAlgebra μG)
    (left_commutes_right μG μH φ hφ)

theorem bimodule_isNondegenerate :
    letI := leftModule μG μH φ hφ
    letI := rightModule μG μH φ hφ
    IsNondegenerateBimodule (HeckeAlgebra μH) (HeckeAlgebra μH) (HeckeAlgebra μG) :=
  ⟨leftModule_isNondegenerate μG μH φ hφ, rightModule_isNondegenerate μG μH φ hφ⟩

/-- The `H(G)`–`H(H)` bimodule is nondegenerate on both sides. -/
theorem regular_right_nondegenerate :
    letI := NonUnitalModule.regular (HeckeAlgebra μG)
    letI := rightModule μG μH φ hφ
    IsNondegenerateBimodule (HeckeAlgebra μG) (HeckeAlgebra μH) (HeckeAlgebra μG) :=
  ⟨NondegenerateTensorFunctor.regular_isNondegenerate (isIdempotented μG),
    rightModule_isNondegenerate μG μH φ hφ⟩

/-- Renard's left induction `P`, on exactly the original nonunital tensor quotient. -/
def P : NondegenerateModuleCat.{uH, v} (HeckeAlgebra μH) ⥤
    NondegenerateModuleCat.{uG, max uG v} (HeckeAlgebra μG) := by
  letI := NonUnitalModule.regular (HeckeAlgebra μG)
  letI := rightModule μG μH φ hφ
  exact NondegenerateTensorFunctor.P (isIdempotented μG)
    (regular_commutes_right μG μH φ hφ) (regular_right_nondegenerate μG μH φ hφ)

/-- Renard's pseudo-forgetful functor, on the published nondegenerate Hom part. -/
def pseudoF : NondegenerateModuleCat.{uG, v} (HeckeAlgebra μG) ⥤
    NondegenerateModuleCat.{uH, max uG v} (HeckeAlgebra μH) := by
  letI := rightModule μG μH φ hφ
  exact RenardHomFunctors.pseudoF (regular_commutes_right μG μH φ hφ)
    (isIdempotented μH)

end Langlands.Hecke.Homomorphism
