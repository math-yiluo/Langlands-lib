import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Parabolic.InducedMapSurjectivity
import Langlands.Representation.Tensor.SmoothSubquotients
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! Actual injective and surjective maps and subquotient presentations for the
all-rank binary normalized product. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {a b : ℕ}

/-- The actual binary product map is injective when both factor maps are. -/
theorem binaryProductMap_injective
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y)
    (h₁ : letI := T.topology; Function.Injective (SmoothRep.hom f.1))
    (h₂ : letI := T.topology; Function.Injective (SmoothRep.hom f.2)) :
    letI := T.topology
    Function.Injective (SmoothRep.hom ((T.binaryNormalizedProductFunctor a b).map f)) := by
  let := T.topology
  by_cases ha : a = 0
  · intro x y hxy
    apply (T.binaryLeftZeroTensorEquiv ha X).injective
    simp only [Representation.Equiv.toLinearEquiv_apply,
      Representation.Equiv.coe_toIntertwiningMap]
    apply TensorProduct.map_injective_of_flat_flat
      (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap h₁ h₂
    simpa only [T.binaryLeftZeroTensorEquiv_naturality ha] using
      congrArg (T.binaryLeftZeroTensorEquiv ha Y) hxy
  · by_cases hb : b = 0
    · intro x y hxy
      apply (T.binaryRightZeroTensorEquiv hb X).injective
      simp only [Representation.Equiv.toLinearEquiv_apply,
        Representation.Equiv.coe_toIntertwiningMap]
      apply TensorProduct.map_injective_of_flat_flat
        (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap h₁ h₂
      simpa only [T.binaryRightZeroTensorEquiv_naturality hb] using
        congrArg (T.binaryRightZeroTensorEquiv hb Y) hxy
    · rw [T.binaryNormalizedProductFunctor_of_pos (Nat.pos_of_ne_zero ha)
        (Nat.pos_of_ne_zero hb)]
      rw [T.binaryPositiveProductFunctor_map]
      apply T.normalizedParabolicInducedMap_injective
      apply FiniteTensor.piTensorMap_injective
      intro i
      fin_cases i
      · exact h₁
      · exact h₂

/-- The actual binary product map is surjective when both factor maps are. -/
theorem binaryProductMap_surjective
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (f : letI := T.topology; X ⟶ Y)
    (h₁ : letI := T.topology; Function.Surjective (SmoothRep.hom f.1))
    (h₂ : letI := T.topology; Function.Surjective (SmoothRep.hom f.2)) :
    letI := T.topology
    Function.Surjective (SmoothRep.hom ((T.binaryNormalizedProductFunctor a b).map f)) := by
  let := T.topology
  by_cases ha : a = 0
  · intro y
    obtain ⟨x, hx⟩ := TensorProduct.map_surjective
      (g := (SmoothRep.hom f.1).toLinearMap)
      (g' := (SmoothRep.hom f.2).toLinearMap) h₁ h₂
      (T.binaryLeftZeroTensorEquiv ha Y y)
    refine ⟨(T.binaryLeftZeroTensorEquiv ha X).symm x, ?_⟩
    apply (T.binaryLeftZeroTensorEquiv ha Y).injective
    simp only [Representation.Equiv.toLinearEquiv_apply,
      Representation.Equiv.coe_toIntertwiningMap]
    rw [T.binaryLeftZeroTensorEquiv_naturality, Representation.Equiv.apply_symm_apply]
    exact hx
  · by_cases hb : b = 0
    · intro y
      obtain ⟨x, hx⟩ := TensorProduct.map_surjective
        (g := (SmoothRep.hom f.1).toLinearMap)
        (g' := (SmoothRep.hom f.2).toLinearMap) h₁ h₂
        (T.binaryRightZeroTensorEquiv hb Y y)
      refine ⟨(T.binaryRightZeroTensorEquiv hb X).symm x, ?_⟩
      apply (T.binaryRightZeroTensorEquiv hb Y).injective
      simp only [Representation.Equiv.toLinearEquiv_apply,
        Representation.Equiv.coe_toIntertwiningMap]
      rw [T.binaryRightZeroTensorEquiv_naturality, Representation.Equiv.apply_symm_apply]
      exact hx
    · rw [T.binaryNormalizedProductFunctor_of_pos (Nat.pos_of_ne_zero ha)
        (Nat.pos_of_ne_zero hb)]
      rw [T.binaryPositiveProductFunctor_map]
      apply Classification.normalizedProductMap_surjective F T
      intro i
      fin_cases i
      · exact h₁
      · exact h₂

/-- An explicit actual subquotient of the ambient product, presented by the
products of the supplied injective and surjective factor maps. The subspace is
the range of the product injection, and the kernel is that of the descended
product surjection. -/
def binaryProductSubquotientData
    {A₁ C₁ D₁ : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)}
    {A₂ C₂ D₂ : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (i₁ : letI := T.topology; C₁ ⟶ A₁)
    (i₂ : letI := T.topology; C₂ ⟶ A₂)
    (q₁ : letI := T.topology; C₁ ⟶ D₁)
    (q₂ : letI := T.topology; C₂ ⟶ D₂)
    (hi₁ : letI := T.topology; Function.Injective (SmoothRep.hom i₁))
    (hi₂ : letI := T.topology; Function.Injective (SmoothRep.hom i₂))
    (hq₁ : letI := T.topology; Function.Surjective (SmoothRep.hom q₁))
    (hq₂ : letI := T.topology; Function.Surjective (SmoothRep.hom q₂)) :
    letI := T.topology
    let A := (T.binaryNormalizedProductFunctor a b).obj (A₁, A₂)
    let D := (T.binaryNormalizedProductFunctor a b).obj (D₁, D₂)
    Σ S : Subrepresentation A.representation,
      Σ K : Subrepresentation (SmoothRep.subrepresentation A S).representation,
        D ≅ SmoothRep.subquotient A S K := by
  let := T.topology
  let P := T.binaryNormalizedProductFunctor a b
  let A := P.obj (A₁, A₂)
  let C := P.obj (C₁, C₂)
  let I : C ⟶ A := P.map (i₁, i₂)
  let Q : C ⟶ P.obj (D₁, D₂) := P.map (q₁, q₂)
  have hI : Function.Injective (SmoothRep.hom I) :=
    T.binaryProductMap_injective (a := a) (b := b)
      (X := (C₁, C₂)) (Y := (A₁, A₂)) (i₁, i₂) hi₁ hi₂
  have hQ : Function.Surjective (SmoothRep.hom Q) :=
    T.binaryProductMap_surjective (a := a) (b := b)
      (X := (C₁, C₂)) (Y := (D₁, D₂)) (q₁, q₂) hq₁ hq₂
  let S : Subrepresentation A.representation := (SmoothRep.hom I).range
  let j : C.representation.IntertwiningMap
      (SmoothRep.subrepresentation A S).representation :=
    { toLinearMap := (SmoothRep.hom I).toLinearMap.rangeRestrict
      isIntertwining' := fun g => by
        ext v
        exact Subtype.ext
          (Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom I) g v) }
  have hj : Function.Bijective j :=
    ⟨fun x y h => hI (congrArg Subtype.val h),
      fun ⟨_, x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩
  let e : C ≅ SmoothRep.subrepresentation A S := SmoothRep.mkIso (j.ofBijective hj)
  let q := SmoothRep.hom (e.inv ≫ Q)
  have hq : Function.Surjective q :=
    hQ.comp (SmoothRep.hom_hom_surjective e.symm)
  exact ⟨S, q.ker, (SmoothRep.subquotientPresentationIso S q hq).symm⟩

/-- Taking an actual subquotient in each original factor gives an actual
subquotient of their all-rank normalized binary product. -/
theorem binaryProduct_isSubquotient
    {A₁ D₁ : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)}
    {A₂ D₂ : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)}
    (h₁ : letI := T.topology; SmoothRep.IsSubquotient D₁ A₁)
    (h₂ : letI := T.topology; SmoothRep.IsSubquotient D₂ A₂) :
    letI := T.topology
    SmoothRep.IsSubquotient
      ((T.binaryNormalizedProductFunctor a b).obj (D₁, D₂))
      ((T.binaryNormalizedProductFunctor a b).obj (A₁, A₂)) := by
  let := T.topology
  obtain ⟨C₁, i₁, q₁, hi₁, hq₁⟩ := SmoothRep.isSubquotient_iff_exists.mp h₁
  obtain ⟨C₂, i₂, q₂, hi₂, hq₂⟩ := SmoothRep.isSubquotient_iff_exists.mp h₂
  let d := T.binaryProductSubquotientData i₁ i₂ q₁ q₂ hi₁ hi₂ hq₁ hq₂
  exact ⟨d.1, d.2.1, ⟨d.2.2⟩⟩

end Langlands.PadicField.TopologicalData
