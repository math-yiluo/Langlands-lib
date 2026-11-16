import Langlands.GroupScheme.Reductive.RankOneRingSquareRoots
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Localization.FractionRing

/-! # The rank-one relation with arbitrary second coordinate -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RingRootCell

namespace UnitSumExtension

variable {R : Type u} [CommRing R]

/-- The total quotient ring of a polynomial ring, also for rings with zero divisors. -/
abbrev Ring (R : Type u) [CommRing R] := FractionRing (Polynomial R)

/-- The constant-polynomial inclusion into the total quotient ring. -/
def inclusion : R →+* Ring R :=
  (algebraMap (Polynomial R) (Ring R)).comp Polynomial.C

theorem inclusion_injective : Function.Injective (inclusion (R := R)) :=
  (IsFractionRing.injective (Polynomial R) (Ring R)).comp Polynomial.C_injective

/-- After an injective extension, any element is a sum of two units, with an
additional unit of the form `1 + x*a`. -/
theorem exists_units (x w : R) :
    ∃ a b v : (Ring R)ˣ,
      inclusion w = (a : Ring R) + (b : Ring R) ∧
      (v : Ring R) = 1 + inclusion x * (a : Ring R) := by
  let f := algebraMap (Polynomial R) (Ring R)
  have ha : IsUnit (f Polynomial.X) :=
    IsLocalization.map_units (Ring R) ⟨_, Polynomial.X_mem_nonzeroDivisors⟩
  have hb : IsUnit (f (Polynomial.C w - Polynomial.X)) := by
    apply IsLocalization.map_units (M := nonZeroDivisors (Polynomial R)) (Ring R) ⟨_, ?_⟩
    apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 1
    simpa using ((isUnit_one : IsUnit (1 : R)).neg).mem_nonZeroDivisors
  have hv : IsUnit (f (1 + Polynomial.C x * Polynomial.X)) := by
    apply IsLocalization.map_units (M := nonZeroDivisors (Polynomial R)) (Ring R) ⟨_, ?_⟩
    apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 0
    simp
  refine ⟨ha.unit, hb.unit, hv.unit, ?_, ?_⟩
  · simp only [IsUnit.unit_spec, map_sub, inclusion, RingHom.comp_apply]
    ring
  · simp only [IsUnit.unit_spec, map_add, map_one, map_mul,
      inclusion, RingHom.comp_apply]
    rfl

end UnitSumExtension

/-- An affine test has an injective refinement where a chosen coordinate is a
sum of two units and the first intermediate denominator is a unit. -/
theorem exists_unitSum_test {S : Scheme.{u}} (Z : Over S) [IsAffine Z.left]
    (x w : Γ(Z.left, ⊤)) :
    ∃ (W : Over S) (j : W ⟶ Z), Function.Injective j.left.appTop ∧
      ∃ a b v : Γ(W.left, ⊤)ˣ,
        j.left.appTop w = (a : Γ(W.left, ⊤)) + (b : Γ(W.left, ⊤)) ∧
        (v : Γ(W.left, ⊤)) = 1 + j.left.appTop x * (a : Γ(W.left, ⊤)) := by
  let B := UnitSumExtension.Ring Γ(Z.left, ⊤)
  let f : Γ(Z.left, ⊤) ⟶ CommRingCat.of B :=
    CommRingCat.ofHom UnitSumExtension.inclusion
  let j₀ : Spec (CommRingCat.of B) ⟶ Z.left := Spec.map f ≫ Z.left.isoSpec.inv
  let W : Over S := Over.mk (j₀ ≫ Z.hom)
  let j : W ⟶ Z := Over.homMk j₀
  have hj : j.left.appTop = f ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv :=
    appTop_specMap_isoSpec_inv f
  let g := (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  obtain ⟨a, b, v, hw, hv⟩ := UnitSumExtension.exists_units x w
  refine ⟨W, j, ?_, Units.map g.toMonoidHom a, Units.map g.toMonoidHom b,
    Units.map g.toMonoidHom v, ?_, ?_⟩
  · rw [hj]
    exact ((ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv).1).comp
        UnitSumExtension.inclusion_injective
  · change j.left.appTop w = g (a : B) + g (b : B)
    rw [hj]
    change g (UnitSumExtension.inclusion w) = _
    simpa only [map_add] using congrArg g hw
  · simp only [Units.coe_map]
    rw [hj]
    change g (v : B) = 1 + g (UnitSumExtension.inclusion x) * g (a : B)
    simpa only [map_add, map_one, map_mul] using congrArg g hv

namespace WeylData

variable {k : Type u} [CommRing k] (D : WeylData k)
  {Z : Over (Spec (CommRingCat.of k))}

/-- Combine two applications of the unit-coordinate relation. -/
theorem relation_of_unitSum [IsAffine D.G.X.left]
    (X w : Γ(Z.left, ⊤)) (a b v u : Γ(Z.left, ⊤)ˣ)
    (hw : w = (a : Γ(Z.left, ⊤)) + (b : Γ(Z.left, ⊤)))
    (hv : (v : Γ(Z.left, ⊤)) = 1 + X * (a : Γ(Z.left, ⊤)))
    (hu : (u : Γ(Z.left, ⊤)) = 1 + X * w) :
    D.A X * D.B (pb Z D.cβ * w) =
      D.cellPt (pb Z D.cβ * ((↑u⁻¹ : Γ(Z.left, ⊤)) * w))
        (D.tH u) ((↑u⁻¹ : Γ(Z.left, ⊤)) * X) := by
  let q := u * v⁻¹
  have hq : (q : Γ(Z.left, ⊤)) =
      1 + ((↑v⁻¹ : Γ(Z.left, ⊤)) * X) * (b : Γ(Z.left, ⊤)) := by
    change (u : Γ(Z.left, ⊤)) * (↑v⁻¹ : Γ(Z.left, ⊤)) = _
    have hvi := Units.mul_inv v
    rw [hu, hw]
    linear_combination -(↑v⁻¹ : Γ(Z.left, ⊤)) * hv + hvi
  have h1 := D.relation_of_unit X a v hv
  have h2 := D.relation_of_unit ((↑v⁻¹ : Γ(Z.left, ⊤)) * X) b q hq
  have hqinv : q⁻¹ = v * u⁻¹ := by
    simp [q]
  have ht : D.tH v * D.tH q = D.tH u := by
    rw [← tH_mul]
    congr 1
    simp [q]
  have hcross : (u : Γ(Z.left, ⊤)) * (a : Γ(Z.left, ⊤)) +
      (b : Γ(Z.left, ⊤)) = (v : Γ(Z.left, ⊤)) * w := by
    rw [hu, hv, hw]
    ring
  have hy :
      pb Z D.cβ * ((↑v⁻¹ : Γ(Z.left, ⊤)) * (a : Γ(Z.left, ⊤))) +
        (↑(cu D.α (D.tH v))⁻¹ : Γ(Z.left, ⊤)) *
          (pb Z D.cβ * ((↑q⁻¹ : Γ(Z.left, ⊤)) * (b : Γ(Z.left, ⊤)))) =
      pb Z D.cβ * ((↑u⁻¹ : Γ(Z.left, ⊤)) * w) := by
    rw [cu_tH, hqinv]
    simp only [mul_inv_rev, Units.val_mul]
    have hui := Units.mul_inv u
    have hvi := Units.mul_inv v
    linear_combination
      -(pb Z D.cβ * (↑v⁻¹ : Γ(Z.left, ⊤)) * (a : Γ(Z.left, ⊤))) * hui +
      (pb Z D.cβ * (↑u⁻¹ : Γ(Z.left, ⊤)) *
        ((↑v⁻¹ : Γ(Z.left, ⊤)) * (b : Γ(Z.left, ⊤)) + w)) * hvi +
      (pb Z D.cβ * (↑u⁻¹ : Γ(Z.left, ⊤)) *
        (↑v⁻¹ : Γ(Z.left, ⊤))) * hcross
  have hx : (↑q⁻¹ : Γ(Z.left, ⊤)) * ((↑v⁻¹ : Γ(Z.left, ⊤)) * X) =
      (↑u⁻¹ : Γ(Z.left, ⊤)) * X := by
    rw [hqinv, Units.val_mul]
    calc
      _ = (↑u⁻¹ : Γ(Z.left, ⊤)) * X *
          ((v : Γ(Z.left, ⊤)) * (↑v⁻¹ : Γ(Z.left, ⊤))) := by ring
      _ = _ := by rw [Units.mul_inv, mul_one]
  calc
    D.A X * D.B (pb Z D.cβ * w) =
        (D.A X * D.B (pb Z D.cβ * (a : Γ(Z.left, ⊤)))) *
          D.B (pb Z D.cβ * (b : Γ(Z.left, ⊤))) := by
      rw [hw, mul_add, CellData.B_add, mul_assoc]
    _ = D.B (pb Z D.cβ * ((↑v⁻¹ : Γ(Z.left, ⊤)) * (a : Γ(Z.left, ⊤)))) *
        (D.I (D.tH v) *
          (D.A ((↑v⁻¹ : Γ(Z.left, ⊤)) * X) *
            D.B (pb Z D.cβ * (b : Γ(Z.left, ⊤))))) := by
      rw [h1, CellData.cellPt]
      simp only [mul_assoc]
    _ = _ := by
      rw [h2, CellData.I_mul_cellPt, CellData.B_mul_cellPt, hy, ht, hx]

/-- The rank-one relation on affine tests, with arbitrary second coordinate. -/
theorem relation_affine [IsAffine D.G.X.left] [IsAffine Z.left]
    (X w : Γ(Z.left, ⊤)) (u : Γ(Z.left, ⊤)ˣ)
    (hu : (u : Γ(Z.left, ⊤)) = 1 + X * w) :
    D.A X * D.B (pb Z D.cβ * w) =
      D.cellPt (pb Z D.cβ * ((↑u⁻¹ : Γ(Z.left, ⊤)) * w))
        (D.tH u) ((↑u⁻¹ : Γ(Z.left, ⊤)) * X) := by
  obtain ⟨W, j, hj, a, b, v, hw, hv⟩ := exists_unitSum_test Z X w
  let u' := Units.map j.left.appTop.hom.toMonoidHom u
  have hu' : (u' : Γ(W.left, ⊤)) = 1 + j.left.appTop X * j.left.appTop w := by
    change j.left.appTop (u : Γ(Z.left, ⊤)) = _
    rw [hu, map_add, map_one, map_mul]
  have h := D.relation_of_unitSum (j.left.appTop X) (j.left.appTop w)
    a b v u' hw hv hu'
  apply points_ext_of_injective_appTop j hj
  rw [MonObj.comp_mul, CellData.comp_A, CellData.comp_B, CellData.comp_cellPt,
    comp_tH]
  have hvu (v : Γ(Z.left, ⊤)ˣ) :
      (Units.map j.left.appTop.hom.toMonoidHom v : Γ(W.left, ⊤)) =
        j.left.appTop (v : Γ(Z.left, ⊤)) := rfl
  simpa only [u', map_mul, comp_pb, ← map_inv, hvu] using h

/-- The rank-one relation on every scheme test, without a unit hypothesis on the
second coordinate. -/
theorem relation [IsAffine D.G.X.left]
    (X w : Γ(Z.left, ⊤)) (u : Γ(Z.left, ⊤)ˣ)
    (hu : (u : Γ(Z.left, ⊤)) = 1 + X * w) :
    D.A X * D.B (pb Z D.cβ * w) =
      D.cellPt (pb Z D.cβ * ((↑u⁻¹ : Γ(Z.left, ⊤)) * w))
        (D.tH u) ((↑u⁻¹ : Γ(Z.left, ⊤)) * X) := by
  apply Over.OverMorphism.ext
  apply Z.left.affineCover.hom_ext
  intro i
  let V := SubgroupFunctor.coverObj Z.left.affineCover i
  let : IsAffine V.left := inferInstanceAs (IsAffine (Z.left.affineCover.X i))
  let j : V ⟶ Z := SubgroupFunctor.coverMap Z.left.affineCover i
  let u' := Units.map j.left.appTop.hom.toMonoidHom u
  have hv (v : Γ(Z.left, ⊤)ˣ) :
      (Units.map j.left.appTop.hom.toMonoidHom v : Γ(V.left, ⊤)) =
        j.left.appTop (v : Γ(Z.left, ⊤)) := rfl
  have hu' : (u' : Γ(V.left, ⊤)) = 1 + j.left.appTop X * j.left.appTop w := by
    change j.left.appTop (u : Γ(Z.left, ⊤)) = _
    rw [hu, map_add, map_one, map_mul]
  have h := D.relation_affine (j.left.appTop X) (j.left.appTop w) u' hu'
  have h' : j ≫ (D.A X * D.B (pb Z D.cβ * w)) =
      j ≫ D.cellPt (pb Z D.cβ * ((↑u⁻¹ : Γ(Z.left, ⊤)) * w))
        (D.tH u) ((↑u⁻¹ : Γ(Z.left, ⊤)) * X) := by
    rw [MonObj.comp_mul, CellData.comp_A, CellData.comp_B, CellData.comp_cellPt,
      comp_tH]
    simpa only [u', map_mul, comp_pb, ← map_inv, hv] using h
  exact congrArg (fun f => f.left) h'

end WeylData

end Langlands.GroupScheme.RingRootCell
