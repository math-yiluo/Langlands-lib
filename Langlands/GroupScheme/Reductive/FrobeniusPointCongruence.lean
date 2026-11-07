import Langlands.GroupScheme.Reductive.FrobeniusCovariantInvariants
import Langlands.GroupScheme.Reductive.SteinbergBigCellReduction

/-! # Characteristic-power congruence on actual arbitrary-test group points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Langlands.GroupScheme.FrobeniusPointCongruence

open AffineCoordinates MatrixRepresentation FrobeniusCovariantInvariants

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : ℕ) [ExpChar k p] (r : ℕ)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- Equality of characteristic powers of every actual coordinate value. -/
def Congruent (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X) : Prop :=
  ∀ a : algebra G, pointAlgebraHom G V g a ^ p ^ r =
    pointAlgebraHom G V h a ^ p ^ r

variable {G p r}

omit [ExpChar k p] in
theorem refl (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X) :
    Congruent G p r V g g := fun _ => rfl

omit [ExpChar k p] in
theorem symm {V : Over (Spec (CommRingCat.of k))} {g h : V ⟶ G.X}
    (hgh : Congruent G p r V g h) : Congruent G p r V h g :=
  fun a => (hgh a).symm

omit [ExpChar k p] in
theorem trans {V : Over (Spec (CommRingCat.of k))} {g h l : V ⟶ G.X}
    (hgh : Congruent G p r V g h) (hhl : Congruent G p r V h l) :
    Congruent G p r V g l := fun a => (hgh a).trans (hhl a)

/-- Multiplication preserves congruence in both arguments on the same test. -/
theorem mul {V : Over (Spec (CommRingCat.of k))} {g h a b : V ⟶ G.X}
    (hgh : Congruent G p r V g h) (hab : Congruent G p r V a b) :
    Congruent G p r V (g * a) (h * b) := by
  intro c
  rw [pointAlgebraHom_mul, pointAlgebraHom_mul]
  simp only [AlgHom.comp_apply]
  let F := characteristicPowerMap k p ((algΓ (CommRingCat.of k)).obj V).unop r
  change F (Algebra.TensorProduct.productMap _ _
    (AffineLinearEmbedding.comul (corepresentation G) c)) =
    F (Algebra.TensorProduct.productMap _ _
      (AffineLinearEmbedding.comul (corepresentation G) c))
  generalize (AffineLinearEmbedding.comul (corepresentation G) c) = z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      simpa only [Algebra.TensorProduct.productMap_apply_tmul, map_mul,
        F, characteristicPowerMap_apply] using
        congrArg₂ (· * ·) (hgh x) (hab y)
  | add z w hz hw => simp only [map_add, hz, hw]

omit [ExpChar k p] in
/-- Inversion also preserves characteristic-power congruence. -/
theorem inv {V : Over (Spec (CommRingCat.of k))} {g h : V ⟶ G.X}
    (hgh : Congruent G p r V g h) : Congruent G p r V g⁻¹ h⁻¹ := by
  intro a
  rw [← pointAlgebraHom_antipode, ← pointAlgebraHom_antipode]
  exact hgh (antipodeCoord G a)

variable (G)

theorem testCoordinates_one (V : Over (Spec (CommRingCat.of k)))
    (a : CharacterUnits.Coord G) :
    testCoordinates G V 1 a =
      algebraMap k ((algΓ (CommRingCat.of k)).obj V).unop (Lie.coordinateOrigin G a) := by
  change pointAlgebraHom G V 1 ((lieCoordinateAlgEquiv G).symm a) = _
  rw [pointAlgebraHom_one]
  change algebraMap k _ (AffineLinearEmbedding.counit (corepresentation G)
    ((lieCoordinateAlgEquiv G).symm a)) = _
  apply congrArg (algebraMap k _)
  have hc := LinearMap.congr_fun (corepresentation_counit G)
    ((lieCoordinateAlgEquiv G).symm a)
  have he := lieCoordinateAlgEquiv_counit G ((lieCoordinateAlgEquiv G).symm a)
  rw [AlgEquiv.apply_symm_apply] at he
  exact hc.trans he.symm

omit [ExpChar k p] in
/-- The two coordinate presentations detect exactly the same congruence. -/
theorem congruent_iff_testCoordinates {V : Over (Spec (CommRingCat.of k))}
    (g h : V ⟶ G.X) :
    Congruent G p r V g h ↔
      ∀ a : CharacterUnits.Coord G,
        testCoordinates G V g a ^ p ^ r = testCoordinates G V h a ^ p ^ r := by
  constructor
  · intro hgh a
    exact hgh ((lieCoordinateAlgEquiv G).symm a)
  · intro hgh a
    have he := hgh (lieCoordinateAlgEquiv G a)
    change pointAlgebraHom G V g
      ((lieCoordinateAlgEquiv G).symm (lieCoordinateAlgEquiv G a)) ^ p ^ r =
      pointAlgebraHom G V h
        ((lieCoordinateAlgEquiv G).symm (lieCoordinateAlgEquiv G a)) ^ p ^ r at he
    simpa only [AlgEquiv.symm_apply_apply] using he

/-- The intrinsic origin condition is congruence to the actual identity. -/
theorem isOriginTestPoint_iff_congruent_one
    (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X) :
    IsOriginTestPoint G p r V g ↔ Congruent G p r V g 1 := by
  rw [congruent_iff_testCoordinates]
  constructor
  · intro hg a
    rw [testCoordinates_one]
    have ha : Lie.coordinateOrigin G
        (a - algebraMap k (CharacterUnits.Coord G) (Lie.coordinateOrigin G a)) = 0 := by
      rw [map_sub, (Lie.coordinateOrigin G).commutes]
      exact sub_self _
    have hz := hg _ ha
    simp only [map_sub, (testCoordinates G V g).commutes] at hz
    apply sub_eq_zero.mp
    exact (map_sub (characteristicPowerMap k p
      ((algΓ (CommRingCat.of k)).obj V).unop r) _ _).symm.trans hz
  · intro hg a ha
    have he := hg a
    rw [testCoordinates_one, ha, map_zero,
      zero_pow (pow_ne_zero _ (expChar_ne_zero k p))] at he
    exact he

variable (p r)

/-- The actual Frobenius-origin points form a subgroup on every relative test. -/
def originTestSubgroup (V : Over (Spec (CommRingCat.of k))) : Subgroup (V ⟶ G.X) where
  carrier := {g | IsOriginTestPoint G p r V g}
  one_mem' := (isOriginTestPoint_iff_congruent_one G V 1).mpr (refl V 1)
  mul_mem' {a b} ha hb := by
    change IsOriginTestPoint G p r V a at ha
    change IsOriginTestPoint G p r V b at hb
    change IsOriginTestPoint G p r V (a * b)
    rw [isOriginTestPoint_iff_congruent_one] at ha hb ⊢
    simpa only [one_mul] using mul ha hb
  inv_mem' {a} ha := by
    change IsOriginTestPoint G p r V a at ha
    change IsOriginTestPoint G p r V a⁻¹
    rw [isOriginTestPoint_iff_congruent_one] at ha ⊢
    simpa only [inv_one] using inv ha

instance originTestSubgroup_normal (V : Over (Spec (CommRingCat.of k))) :
    (originTestSubgroup G p r V).Normal where
  conj_mem a ha g := by
    change IsOriginTestPoint G p r V (g * a * g⁻¹)
    apply (isOriginTestPoint_iff_congruent_one G V _).mpr
    have he := mul (mul (refl V g)
      ((isOriginTestPoint_iff_congruent_one G V a).mp ha)) (refl V g⁻¹)
    simpa only [mul_one, mul_inv_cancel] using he

variable {p r}

/-- Two congruent points differ by an intrinsic origin point. -/
theorem isOriginTestPoint_inv_mul
    {V : Over (Spec (CommRingCat.of k))} {g h : V ⟶ G.X}
    (hgh : Congruent G p r V g h) :
    IsOriginTestPoint G p r V (g⁻¹ * h) := by
  apply (isOriginTestPoint_iff_congruent_one G V _).mpr
  have he := mul (inv (refl V g)) (symm hgh)
  simpa only [inv_mul_cancel] using he

/-- Invariance under intrinsic origin points makes evaluation constant on
each actual characteristic-power congruence class. -/
theorem pointAlgebraHom_eq_of_congruent {b : algebra G}
    (hb : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      IsOriginTestPoint G p r V h →
        pointAlgebraHom G V (g * h) b = pointAlgebraHom G V g b)
    {V : Over (Spec (CommRingCat.of k))} {g h : V ⟶ G.X}
    (hgh : Congruent G p r V g h) :
    pointAlgebraHom G V g b = pointAlgebraHom G V h b := by
  have he := hb V g (g⁻¹ * h) (isOriginTestPoint_inv_mul G hgh)
  simpa only [mul_inv_cancel_left] using he.symm

end Langlands.GroupScheme.FrobeniusPointCongruence
