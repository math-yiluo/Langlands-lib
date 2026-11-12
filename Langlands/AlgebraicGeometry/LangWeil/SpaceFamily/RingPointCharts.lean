import Langlands.AlgebraicGeometry.LangWeil.SpaceFamily.FibreProductBase
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceUniformLangWeilStatement

/-!
# From scheme charts of the base to the algebraic-space estimate

The `κ`-valued points `RingPoints (ULift ℤ) X κ` of an algebraic space `X` are its sections
over `Spec κ`; by the Yoneda lemma they are the morphisms from the functor of points of
`Spec κ` over the terminal base to `X`, compatibly with morphisms of spaces
(`ringPointsEquiv`).

Given finitely many affine schemes `M i` locally of finite type over `ℤ` with morphisms
`t i : M i → B` such that every `κ`-point of `B` with `κ` finite comes from a `κ`-point of some
`M i`, the estimate `uniformLangWeil_fibreProduct` over each chart gives one constant for all
points of `B`: the sum of the chart constants plus one (`spaceUniformLangWeil_of_charts`).
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (ringTest)

namespace Langlands.AlgebraicGeometry.LangWeil.SpaceFamily

open Langlands.AlgebraicGeometry.AlgebraicSpace

/-- For any structure of `ULift ℤ`-algebra on a field `κ`, the test object `Spec κ` of ring points
is `Spec κ` over the terminal base. -/
def ringTestIso (κ : Type u) [Field κ] [Algebra (ULift.{u} ℤ) κ] :
    ringTest (ULift.{u} ℤ) κ ≅ toOver (Spec (CommRingCat.of κ)) :=
  Over.isoMk (Iso.refl _) (specULiftZIsTerminal.hom_ext _ _)

/-- The `κ`-points of an algebraic space over the terminal base, for any structure of
`ULift ℤ`-algebra on the field `κ`, are the morphisms from the functor of points of `Spec κ`. -/
def ringPointsEquiv (X : AlgebraicSpace S0.{u}) (κ : Type u) [Field κ]
    [Algebra (ULift.{u} ℤ) κ] :
    RingPoints (ULift.{u} ℤ) X κ ≃
      ((schemeYoneda S0).obj (toOver (Spec (CommRingCat.of κ))) ⟶ X.presheaf) :=
  uliftYonedaEquiv.{u + 1}.symm.trans
    (((schemeYoneda S0).mapIso (ringTestIso κ)).homCongr (Iso.refl X.presheaf))

/-- The comparison `ringPointsEquiv` is natural in morphisms of spaces. -/
theorem ringPointsEquiv_map {X Y : AlgebraicSpace S0.{u}} (f : X ⟶ Y) (κ : Type u) [Field κ]
    [Algebra (ULift.{u} ℤ) κ] (y : RingPoints (ULift.{u} ℤ) X κ) :
    ringPointsEquiv Y κ (RingPoints.map f y) = ringPointsEquiv X κ y ≫ hom f := by
  show (schemeYoneda S0).map (ringTestIso κ).inv ≫
      uliftYonedaEquiv.{u + 1}.symm ((hom f).app _ y) ≫ 𝟙 _ =
    ((schemeYoneda S0).map (ringTestIso κ).inv ≫ uliftYonedaEquiv.{u + 1}.symm y ≫ 𝟙 _) ≫ hom f
  have h := uliftYonedaEquiv_symm_comp.{u + 1}
    (show X.presheaf.obj (op (ringTest (ULift.{u} ℤ) κ)) from y) (hom f)
  simp only [Category.comp_id, Category.assoc]
  exact congrArg _ h.symm

/-- The `κ`-points of `Y` over a `κ`-point `x` of `B`, counted as ring points or as morphisms
from the functor of points of `Spec κ`. -/
theorem card_ringPoints_fibre {B Y : AlgebraicSpace S0.{u}} (f : Y ⟶ B) (κ : Type u) [Field κ]
    [Algebra (ULift.{u} ℤ) κ] (x : RingPoints (ULift.{u} ℤ) B κ) :
    Nat.card {y : RingPoints (ULift.{u} ℤ) Y κ // RingPoints.map f y = x} =
      Nat.card {y : (schemeYoneda S0).obj (toOver (Spec (CommRingCat.of κ))) ⟶ Y.presheaf //
        y ≫ hom f = ringPointsEquiv B κ x} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (ringPointsEquiv Y κ) fun y => ?_)
  rw [← ringPointsEquiv_map]
  exact (ringPointsEquiv B κ).apply_eq_iff_eq.symm

/-- **The algebraic-space estimate from scheme charts of the base.** Let `f : Y → B` satisfy the
hypotheses of `uniformLangWeil_fibreProduct`, and let `t i : M i → B` (`i < n`) be morphisms
from affine schemes locally of finite type over `ℤ` such that every point of `B` with values
in a finite field lifts to a point of some `M i`. Assuming the uniform Lang–Weil estimate and
the uniform upper bound in families of schemes, there is `C > 0` such that for every finite
field `κ` and every `κ`-point `x` of `B`, the number `N` of `κ`-points of `Y` over `x`
satisfies `|N - (#κ) ^ d| ≤ C (#κ) ^ (d - 1/2)`. -/
theorem spaceUniformLangWeil_of_charts (hFLW : FamilyLangWeilStatement.{u})
    (hFPU : FamilyPointUpperBoundStatement.{u}) {B Y : AlgebraicSpace S0.{u}} (f : Y ⟶ B)
    (d : ℕ) {U V : Over S0.{u}} (a : (schemeYoneda S0).obj U ⟶ Y.presheaf)
    (b : (schemeYoneda S0).obj V ⟶ B.presheaf) (φ : U ⟶ V)
    (hae : IsEtale a) (has : IsSurjective a) (hbe : IsEtale b)
    (hφ : SmoothOfRelativeDimension d φ.left) (hsq : a ≫ hom f = (schemeYoneda S0).map φ ≫ b)
    (hsep : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    (hsurj : IsSurjectiveMorphism f) (hconn : HasGeometricallyConnectedFibres f)
    {n : ℕ} (M : Fin n → Scheme.{u}) (t : ∀ i, (schemeYoneda S0).obj (toOver (M i)) ⟶ B.presheaf)
    (hM : ∀ i, IsAffine (M i)) (hMft : ∀ i, LocallyOfFiniteType (specULiftZIsTerminal.from (M i)))
    (hpts : ∀ (κ : Type u) [Field κ] [Finite κ]
      (x : (schemeYoneda S0).obj (toOver (Spec (CommRingCat.of κ))) ⟶ B.presheaf),
      ∃ i, ∃ m : Spec (CommRingCat.of κ) ⟶ M i, (schemeYoneda S0).map (toOverHom m) ≫ t i = x) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : Type u) [Field κ] [Finite κ] [Algebra (ULift.{u} ℤ) κ]
      (x : RingPoints (ULift.{u} ℤ) B κ),
      |(Nat.card {y : RingPoints (ULift.{u} ℤ) Y κ // RingPoints.map f y = x} : ℝ) -
          (Nat.card κ : ℝ) ^ d| ≤
        C * (Nat.card κ : ℝ) ^ ((d : ℝ) - 1 / 2) := by
  have hC : ∀ i, ∃ C : ℝ, 0 < C ∧ ∀ (κ : Type u) [Field κ] [Finite κ]
      (m : Spec (CommRingCat.of κ) ⟶ M i),
      |(Nat.card {y : (schemeYoneda S0).obj (toOver (Spec (CommRingCat.of κ))) ⟶ Y.presheaf //
          y ≫ hom f = (schemeYoneda S0).map (toOverHom m) ≫ t i} : ℝ) - (Nat.card κ : ℝ) ^ d| ≤
        C * (Nat.card κ : ℝ) ^ ((d : ℝ) - 1 / 2) := fun i => by
    have := hM i
    have := hMft i
    exact uniformLangWeil_fibreProduct hFLW hFPU f d a b φ hae has hbe hφ hsq hsep hqc hsurj
      hconn (M i) (t i)
  choose C hCpos hCb using hC
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => (hCpos i).le
  refine ⟨1 + ∑ i, C i, add_pos_of_pos_of_nonneg one_pos hsum, fun κ _ _ _ x => ?_⟩
  obtain ⟨i, m, hm⟩ := hpts κ (ringPointsEquiv B κ x)
  rw [card_ringPoints_fibre f κ x, ← hm]
  refine (hCb i κ m).trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · exact le_add_of_nonneg_of_le zero_le_one
      (Finset.single_le_sum (fun j _ => (hCpos j).le) (Finset.mem_univ i))
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

end Langlands.AlgebraicGeometry.LangWeil.SpaceFamily
