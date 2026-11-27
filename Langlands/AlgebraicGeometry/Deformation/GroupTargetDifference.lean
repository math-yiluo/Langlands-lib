import Langlands.AlgebraicGeometry.Deformation.ElementaryLiftCech
import Langlands.AlgebraicGeometry.Deformation.SplitPointGroupLaw

/-! # Differences of lifts into a group scheme, and lifts agreeing on the residue fibre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Deformation.ElementaryMorphismLifts

open SquareZeroAffinePairs SplitInfinitesimalCoordinates ElementaryIdealCoefficients
open scoped SquareZeroAffinePairs ElementaryIdealCoefficients

variable {R : Type u} [CommRing R] [IsLocalRing R]

local notation "𝕜" => ResidueField R
local notation "S" => Spec (CommRingCat.of R)
local notation "K" => Spec (CommRingCat.of 𝕜)
local notation "r" => (specMap (IsLocalRing.residue R) : K ⟶ S)

namespace Target

/-- The target given by a group scheme over the local base, with its actual residue fibre and
the base-changed group law. -/
abbrev ofGroup (H : GroupScheme S) : Target R where
  X := H.X
  G := (GroupScheme.baseChange r).obj H
  i := pullback.fst H.X.hom r
  fibre := IsPullback.of_hasPullback _ _

variable (H : GroupScheme (Spec (CommRingCat.of R)))

theorem ofGroup_X : (ofGroup H).X = H.X := rfl

@[simp] theorem ofGroup_i : (ofGroup H).i = pullback.fst H.X.hom r := rfl

omit [IsLocalRing R] in
theorem mul_left_comp_hom {U : Over S} (p q : U ⟶ H.X) :
    (p * q).left = pullback.lift p.left q.left (p.w.trans q.w.symm) ≫ μ[H.X].left := by
  rw [CategoryTheory.Hom.mul_def, Over.comp_left, Over.lift_left]

private theorem lift_mul_hom {U : Scheme.{u}} {u : U ⟶ K} (a b : U ⟶ H.X.left)
    (ha : a ≫ H.X.hom = u ≫ r) (hb : b ≫ H.X.hom = u ≫ r) :
    (pullback.lift a b (ha.trans hb.symm) ≫ μ[H.X].left) ≫ H.X.hom = u ≫ r := by
  rw [Category.assoc, Over.w μ[H.X]]
  change pullback.lift a b _ ≫ pullback.fst H.X.hom H.X.hom ≫ H.X.hom = _
  rw [pullback.lift_fst_assoc, ha]

/-- The residue point of a product is the product of the residue points. -/
theorem ofGroup_fibrePoint_mul {U : Over K} (a b : U.left ⟶ H.X.left)
    (ha : a ≫ H.X.hom = U.hom ≫ r) (hb : b ≫ H.X.hom = U.hom ≫ r) :
    (ofGroup H).fibrePoint (pullback.lift a b (ha.trans hb.symm) ≫ μ[H.X].left)
        (lift_mul_hom H a b ha hb) =
      (ofGroup H).fibrePoint a ha * (ofGroup H).fibrePoint b hb := by
  apply fibrePoint_ext
  rw [fibrePoint_left_i, CategoryTheory.Hom.mul_def, Over.comp_left]
  change _ = (CartesianMonoidalCategory.lift ((ofGroup H).fibrePoint a ha) ((ofGroup H).fibrePoint b hb)).left ≫
    (Functor.LaxMonoidal.μ (Over.pullback r) H.X H.X ≫ (Over.pullback r).map μ[H.X]).left ≫
      pullback.fst H.X.hom r
  have e : ((Over.pullback r).map μ[H.X]).left ≫ pullback.fst H.X.hom r =
      pullback.fst (H.X ⊗ H.X).hom r ≫ μ[H.X].left := pullback.lift_fst _ _ _
  rw [Over.comp_left, Category.assoc, e, ← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, Category.assoc, Over.μ_pullback_left_fst_fst,
      ← Category.assoc, Over.lift_left]
    erw [pullback.lift_fst]
    exact ((ofGroup H).fibrePoint_left_i a ha).symm
  · rw [pullback.lift_snd, Category.assoc, Category.assoc, Over.μ_pullback_left_fst_snd,
      ← Category.assoc, Over.lift_left]
    erw [pullback.lift_snd]
    exact ((ofGroup H).fibrePoint_left_i b hb).symm


section Differences

variable (Z : Target R) (I : Ideal R) [hI : Fact (maximalIdeal R * I = ⊥)]
  (hproper : I ≤ maximalIdeal R) {C : Type u} [CommRing C] [Algebra R C]

local notation "D₀" => Fibre (R := R) C
local notation "J₀" => Extended I C
local notation "T" => TrivSqZeroExt D₀ J₀
local notation "ρ" => reduce (R := R) C
local notation "j₀" => specMap (Ideal.Quotient.mk J₀)
local notation "pC" => specMap (algebraMap R C)
local notation "hJ" => extended_squareZero I C hproper
local notation "hs" => reduce_smul I C

theorem reduce_comp_base : specMap ρ ≫ pC = (test (k := 𝕜) D₀).hom ≫ r := by
  rw [← specMap_comp]
  change specMap ((ρ).comp (algebraMap R C)) = specMap (algebraMap 𝕜 D₀) ≫ r
  rw [← specMap_comp]
  rfl

private theorem inclusion_test_hom' :
    specMap (inclusion (C := D₀) (M := J₀)) ≫ (test (k := 𝕜) D₀).hom =
      (test (k := 𝕜) T).hom :=
  Over.w (affineTestMap (TrivSqZeroExt.inlAlgHom 𝕜 D₀ J₀))

include hproper in
/-- The split test of two maps over the base lies over the residue field. -/
theorem splitPoint_over {W : Over S} (x y : Over.mk pC ⟶ W) (h : j₀ ≫ x.left = j₀ ≫ y.left) :
    splitPoint J₀ hJ ρ hs x.left y.left h ≫ W.hom = (test (k := 𝕜) T).hom ≫ r := by
  have hbase (a b : Spec (CommRingCat.of C) ⟶ S) (ha : a = pC) (hb : b = pC)
      (hab : j₀ ≫ a = j₀ ≫ b) :
      splitPoint J₀ hJ ρ hs a b hab = (test (k := 𝕜) T).hom ≫ r := by
    subst a b
    rw [splitPoint_same, reduce_comp_base, ← Category.assoc, inclusion_test_hom']
  rw [splitPoint_comp]
  exact hbase _ _ (Over.w x) (Over.w y) _

theorem splitPoint_congr {X : Scheme.{u}} {g g' h h' : Spec (CommRingCat.of C) ⟶ X}
    (hg : g = g') (hh : h = h') (he : j₀ ≫ g = j₀ ≫ h) :
    splitPoint J₀ hJ ρ hs g h he = splitPoint J₀ hJ ρ hs g' h' (hg ▸ hh ▸ he) := by
  subst hg hh
  rfl

/-- Maps agreeing on the actual residue fibre agree on every test over the residue field. -/
theorem comp_eq_of_fibre {W : Over S} {X : Scheme.{u}} (F₁ F₂ : W.left ⟶ X)
    (hF : pullback.fst W.hom r ≫ F₁ = pullback.fst W.hom r ≫ F₂) {U : Scheme.{u}}
    (u : U ⟶ W.left) (v : U ⟶ K) (huv : u ≫ W.hom = v ≫ r) : u ≫ F₁ = u ≫ F₂ := by
  rw [← pullback.lift_fst u v huv, Category.assoc, Category.assoc, hF]

omit hI in
theorem agree_comp {W : Over S} (x y : Over.mk pC ⟶ W) (h : j₀ ≫ x.left = j₀ ≫ y.left)
    (F : W ⟶ Z.X) : Z.Agree I (x ≫ F) (y ≫ F) := by
  change j₀ ≫ x.left ≫ F.left = j₀ ≫ y.left ≫ F.left
  rw [← Category.assoc, h, Category.assoc]

variable (c : PointChart Z.G.X Z.unitPoint)

/-- The translated difference of two composites depends only on the residue fibre of the
second map. -/
theorem translatedDifference_comp_eq {W : Over S} (F₁ F₂ : W ⟶ Z.X)
    (hF : pullback.fst W.hom r ≫ F₁.left = pullback.fst W.hom r ≫ F₂.left)
    (x y : Over.mk pC ⟶ W) (h : j₀ ≫ x.left = j₀ ≫ y.left) :
    Z.translatedDifference I hproper c (x ≫ F₁) (y ≫ F₁) (Z.agree_comp I x y h F₁) =
      Z.translatedDifference I hproper c (x ≫ F₂) (y ≫ F₂) (Z.agree_comp I x y h F₂) := by
  have hsp : Z.splitFibrePoint I hproper (x ≫ F₁) (y ≫ F₁) (Z.agree_comp I x y h F₁) =
      Z.splitFibrePoint I hproper (x ≫ F₂) (y ≫ F₂) (Z.agree_comp I x y h F₂) := by
    apply Z.fibrePoint_ext
    rw [splitFibrePoint, fibrePoint_left_i, splitFibrePoint, fibrePoint_left_i]
    change splitPoint J₀ hJ ρ hs (x.left ≫ F₁.left) (y.left ≫ F₁.left) _ =
      splitPoint J₀ hJ ρ hs (x.left ≫ F₂.left) (y.left ≫ F₂.left) _
    rw [← splitPoint_comp J₀ hJ ρ hs x.left y.left h F₁.left,
      ← splitPoint_comp J₀ hJ ρ hs x.left y.left h F₂.left]
    exact comp_eq_of_fibre F₁.left F₂.left hF _ (test (k := 𝕜) T).hom
      (splitPoint_over I hproper x y h)
  have hred (F : W ⟶ Z.X) : specMap ρ ≫ (x ≫ F).left = (specMap ρ ≫ x.left) ≫ F.left := by
    rw [Over.comp_left, Category.assoc]
  have hbase : (specMap ρ ≫ x.left) ≫ W.hom = (test (k := 𝕜) D₀).hom ≫ r := by
    rw [Category.assoc, Over.w x]
    exact reduce_comp_base
  have hce : Z.constantExtension I (x ≫ F₁) = Z.constantExtension I (x ≫ F₂) := by
    unfold constantExtension
    congr 1
    apply Z.fibrePoint_ext
    rw [reducePoint, fibrePoint_left_i, reducePoint, fibrePoint_left_i, hred, hred]
    exact comp_eq_of_fibre F₁.left F₂.left hF _ _ hbase
  apply Subtype.ext
  change (Z.constantExtension I (x ≫ F₁))⁻¹ * Z.splitFibrePoint I hproper (x ≫ F₁) (y ≫ F₁) _ =
    (Z.constantExtension I (x ≫ F₂))⁻¹ * Z.splitFibrePoint I hproper (x ≫ F₂) (y ≫ F₂) _
  rw [hce, hsp]

end Differences


section GroupLaw

variable (I : Ideal R) [hI : Fact (maximalIdeal R * I = ⊥)]
  (hproper : I ≤ maximalIdeal R) {C : Type u} [CommRing C] [Algebra R C]

local notation "D₀" => Fibre (R := R) C
local notation "J₀" => Extended I C
local notation "T" => TrivSqZeroExt D₀ J₀
local notation "ρ" => reduce (R := R) C
local notation "j₀" => specMap (Ideal.Quotient.mk J₀)
local notation "pC" => specMap (algebraMap R C)
local notation "hJ" => extended_squareZero I C hproper
local notation "hs" => reduce_smul I C

omit hI in
theorem agree_mul {x x' y y' : (ofGroup H).Points C} (h : (ofGroup H).Agree I x y)
    (h' : (ofGroup H).Agree I x' y') : (ofGroup H).Agree I (x * x') (y * y') := by
  let J : Over.mk (j₀ ≫ pC) ⟶ Over.mk pC := Over.homMk j₀ rfl
  have e₁ : J ≫ x = J ≫ y := Over.OverMorphism.ext h
  have e₂ : J ≫ x' = J ≫ y' := Over.OverMorphism.ext h'
  have e : J ≫ (x * x') = J ≫ (y * y') := by
    rw [MonObj.comp_mul, MonObj.comp_mul, e₁, e₂]
  exact congrArg (fun g ↦ g.left) e

theorem splitPoint_lift {g g' h h' : Spec (CommRingCat.of C) ⟶ H.X.left}
    (hg : g ≫ H.X.hom = g' ≫ H.X.hom) (hh : h ≫ H.X.hom = h' ≫ H.X.hom)
    (he : j₀ ≫ g = j₀ ≫ h) (he' : j₀ ≫ g' = j₀ ≫ h') :
    splitPoint J₀ hJ ρ hs (pullback.lift g g' hg) (pullback.lift h h' hh)
        (by apply pullback.hom_ext <;> simp [he, he']) =
      pullback.lift (splitPoint J₀ hJ ρ hs g h he) (splitPoint J₀ hJ ρ hs g' h' he') (by
        rw [splitPoint_comp, splitPoint_comp]
        exact splitPoint_congr I hproper hg hh _) := by
  apply pullback.hom_ext
  · rw [splitPoint_comp]
    exact (splitPoint_congr I hproper (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) _).trans
      (pullback.lift_fst _ _ _).symm
  · rw [splitPoint_comp]
    exact (splitPoint_congr I hproper (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) _).trans
      (pullback.lift_snd _ _ _).symm

theorem splitFibrePoint_mul (x x' y y' : (ofGroup H).Points C) (h : (ofGroup H).Agree I x y)
    (h' : (ofGroup H).Agree I x' y') :
    (ofGroup H).splitFibrePoint I hproper (x * x') (y * y') (agree_mul H I h h') =
      (ofGroup H).splitFibrePoint I hproper x y h * (ofGroup H).splitFibrePoint I hproper x' y' h' := by
  unfold splitFibrePoint
  rw [← ofGroup_fibrePoint_mul]
  apply fibrePoint_ext
  rw [fibrePoint_left_i, fibrePoint_left_i]
  rw [splitPoint_congr I hproper (mul_left_comp_hom H x x') (mul_left_comp_hom H y y')]
  rw [← splitPoint_comp J₀ hJ ρ hs _ _ _ μ[H.X].left]
  congr 1
  exact splitPoint_lift H I hproper _ _ h h'

theorem reducePoint_mul (x x' : (ofGroup H).Points C) :
    (ofGroup H).reducePoint (x * x') = (ofGroup H).reducePoint x * (ofGroup H).reducePoint x' := by
  unfold reducePoint
  rw [← ofGroup_fibrePoint_mul]
  apply fibrePoint_ext
  rw [fibrePoint_left_i, fibrePoint_left_i, mul_left_comp_hom, ← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp

theorem constantExtension_mul (x x' : (ofGroup H).Points C) :
    (ofGroup H).constantExtension I (x * x') =
      (ofGroup H).constantExtension I x * (ofGroup H).constantExtension I x' := by
  unfold constantExtension
  rw [reducePoint_mul, MonObj.comp_mul]

instance [IsCommMonObj H.X] : IsCommMonObj (ofGroup H).G.X :=
  Functor.isCommMonObj_obj (F := Over.pullback r) (M := H.X)

variable [IsCommMonObj H.X] (c : PointChart (ofGroup H).G.X (ofGroup H).unitPoint)

/-- On a commutative group target, the translated difference of products is the product of the
translated differences. -/
theorem translatedDifference_mul (x x' y y' : (ofGroup H).Points C) (h : (ofGroup H).Agree I x y)
    (h' : (ofGroup H).Agree I x' y') :
    (ofGroup H).translatedDifference I hproper c (x * x') (y * y') (agree_mul H I h h') =
      c.mul ((ofGroup H).translatedDifference I hproper c x y h)
        ((ofGroup H).translatedDifference I hproper c x' y' h') := by
  apply Subtype.ext
  change ((ofGroup H).constantExtension I (x * x'))⁻¹ *
      (ofGroup H).splitFibrePoint I hproper (x * x') (y * y') (agree_mul H I h h') =
    ((ofGroup H).constantExtension I x)⁻¹ * (ofGroup H).splitFibrePoint I hproper x y h *
      (((ofGroup H).constantExtension I x')⁻¹ * (ofGroup H).splitFibrePoint I hproper x' y' h')
  rw [constantExtension_mul, splitFibrePoint_mul, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

omit hI in
theorem agree_inv {x y : (ofGroup H).Points C} (h : (ofGroup H).Agree I x y) :
    (ofGroup H).Agree I x⁻¹ y⁻¹ := by
  let J : Over.mk (j₀ ≫ pC) ⟶ Over.mk pC := Over.homMk j₀ rfl
  have e₁ : J ≫ x = J ≫ y := Over.OverMorphism.ext h
  have e : J ≫ x⁻¹ = J ≫ y⁻¹ := by
    rw [GrpObj.comp_inv, GrpObj.comp_inv, e₁]
  exact congrArg (fun g ↦ g.left) e

end GroupLaw

namespace Coordinates

variable {Z : Target R} {I : Ideal R} [hI : Fact (maximalIdeal R * I = ⊥)] (b : Z.Coordinates I)
  {C : Type u} [CommRing C] [Algebra R C] [Module.Flat R C]

theorem equiv_apply' (v : b.chart.Points (D := Fibre (R := R) C) (M := Extended I C))
    (ij : Fin b.cotangentRank × Fin b.idealRank) :
    b.equiv v ij = (extendedBasis I b.idealBasis C).equivFun
      (b.chart.linearCoordinates v (b.cotangentBasis ij.1)) ij.2 := rfl

theorem difference_congr {x x' y y' : Z.Points C} (hx : x = x') (hy : y = y')
    (h : Z.Agree I x y) (h' : Z.Agree I x' y') : b.difference x y h = b.difference x' y' h' := by
  subst hx hy
  rfl

end Coordinates

section GroupCoordinates

variable {I : Ideal R} [hI : Fact (maximalIdeal R * I = ⊥)] [IsCommMonObj H.X]
  (b : (ofGroup H).Coordinates I) {C : Type u} [CommRing C] [Algebra R C] [Module.Flat R C]

/-- Difference coordinates of products of lifts into a commutative group scheme add. -/
theorem difference_mul (x x' y y' : (ofGroup H).Points C) (h : (ofGroup H).Agree I x y)
    (h' : (ofGroup H).Agree I x' y') :
    b.difference (x * x') (y * y') (agree_mul H I h h') =
      b.difference x y h + b.difference x' y' h' := by
  have hL : b.chart.linearCoordinates
      ((ofGroup H).translatedDifference I b.ideal_le b.chart (x * x') (y * y') (agree_mul H I h h')) =
      b.chart.linearCoordinates ((ofGroup H).translatedDifference I b.ideal_le b.chart x y h) +
        b.chart.linearCoordinates ((ofGroup H).translatedDifference I b.ideal_le b.chart x' y' h') := by
    rw [translatedDifference_mul H I b.ideal_le b.chart x x' y y' h h']
    exact PointChart.linearCoordinates_mul (G := (ofGroup H).G) b.chart _ _
  funext ij
  change b.equiv _ ij = b.equiv _ ij + b.equiv _ ij
  rw [Coordinates.equiv_apply', Coordinates.equiv_apply', Coordinates.equiv_apply', hL,
    LinearMap.add_apply, map_add, Pi.add_apply]

theorem difference_inv (x y : (ofGroup H).Points C) (h : (ofGroup H).Agree I x y) :
    b.difference x⁻¹ y⁻¹ (agree_inv H I h) = -b.difference x y h := by
  have e := difference_mul H b x x⁻¹ y y⁻¹ h (agree_inv H I h)
  rw [b.difference_congr (mul_inv_cancel x) (mul_inv_cancel y) _ rfl,
    Coordinates.difference_same] at e
  exact eq_neg_of_add_eq_zero_right e.symm

theorem difference_div (x x' y y' : (ofGroup H).Points C) (h : (ofGroup H).Agree I x y)
    (h' : (ofGroup H).Agree I x' y') :
    b.difference (x * x'⁻¹) (y * y'⁻¹) (agree_mul H I h (agree_inv H I h')) =
      b.difference x y h - b.difference x' y' h' := by
  rw [difference_mul H b x x'⁻¹ y y'⁻¹ h (agree_inv H I h'), difference_inv, sub_eq_add_neg]

end GroupCoordinates


end Target

end Langlands.AlgebraicGeometry.Deformation.ElementaryMorphismLifts
