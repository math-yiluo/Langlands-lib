import Langlands.AlgebraicGeometry.Deformation.ElementaryIdealCoefficients
import Langlands.AlgebraicGeometry.SplitInfinitesimalCoordinates
import Langlands.AlgebraicGeometry.SmoothLifting.SquareZero

/-! # Ordinary morphism lifts with a group on the residue fibre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

namespace Langlands.AlgebraicGeometry.Deformation.ElementaryMorphismLifts

open SquareZeroAffinePairs SplitInfinitesimalCoordinates ElementaryIdealCoefficients
open scoped SquareZeroAffinePairs ElementaryIdealCoefficients

variable {R : Type u} [CommRing R] [IsLocalRing R]

local notation "𝕜" => ResidueField R
local notation "S" => Spec (CommRingCat.of R)
local notation "K" => Spec (CommRingCat.of 𝕜)
local notation "r" => specMap (residue R)

@[simp] theorem affineTestMap_left {A B : Type u} [CommRing A] [CommRing B]
    [Algebra 𝕜 A] [Algebra 𝕜 B] (f : A →ₐ[𝕜] B) :
    (affineTestMap f).left = specMap f.toRingHom := rfl

/-- The residue fibre of a target, presented by a group scheme. -/
structure Target (R : Type u) [CommRing R] [IsLocalRing R] where
  X : Over (Spec (CommRingCat.of R))
  G : GroupScheme (Spec (CommRingCat.of (ResidueField R)))
  i : G.X.left ⟶ X.left
  fibre : IsPullback i G.X.hom X.hom (specMap (residue R))

namespace Target

variable (Z : Target R)

instance : Mono Z.i := by
  have : IsClosedImmersion r := IsClosedImmersion.spec_of_surjective _ residue_surjective
  exact Z.fibre.mono_fst_of_mono

/-- A map to the original target over the residue field is a point of the residue group. -/
def fibrePoint {U : Over K} (x : U.left ⟶ Z.X.left) (hx : x ≫ Z.X.hom = U.hom ≫ r) :
    U ⟶ Z.G.X := Over.homMk (Z.fibre.lift x U.hom hx) (Z.fibre.lift_snd _ _ _)

@[reassoc (attr := simp)] theorem fibrePoint_left_i {U : Over K} (x : U.left ⟶ Z.X.left)
    (hx : x ≫ Z.X.hom = U.hom ≫ r) : (Z.fibrePoint x hx).left ≫ Z.i = x :=
  Z.fibre.lift_fst _ _ _

theorem fibrePoint_ext {U : Over K} {x y : U ⟶ Z.G.X}
    (h : x.left ≫ Z.i = y.left ≫ Z.i) : x = y :=
  Over.OverMorphism.ext ((cancel_mono Z.i).mp h)

variable (I : Ideal R) [hI : Fact (maximalIdeal R * I = ⊥)] (hproper : I ≤ maximalIdeal R)
variable {C : Type u} [CommRing C] [Algebra R C]

local notation "D₀" => Fibre (R := R) C
local notation "J₀" => Extended I C
local notation "T" => TrivSqZeroExt D₀ J₀
local notation "ρ" => reduce (R := R) C
local notation "j₀" => specMap (Ideal.Quotient.mk J₀)
local notation "pC" => specMap (algebraMap R C)
local notation "hJ" => extended_squareZero I C hproper
local notation "hs" => reduce_smul I C

/-- A point of the target over an affine test with its original base map. -/
abbrev Points (C : Type u) [CommRing C] [Algebra R C] := Over.mk (specMap (algebraMap R C)) ⟶ Z.X

/-- The condition that two ordinary maps have equal reduction modulo the extended ideal. -/
abbrev Agree (x y : Z.Points C) : Prop := j₀ ≫ x.left = j₀ ≫ y.left

private theorem reduce_base : specMap ρ ≫ pC = (test (k := 𝕜) D₀).hom ≫ r := by
  rw [← specMap_comp]
  change specMap ((ρ).comp (algebraMap R C)) = specMap (algebraMap 𝕜 D₀) ≫ r
  rw [← specMap_comp]
  rfl

/-- The residue point of a lift. -/
def reducePoint (x : Z.Points C) : test (k := 𝕜) D₀ ⟶ Z.G.X :=
  Z.fibrePoint (U := test (k := 𝕜) D₀) (specMap ρ ≫ x.left) (by
    rw [Category.assoc, Over.w x]
    exact reduce_base)

private theorem inclusion_test_hom :
    specMap (inclusion (C := D₀) (M := J₀)) ≫ (test (k := 𝕜) D₀).hom =
      (test (k := 𝕜) T).hom :=
  Over.w (affineTestMap (TrivSqZeroExt.inlAlgHom 𝕜 D₀ J₀))

private theorem splitPoint_base (x y : Z.Points C) (h : Z.Agree I x y) :
    splitPoint J₀ hJ ρ hs x.left y.left h ≫ Z.X.hom = (test (k := 𝕜) T).hom ≫ r := by
  have hbase (a b : Spec (CommRingCat.of C) ⟶ S) (ha : a = pC) (hb : b = pC)
      (hab : j₀ ≫ a = j₀ ≫ b) :
      splitPoint J₀ hJ ρ hs a b hab = (test (k := 𝕜) T).hom ≫ r := by
    subst a b
    rw [splitPoint_same, reduce_base, ← Category.assoc, inclusion_test_hom]
  rw [splitPoint_comp]
  exact hbase _ _ (Over.w x) (Over.w y) _

/-- The difference test as a point of the residue fibre at the common reduced map. -/
def splitFibrePoint (x y : Z.Points C) (h : Z.Agree I x y) : test (k := 𝕜) T ⟶ Z.G.X :=
  Z.fibrePoint (splitPoint J₀ hJ ρ hs x.left y.left h) (Z.splitPoint_base I hproper x y h)

private theorem splitFibrePoint_reduce (x y : Z.Points C) (h : Z.Agree I x y) :
    affineTestMap (TrivSqZeroExt.fstHom 𝕜 D₀ J₀) ≫ Z.splitFibrePoint I hproper x y h =
      Z.reducePoint x := by
  apply Z.fibrePoint_ext
  simpa only [Over.comp_left, affineTestMap_left, Category.assoc, splitFibrePoint, reducePoint,
    fibrePoint_left_i] using!
    (projection_splitPoint J₀ hJ ρ hs x.left y.left h)

/-- A map from the split test obtained by extending the residue point with zero coefficient. -/
def constantExtension (x : Z.Points C) : test (k := 𝕜) T ⟶ Z.G.X :=
  affineTestMap (TrivSqZeroExt.inlAlgHom 𝕜 D₀ J₀) ≫ Z.reducePoint x

private theorem constantExtension_reduce (x : Z.Points C) :
    affineTestMap (TrivSqZeroExt.fstHom 𝕜 D₀ J₀) ≫ Z.constantExtension I x = Z.reducePoint x := by
  rw [constantExtension, ← Category.assoc, ← affineTestMap_comp]
  change affineTestMap (AlgHom.id 𝕜 D₀) ≫ Z.reducePoint x = _
  simp [affineTestMap]

/-- The identity of the residue group as a rational point of the affine base. -/
def unitPoint : test (k := 𝕜) 𝕜 ⟶ Z.G.X := 1

variable (c : PointChart Z.G.X Z.unitPoint)

/-- Translation of the infinitesimal point by the inverse of its constant term. -/
def translatedDifference (x y : Z.Points C) (h : Z.Agree I x y) : c.Points (D := D₀) (M := J₀) :=
  ⟨(Z.constantExtension I x)⁻¹ * Z.splitFibrePoint I hproper x y h, by
    unfold unitPoint
    rw [MonObj.comp_mul, GrpObj.comp_inv, constantExtension_reduce, splitFibrePoint_reduce,
      inv_mul_cancel, MonObj.comp_one]⟩

private theorem splitFibrePoint_same (x : Z.Points C) :
    Z.splitFibrePoint I hproper x x rfl = Z.constantExtension I x := by
  apply Z.fibrePoint_ext
  simpa only [Over.comp_left, affineTestMap_left, Category.assoc, splitFibrePoint, constantExtension, reducePoint,
    fibrePoint_left_i] using! (splitPoint_same J₀ hJ ρ hs x.left)

@[simp] theorem translatedDifference_same (x : Z.Points C) :
    Z.translatedDifference I hproper c x x rfl = c.constant := by
  apply Subtype.ext
  change (Z.constantExtension I x)⁻¹ * Z.splitFibrePoint I hproper x x rfl =
    (c.constant (D := D₀) (M := J₀)).val
  rw [c.constant_val, splitFibrePoint_same, inv_mul_cancel]
  simp [unitPoint, MonObj.comp_one]

/-- Change an ordinary lift by a point at the identity of the split residue test. -/
def correct (x : Z.Points C) (d : c.Points (D := D₀) (M := J₀)) : Z.Points C := by
  let v := Z.constantExtension I x * d.val
  have hv₀ : affineTestMap (TrivSqZeroExt.fstHom 𝕜 D₀ J₀) ≫ v = Z.reducePoint x := by
    rw [MonObj.comp_mul, constantExtension_reduce, d.property]
    simp [unitPoint, MonObj.comp_one]
  have hv : specMap ρ ≫ x.left = specMap projection ≫ (v.left ≫ Z.i) := by
    have h := congrArg (fun a : test (k := 𝕜) D₀ ⟶ Z.G.X ↦ a.left ≫ Z.i) hv₀.symm
    simpa only [Over.comp_left, affineTestMap_left, Category.assoc, reducePoint, fibrePoint_left_i] using! h
  refine Over.homMk (update J₀ hJ ρ Ideal.Quotient.mk_surjective hs x.left (v.left ≫ Z.i) hv) ?_
  change update _ _ _ _ _ _ _ _ ≫ Z.X.hom = pC
  rw [update_comp]
  have hb : (v.left ≫ Z.i) ≫ Z.X.hom = splitPoint J₀ hJ ρ hs pC pC rfl := by
    rw [Category.assoc, Z.fibre.w, Over.w_assoc, splitPoint_same, reduce_base,
      ← Category.assoc, inclusion_test_hom]
  have hu (a : Spec (CommRingCat.of C) ⟶ S) (b : Spec (CommRingCat.of T) ⟶ S)
      (ha : a = pC) (hb : b = splitPoint J₀ hJ ρ hs pC pC rfl)
      (hab : specMap ρ ≫ a = specMap projection ≫ b) :
      update J₀ hJ ρ Ideal.Quotient.mk_surjective hs a b hab = pC := by
    subst a b
    exact update_splitPoint J₀ hJ ρ Ideal.Quotient.mk_surjective hs pC pC rfl
  exact hu _ _ (Over.w x) hb _

@[simp] theorem correct_agree (x : Z.Points C) (d : c.Points (D := D₀) (M := J₀)) :
    Z.Agree I x (Z.correct I hproper c x d) :=
  (reduction_update J₀ hJ ρ Ideal.Quotient.mk_surjective hs _ _ _).symm

@[simp] theorem translatedDifference_correct (x : Z.Points C) (d : c.Points (D := D₀) (M := J₀)) :
    Z.translatedDifference I hproper c x (Z.correct I hproper c x d)
      (Z.correct_agree I hproper c x d) = d := by
  have he : Z.splitFibrePoint I hproper x (Z.correct I hproper c x d)
      (Z.correct_agree I hproper c x d) =
      Z.constantExtension I x * d.val := by
    apply Z.fibrePoint_ext
    rw [splitFibrePoint, Z.fibrePoint_left_i]
    exact splitPoint_update J₀ hJ ρ Ideal.Quotient.mk_surjective hs _ _ _
  apply Subtype.ext
  change (Z.constantExtension I x)⁻¹ * Z.splitFibrePoint I hproper x
    (Z.correct I hproper c x d) (Z.correct_agree I hproper c x d) = d.val
  rw [he, inv_mul_cancel_left]

@[simp] theorem correct_translatedDifference (x y : Z.Points C) (h : Z.Agree I x y) :
    Z.correct I hproper c x (Z.translatedDifference I hproper c x y h) = y := by
  have he : Z.constantExtension I x * (Z.translatedDifference I hproper c x y h).val =
      Z.splitFibrePoint I hproper x y h := by
    change _ * (_⁻¹ * _) = _
    rw [mul_inv_cancel_left]
  apply Over.OverMorphism.ext
  change update J₀ hJ ρ Ideal.Quotient.mk_surjective hs x.left
    ((Z.constantExtension I x * _).left ≫ Z.i) _ = _
  simp only [he, splitFibrePoint, Z.fibrePoint_left_i]
  exact update_splitPoint J₀ hJ ρ Ideal.Quotient.mk_surjective hs _ _ h

include hproper in
/-- Smoothness supplies an ordinary lift on every affine test. -/
theorem exists_lift [Smooth Z.X.hom] (x₀ : Spec (CommRingCat.of (C ⧸ J₀)) ⟶ Z.X.left)
    (hx₀ : x₀ ≫ Z.X.hom = j₀ ≫ pC) : ∃ x : Z.Points C, j₀ ≫ x.left = x₀ := by
  have hnil : SmoothLifting.SqZero (RingHom.ker (Ideal.Quotient.mk J₀)) := by
    rw [Ideal.mk_ker]
    intro a ha b hb
    exact Ideal.mem_bot.mp (hJ ▸ (pow_two J₀).symm ▸ Ideal.mul_mem_mul ha hb)
  obtain ⟨x, hx, hxp⟩ := SmoothLifting.exists_lift_sqZero (CommRingCat.ofHom (Ideal.Quotient.mk J₀))
    Ideal.Quotient.mk_surjective hnil x₀ pC hx₀
  exact ⟨Over.homMk x hxp, hx⟩

include hproper in
omit hI in
private theorem reducePoint_eq (x y : Z.Points C) (h : Z.Agree I x y) :
    Z.reducePoint x = Z.reducePoint y := by
  apply Z.fibrePoint_ext
  rw [reducePoint, reducePoint, fibrePoint_left_i, fibrePoint_left_i]
  let φ := Ideal.Quotient.factor (Ideal.map_mono (f := algebraMap R C) hproper)
  have hφ : (ρ) = φ.comp (Ideal.Quotient.mk J₀) := rfl
  rw [hφ, specMap_comp_assoc, specMap_comp_assoc, show j₀ ≫ x.left = j₀ ≫ y.left from h]

section Naturality

variable {C' : Type u} [CommRing C'] [Algebra R C'] (f : C →ₐ[R] C')

/-- Restriction of an ordinary lift to another affine test. -/
def restrict (x : Z.Points C) : Z.Points C' := Over.homMk (specMap f.toRingHom ≫ x.left) (by
  rw [Category.assoc, Over.w x]
  change specMap f.toRingHom ≫ pC = specMap (algebraMap R C')
  rw [← specMap_comp]
  exact congrArg specMap f.comp_algebraMap)

@[simp] theorem restrict_left (x : Z.Points C) :
    (Z.restrict f x).left = specMap f.toRingHom ≫ x.left := rfl

omit hI in
/-- Restricting along an algebra map preserves agreement on the quotient. -/
theorem restrict_agree (x y : Z.Points C) (h : Z.Agree I x y) :
    Z.Agree I (Z.restrict f x) (Z.restrict f y) :=
  map_reduced_agree J₀ (Extended I C') f.toRingHom (map_extended_le I f) _ _ h

private theorem reducePoint_restrict (x : Z.Points C) :
    Z.reducePoint (Z.restrict f x) = affineTestMap (fibreMap f) ≫ Z.reducePoint x := by
  apply Z.fibrePoint_ext
  simp only [Over.comp_left, affineTestMap_left, Category.assoc, reducePoint, fibrePoint_left_i,
    restrict_left]
  rw [← specMap_comp_assoc, ← specMap_comp_assoc]
  rfl

private theorem constantExtension_restrict (x : Z.Points C) :
    Z.constantExtension I (Z.restrict f x) =
      affineTestMap (splitAlgMap (fibreMap f) (extendedMap I f)) ≫ Z.constantExtension I x := by
  rw [constantExtension, reducePoint_restrict, ← Category.assoc, ← affineTestMap_comp, constantExtension,
    ← Category.assoc, ← affineTestMap_comp, splitAlgMap_comp_inl]

/-- The translated difference commutes with restriction between affine tests. -/
theorem translatedDifference_restrict (x y : Z.Points C) (h : Z.Agree I x y) :
    Z.translatedDifference I hproper c (Z.restrict f x) (Z.restrict f y) (Z.restrict_agree I f x y h) =
      c.mapPoints (fibreMap f) (extendedMap I f) (Z.translatedDifference I hproper c x y h) := by
  have he : Z.splitFibrePoint I hproper (Z.restrict f x) (Z.restrict f y)
      (Z.restrict_agree I f x y h) =
      affineTestMap (splitAlgMap (fibreMap f) (extendedMap I f)) ≫ Z.splitFibrePoint I hproper x y h := by
    apply Z.fibrePoint_ext
    simpa only [Over.comp_left, Category.assoc, affineTestMap_left, splitFibrePoint,
      fibrePoint_left_i, restrict_left] using!
      (splitPoint_natural J₀ hJ ρ Ideal.Quotient.mk_surjective hs (Extended I C')
        (extended_squareZero I C' hproper) (reduce (R := R) C') (reduce_smul I C') f.toRingHom
        (map_extended_le I f) (fibreMap f).toRingHom rfl x.left y.left h).symm
  apply Subtype.ext
  change (Z.constantExtension I (Z.restrict f x))⁻¹ * Z.splitFibrePoint I hproper
    (Z.restrict f x) (Z.restrict f y) (Z.restrict_agree I f x y h) =
    affineTestMap (splitAlgMap (fibreMap f) (extendedMap I f)) ≫
      ((Z.constantExtension I x)⁻¹ * Z.splitFibrePoint I hproper x y h)
  rw [MonObj.comp_mul, GrpObj.comp_inv, constantExtension_restrict, he]

end Naturality

section Cocycle

local notation "T₃" => TrivSqZeroExt D₀ (J₀ × J₀)
local notation "firstCoeff" => LinearMap.fst D₀ J₀ J₀
local notation "secondCoeff" => LinearMap.snd D₀ J₀ J₀
local notation "sumCoeff" => (LinearMap.fst D₀ J₀ J₀ + LinearMap.snd D₀ J₀ J₀)

private abbrev face (coeff : (J₀ × J₀) →ₗ[D₀] J₀) : test (k := 𝕜) T ⟶ test (k := 𝕜) T₃ :=
  affineTestMap (splitAlgMap (AlgHom.id 𝕜 D₀) coeff)

private theorem exists_fibreTriple (x y z : Z.Points C) (hxy : Z.Agree I x y)
    (hyz : Z.Agree I y z) :
    ∃ v : test (k := 𝕜) T₃ ⟶ Z.G.X,
      face (I := I) firstCoeff ≫ v = Z.splitFibrePoint I hproper x y hxy ∧
      face (I := I) secondCoeff ≫ v = Z.splitFibrePoint I hproper y z hyz ∧
      face (I := I) sumCoeff ≫ v =
        Z.splitFibrePoint I hproper x z (hxy.trans hyz) := by
  obtain ⟨w, h₁, h₂, h₃⟩ := exists_splitTriple J₀ hJ ρ hs (reduce_extended I C hproper)
    x.left y.left z.left hxy hyz
  have hw : w ≫ Z.X.hom = (test (k := 𝕜) T₃).hom ≫ r := by
    apply (pushout_split D₀ J₀).hom_ext
    · rw [← Category.assoc, h₁, splitPoint_base Z I hproper, ← Category.assoc]
      exact congrArg (· ≫ r) (Over.w (face (I := I) firstCoeff)).symm
    · rw [← Category.assoc, h₂, splitPoint_base Z I hproper, ← Category.assoc]
      exact congrArg (· ≫ r) (Over.w (face (I := I) secondCoeff)).symm
  let v := Z.fibrePoint (U := test (k := 𝕜) T₃) w hw
  refine ⟨v, ?_, ?_, ?_⟩
  all_goals
    apply Z.fibrePoint_ext
    dsimp only [v]
    simp only [Over.comp_left, Category.assoc, fibrePoint_left_i, splitFibrePoint, affineTestMap_left]
  · exact h₁
  · exact h₂
  · exact h₃

/-- The three differences on one affine test satisfy the Čech cocycle equation. -/
theorem linearDifference_add (x y z : Z.Points C) (hxy : Z.Agree I x y)
    (hyz : Z.Agree I y z) (t : c.Cotangent) :
    c.linearCoordinates (Z.translatedDifference I hproper c x z ((hxy.trans hyz))) t =
      c.linearCoordinates (Z.translatedDifference I hproper c x y hxy) t +
      c.linearCoordinates (Z.translatedDifference I hproper c y z hyz) t := by
  obtain ⟨v, h₁, h₂, h₃⟩ := Z.exists_fibreTriple I hproper x y z hxy hyz
  let π := affineTestMap (TrivSqZeroExt.fstHom 𝕜 D₀ (J₀ × J₀))
  let j := affineTestMap (TrivSqZeroExt.inlAlgHom 𝕜 D₀ (J₀ × J₀))
  let b := j ≫ Z.reducePoint x
  have hπ : π ≫ v = Z.reducePoint x := by
    have h₀ : π = affineTestMap (TrivSqZeroExt.fstHom 𝕜 D₀ J₀) ≫ face (I := I) firstCoeff := by
      rw [← affineTestMap_comp]
      rfl
    rw [h₀, Category.assoc, h₁, splitFibrePoint_reduce]
  have hb : π ≫ b = Z.reducePoint x := by
    dsimp only [b, j, π]
    rw [← Category.assoc, ← affineTestMap_comp]
    change affineTestMap (AlgHom.id 𝕜 D₀) ≫ Z.reducePoint x = _
    simp [affineTestMap]
  let q : c.Points (D := D₀) (M := J₀ × J₀) := ⟨b⁻¹ * v, by
    change π ≫ _ = _
    rw [MonObj.comp_mul, GrpObj.comp_inv, hb, hπ, inv_mul_cancel, unitPoint, MonObj.comp_one]⟩
  have hbface (l : (J₀ × J₀) →ₗ[D₀] J₀) :
      face (I := I) l ≫ b = Z.constantExtension I x := by
    dsimp only [b, j, face, constantExtension]
    rw [← Category.assoc, ← affineTestMap_comp, splitAlgMap_comp_inl]
    rfl
  have face_eq (l : (J₀ × J₀) →ₗ[D₀] J₀) (x' y' : Z.Points C) (hh : Z.Agree I x' y')
      (hx' : Z.reducePoint x = Z.reducePoint x')
      (hv : face (I := I) l ≫ v = Z.splitFibrePoint I hproper x' y' hh) :
      c.mapPoints (AlgHom.id 𝕜 D₀) l q = Z.translatedDifference I hproper c x' y' hh := by
    apply Subtype.ext
    change face (I := I) l ≫ (b⁻¹ * v) =
      (Z.constantExtension I x')⁻¹ * Z.splitFibrePoint I hproper x' y' hh
    rw [MonObj.comp_mul, GrpObj.comp_inv, hbface, hv]
    unfold constantExtension
    rw [hx']
  have eq₁ := c.linearCoordinates_mapPoints (AlgHom.id 𝕜 D₀) firstCoeff q t
  have eq₂ := c.linearCoordinates_mapPoints (AlgHom.id 𝕜 D₀) secondCoeff q t
  have eq₃ := c.linearCoordinates_mapPoints (AlgHom.id 𝕜 D₀) sumCoeff q t
  rw [face_eq _ x y hxy rfl h₁] at eq₁
  rw [face_eq _ y z hyz (Z.reducePoint_eq I hproper x y hxy) h₂] at eq₂
  rw [face_eq _ x z ((hxy.trans hyz)) rfl h₃] at eq₃
  rw [eq₁, eq₂, eq₃]
  rfl

end Cocycle

/-- Fixed bases used to express all lift differences by scalar coefficients. -/
structure Coordinates where
  ideal_le : I ≤ maximalIdeal R
  chart : PointChart Z.G.X Z.unitPoint
  cotangentRank : ℕ
  idealRank : ℕ
  cotangentBasis : Module.Basis (Fin cotangentRank) 𝕜 chart.Cotangent
  idealBasis : Module.Basis (Fin idealRank) 𝕜 I

/-- Smoothness on the residue fibre gives an affine chart at its identity. Both
coefficient spaces are finite dimensional over the residue field. -/
def Coordinates.ofTarget [IsArtinianRing R] [Smooth Z.G.X.hom] : Coordinates Z I := by
  let c₀ := Classical.choice (PointChart.nonempty Z.G.X Z.unitPoint)
  exact ⟨hproper, c₀, _, _, Module.finBasis 𝕜 c₀.Cotangent, Module.finBasis 𝕜 I⟩

namespace Coordinates

variable {Z I} (b : Coordinates Z I)
variable [Module.Flat R C]

/-- A lift difference consists of one section of the residue ring for each pair of basis indices. -/
def equiv : b.chart.Points (D := D₀) (M := J₀) ≃ (Fin b.cotangentRank × Fin b.idealRank → D₀) :=
  b.chart.linearCoordinates.trans
    ((b.cotangentBasis.constr 𝕜 (M' := J₀)).symm.toEquiv.trans
      ((Equiv.piCongrRight (fun _ : Fin b.cotangentRank ↦
        (extendedBasis I b.idealBasis C).equivFun.toEquiv)).trans
          (Equiv.curry (Fin b.cotangentRank) (Fin b.idealRank) D₀).symm))

private theorem equiv_apply (v : b.chart.Points (D := D₀) (M := J₀))
    (ij : Fin b.cotangentRank × Fin b.idealRank) :
    b.equiv v ij = (extendedBasis I b.idealBasis C).equivFun
      (b.chart.linearCoordinates v (b.cotangentBasis ij.1)) ij.2 := rfl

/-- Difference coordinates for two lifts of the same reduced map. -/
def difference (x y : Z.Points C) (h : Z.Agree I x y) :
    Fin b.cotangentRank × Fin b.idealRank → D₀ :=
  b.equiv (Z.translatedDifference I b.ideal_le b.chart x y h)

@[simp] theorem difference_same (x : Z.Points C) : b.difference x x rfl = 0 := by
  funext ij
  change (extendedBasis I b.idealBasis C).equivFun
    (b.chart.linearCoordinates (Z.translatedDifference I b.ideal_le b.chart x x rfl)
      (b.cotangentBasis ij.1)) ij.2 = _
  rw [translatedDifference_same, b.chart.linearCoordinates_constant, LinearMap.zero_apply, map_zero]
  rfl

theorem difference_add (x y z : Z.Points C) (hxy : Z.Agree I x y) (hyz : Z.Agree I y z) :
    b.difference x z (hxy.trans hyz) = b.difference x y hxy + b.difference y z hyz := by
  funext ij
  simp only [difference, equiv_apply, Pi.add_apply]
  rw [Z.linearDifference_add, map_add, Pi.add_apply]

/-- Coordinate values commute with maps of flat affine tests. -/
theorem difference_restrict {C' : Type u} [CommRing C'] [Algebra R C'] [Module.Flat R C']
    (f : C →ₐ[R] C') (x y : Z.Points C) (h : Z.Agree I x y) (ij : Fin b.cotangentRank × Fin b.idealRank) :
    b.difference (Z.restrict f x) (Z.restrict f y) (Z.restrict_agree I f x y h) ij =
      fibreMap f (b.difference x y h ij) := by
  simp only [difference, equiv_apply]
  rw [Z.translatedDifference_restrict I b.ideal_le b.chart f x y h,
    b.chart.linearCoordinates_mapPoints, extendedBasis_equivFun_map]

/-- Change an affine lift by prescribed difference coordinates. -/
def correctBy (x : Z.Points C) (d : Fin b.cotangentRank × Fin b.idealRank → D₀) : Z.Points C :=
  Z.correct I b.ideal_le b.chart x (b.equiv.symm d)

@[simp] theorem correctBy_agree (x : Z.Points C) (d : Fin b.cotangentRank × Fin b.idealRank → D₀) :
    Z.Agree I x (b.correctBy x d) := Z.correct_agree ..

@[simp] theorem difference_correctBy (x : Z.Points C) (d : Fin b.cotangentRank × Fin b.idealRank → D₀) :
    b.difference x (b.correctBy x d) (b.correctBy_agree x d) = d := by
  simp [difference, correctBy]

@[simp] theorem correctBy_difference (x y : Z.Points C) (h : Z.Agree I x y) :
    b.correctBy x (b.difference x y h) = y := by simp [correctBy, difference]

/-- An agreed reduction and zero difference imply equality of the original maps. -/
theorem eq_of_difference_eq_zero (x y : Z.Points C) (h : Z.Agree I x y)
    (h₀ : b.difference x y h = 0) : x = y := by
  rw [← b.difference_same x] at h₀
  exact (b.correctBy_difference x x rfl).symm.trans
    ((congrArg (b.correctBy x) h₀.symm).trans (b.correctBy_difference x y h))

end Coordinates

end Target

end Langlands.AlgebraicGeometry.Deformation.ElementaryMorphismLifts
