import Langlands.GroupScheme.RelativeUnipotent.RootWeightPolynomial
import Langlands.GroupScheme.Rational.NonnegativeCyclicCoordinates

/-! # Intrinsic cyclic cutoffs for actual root-weight charts -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Corepresented

open LocalSplitCell

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} {I : Type u} [Fintype I] [DecidableEq I]

/-- Restrict a split-torus action to the cocharacter with exponent vector v,
read as the rank-one split-torus action on algebra points. -/
def TorusAction.alongCocharacter (σ : TorusAction F I) (v : I → ℤ) :
    TorusAction F PUnit where
  act {A} s x := σ.act (fun i => s PUnit.unit ^ v i) x
  act_one {A} x := by
    have h : (fun i => (1 : PUnit.{u+1} → Aˣ) PUnit.unit ^ v i) = (1 : I → Aˣ) := by
      funext i
      exact one_zpow _
    rw [h, σ.act_one]
  act_mul {A} s s' x := by
    have h : (fun i => (s * s') PUnit.unit ^ v i) =
        (fun i => s PUnit.unit ^ v i) * (fun i => s' PUnit.unit ^ v i) := by
      funext i
      exact mul_zpow _ _ _
    rw [h, σ.act_mul]
  act_map_mul s x y := σ.act_map_mul _ x y
  naturality f s x := by
    simpa only [map_zpow] using σ.naturality f (fun i => s PUnit.unit ^ v i) x

private theorem zpow_sum {A : Type u} [CommGroup A] (z : A) (s : Finset I) (f : I → ℤ) :
    z ^ (∑ i ∈ s, f i) = ∏ i ∈ s, z ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

/-- Restriction to a cocharacter pairs every homogeneous character with its
exponent vector; this is an arbitrary-ring identity. -/
theorem isHomogeneous_alongCocharacter
    (e : (F ⋙ forget GrpCat).CorepresentableBy B) (σ : TorusAction F I)
    (v : I → ℤ) {ch : I → ℤ} {g : B} (hg : IsHomogeneous e σ ch g) :
    IsHomogeneous e (σ.alongCocharacter v) (fun _ => coPairing ch v) g := by
  apply (isHomogeneous_iff_coord_act _ _ _ _).2
  intro A s x
  change coord e (σ.act (fun i => s PUnit.unit ^ v i) x) g = _
  rw [coord_act_of_isHomogeneous e σ _ x hg]
  congr 2
  change (∏ i, (s PUnit.unit ^ v i) ^ ch i) =
    ∏ _ : PUnit, s PUnit.unit ^ coPairing ch v
  simp only [Fintype.prod_unique]
  rw [coPairing, zpow_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [← zpow_mul, mul_comm]

end Langlands.GroupScheme.Corepresented

namespace Langlands.GroupScheme.RelativeUnipotent.RootHeightChart

open LocalSplitCell Corepresented

variable {R : Type u} [CommRing R]
  {I J : Type u} [Fintype I] [DecidableEq I]
  {U G : GroupScheme (Spec (CommRingCat.of R))}
  {t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {ch : J → I → ℤ} {fam : J → (Ga R ⟶ G)}
  (C : RootHeightChart U) (j : U ⟶ G) [Mono j.hom.hom]
  {index : Fin C.dimension → J}
  (hroot : ∀ k, C.roots (ULift.up k) ≫ j = fam (index k))
  (hu : TorusEquivariant t ch fam)

theorem polynomialVariable_counit (k : Fin C.dimension) :
    AffineLinearEmbedding.counit C.polynomialCorepresentation (X k) = 0 := by
  let A : CommAlgCat.{u} (CommRingCat.of R) := CommAlgCat.of (CommRingCat.of R) R
  have hz : coord C.polynomialCorepresentation (1 : U.affinePoints A) (X k) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (affineSectionsIso A).inv).1
    rw [C.polynomialCoordinate_sections, map_zero]
    rw [← orderedProduct_zero C.roots ULift.up _, C.coordinates_orderedProduct]
    rfl
  rw [coord_one] at hz
  exact hz

/-- The actual affine root chart supplies all the data of the nonnegative cyclic
polynomial-coordinate criterion whenever its root pairings have the given weights. -/
def cyclicCoordinates (v : I → ℤ) (w : Fin C.dimension → ℕ)
    (hw : ∀ k, coPairing (ch (index k)) v = w k) :
    NonnegativeCyclicCoordinates C.polynomialCorepresentation
      ((C.polynomialTorusAction j hroot hu).alongCocharacter v) (fun _ : PUnit => (1 : ℤ)) where
  dimension := C.dimension
  weight := w
  generator := X
  homogeneous k := by
    have h := isHomogeneous_alongCocharacter C.polynomialCorepresentation
      (C.polynomialTorusAction j hroot hu) v
      (C.isHomogeneous_polynomialVariable j hroot hu k)
    have he : (w k • (fun _ : PUnit => (1 : ℤ))) =
        (fun _ : PUnit => coPairing (ch (index k)) v) := by
      funext q
      simp only [Pi.smul_apply, nsmul_eq_mul, mul_one, hw k]
    rw [he]
    exact h
  augmented := C.polynomialVariable_counit
  surjective := by
    intro p
    refine ⟨p, ?_⟩
    exact aeval_X_left_apply p

/-- The actual all-algebra root-weight cutoff equals the intrinsic cyclic
cutoff for the actual restricted conjugation action. -/
theorem mem_intrinsic_cutoff_iff (v : I → ℤ) (w : Fin C.dimension → ℕ)
    (hw : ∀ k, coPairing (ch (index k)) v = w k)
    {A : CommAlgCat.{u} (CommRingCat.of R)} (x : U.affinePoints A)
    {r : ℕ} (hr : 0 < r) :
    x ∈ weightSubgroup C.polynomialCorepresentation
      ((C.polynomialTorusAction j hroot hu).alongCocharacter v)
        (cyclicTail (fun _ : PUnit => (1 : ℤ)) r) A ↔
      ∀ k, w k < r → C.coordinates ((algSpec (CommRingCat.of R)).obj (op A)) x k = 0 := by
  have ha : (fun _ : PUnit => (1 : ℤ)) ≠ 0 := by
    intro h
    have := congrFun h PUnit.unit
    exact one_ne_zero this
  rw [(C.cyclicCoordinates j hroot hu v w hw).mem_iff ha _ hr]
  apply forall_congr'
  intro k
  apply imp_congr_right
  intro _
  have he := C.polynomialCoordinate_sections x k
  constructor
  · intro h
    change coord C.polynomialCorepresentation x (X k) = 0 at h
    exact he.symm.trans ((congrArg (affineSectionsIso A).inv.hom h).trans (map_zero _))
  · intro h
    change coord C.polynomialCorepresentation x (X k) = 0
    apply (ConcreteCategory.bijective_of_isIso (affineSectionsIso A).inv).1
    exact (he.trans h).trans (map_zero _).symm

/-- A positive multiplier in the realizing cocharacter only rescales the
intrinsic cutoff; the represented filtration's original weights stay unscaled. -/
theorem mem_intrinsic_scaled_iff (W : RootWeightData C)
    (v : I → ℤ) (q : ℕ) (hq : 0 < q)
    (hw : ∀ k, coPairing (ch (index k)) v = q * W.weight k)
    {A : CommAlgCat.{u} (CommRingCat.of R)} (x : U.affinePoints A) (d : ℕ) :
    x ∈ weightSubgroup C.polynomialCorepresentation
      ((C.polynomialTorusAction j hroot hu).alongCocharacter v)
        (cyclicTail (fun _ : PUnit => (1 : ℤ)) (q * (d + 1))) A ↔
      x ∈ (W.subgroup d).carrier ((algSpec (CommRingCat.of R)).obj (op A)) := by
  rw [C.mem_intrinsic_cutoff_iff j hroot hu v (fun k => q * W.weight k)
    (by intro k; simpa only [Nat.cast_mul] using hw k) x
    (Nat.mul_pos hq (Nat.zero_lt_succ d)), W.mem_subgroup_iff]
  simp only [Nat.mul_lt_mul_left hq]

end Langlands.GroupScheme.RelativeUnipotent.RootHeightChart
