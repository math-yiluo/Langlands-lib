import Langlands.AbelianScheme.MultiplicationSpecialization

/-! # Finite relative powers and the factor maps of an abelian scheme -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.AbelianScheme

universe u

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- The iterated fibre product of `A` over `S`, including `S` at exponent zero. -/
abbrev relativePower : ℕ → Over S
  | 0 => Over.mk (𝟙 S)
  | m + 1 => A.X ⨯ relativePower m

/-- Projection to the specified factor of the relative power. -/
def relativePowerProjection : (m : ℕ) → Fin m → (relativePower A m ⟶ A.X)
  | 0, j => Fin.elim0 j
  | m + 1, j =>
      Fin.cases prod.fst (fun i => prod.snd ≫ relativePowerProjection m i) j

/-- The morphism into the relative power with a given tuple of projections. -/
def relativePowerLift {Z : Over S} :
    (m : ℕ) → (Fin m → (Z ⟶ A.X)) → (Z ⟶ relativePower A m)
  | 0, _ => Over.mkIdTerminal.from Z
  | m + 1, f => prod.lift (f 0) (relativePowerLift m fun i => f i.succ)

@[reassoc (attr := simp)]
theorem relativePowerLift_projection {Z : Over S} (m : ℕ)
    (f : Fin m → (Z ⟶ A.X)) (i : Fin m) :
    relativePowerLift A m f ≫ relativePowerProjection A m i = f i := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [relativePowerLift, relativePowerProjection, Fin.cases_zero, prod.lift_fst]
      · rw [relativePowerLift, relativePowerProjection, Fin.cases_succ,
          ← Category.assoc, prod.lift_snd, ih]

theorem relativePower_hom_ext {Z : Over S} {m : ℕ} {f g : Z ⟶ relativePower A m}
    (h : ∀ i, f ≫ relativePowerProjection A m i = g ≫ relativePowerProjection A m i) :
    f = g := by
  induction m with
  | zero => exact Over.mkIdTerminal.hom_ext f g
  | succ m ih =>
      apply prod.hom_ext
      · simpa only [relativePowerProjection, Fin.cases_zero] using h 0
      · apply ih
        intro i
        simpa only [relativePowerProjection, Fin.cases_succ, Category.assoc] using h i.succ

/-- The given maps exhibit the relative power as the finite product over `S`. -/
def relativePowerIsProduct (m : ℕ) :
    IsLimit (Fan.mk (relativePower A m) (relativePowerProjection A m)) :=
  Fan.IsLimit.mk _ (fun s => relativePowerLift A m (fun i => s.π.app ⟨i⟩))
    (fun _ _ => relativePowerLift_projection A _ _ _)
    (fun _ _ h => relativePower_hom_ext A (fun i =>
      (h i).trans (relativePowerLift_projection A _ _ i).symm))

private theorem product_smooth_proper (X Y : Over S)
    [Smooth X.hom] [IsProper X.hom] [Smooth Y.hom] [IsProper Y.hom] :
    Smooth (X ⨯ Y).hom ∧ IsProper (X ⨯ Y).hom := by
  let f := prod.fst (X := X) (Y := Y)
  let g := prod.snd (X := X) (Y := Y)
  have h : IsPullback f.left g.left X.hom Y.hom :=
    Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk f g) (prodIsProd X Y)
  have : Smooth f.left := MorphismProperty.of_isPullback h.flip inferInstance
  have : IsProper f.left := MorphismProperty.of_isPullback h.flip inferInstance
  rw [← f.w]
  exact ⟨inferInstance, inferInstance⟩

theorem relativePower_smooth_proper (m : ℕ) :
    Smooth (relativePower A m).hom ∧ IsProper (relativePower A m).hom := by
  induction m with
  | zero =>
      change Smooth (𝟙 S) ∧ IsProper (𝟙 S)
      exact ⟨inferInstance, inferInstance⟩
  | succ m ih =>
      have := ih.1
      have := ih.2
      exact product_smooth_proper A.X (relativePower A m)

/-- Integer multiplication on the specified factor, with the other factors fixed. -/
def relativePowerMultiply (m : ℕ) (i : Fin m) (a : ℤ) :
    relativePower A m ⟶ relativePower A m :=
  relativePowerLift A m fun j =>
    if j = i then
      relativePowerProjection A m j ≫ (groupHom (multiplication A a)).hom.hom
    else relativePowerProjection A m j

@[reassoc (attr := simp)]
theorem relativePowerMultiply_projection (m : ℕ) (i j : Fin m) (a : ℤ) :
    relativePowerMultiply A m i a ≫ relativePowerProjection A m j =
      if j = i then
        relativePowerProjection A m j ≫ (groupHom (multiplication A a)).hom.hom
      else relativePowerProjection A m j := by
  exact relativePowerLift_projection A _ _ _

/-- On sections, multiplication on the specified factor raises that coordinate to the
given integer power in the group of sections and keeps the other coordinates. -/
theorem relativePowerMultiply_points {Z : Over S} (m : ℕ) (i j : Fin m) (a : ℤ)
    (x : Z ⟶ relativePower A m) :
    x ≫ relativePowerMultiply A m i a ≫ relativePowerProjection A m j =
      if j = i then (x ≫ relativePowerProjection A m j) ^ a
      else x ≫ relativePowerProjection A m j := by
  rw [relativePowerMultiply_projection]
  split_ifs
  · rw [← Category.assoc, points_multiplication]
  all_goals rfl

/-- Multiplication by one on a factor is the identity. -/
@[simp] theorem relativePowerMultiply_one (m : ℕ) (i : Fin m) :
    relativePowerMultiply A m i 1 = 𝟙 _ := by
  apply relativePower_hom_ext A
  intro j
  rw [relativePowerMultiply_projection, Category.id_comp]
  split_ifs
  · rw [points_multiplication, zpow_one]
  all_goals rfl

/-- Successive multiplications on the same factor compose to multiplication by the
product of the integers. -/
theorem relativePowerMultiply_comp (m : ℕ) (i : Fin m) (a b : ℤ) :
    relativePowerMultiply A m i a ≫ relativePowerMultiply A m i b =
      relativePowerMultiply A m i (a * b) := by
  apply relativePower_hom_ext A
  intro j
  rw [Category.assoc, relativePowerMultiply_points A m i j b (relativePowerMultiply A m i a),
    relativePowerMultiply_projection A m i j a, relativePowerMultiply_projection A m i j (a * b)]
  split_ifs
  · rw [points_multiplication, points_multiplication, zpow_mul]
  all_goals rfl

/-- Applying the same multiplication on two factors commutes. -/
theorem relativePowerMultiply_comm (m : ℕ) (i j : Fin m) (a : ℤ) :
    relativePowerMultiply A m i a ≫ relativePowerMultiply A m j a =
      relativePowerMultiply A m j a ≫ relativePowerMultiply A m i a := by
  apply relativePower_hom_ext A
  intro k
  by_cases hki : k = i
  · subst i
    by_cases hkj : k = j
    · subst j
      rfl
    · simp [Category.assoc, hkj]
  · by_cases hkj : k = j
    · subst j
      simp [Category.assoc, hki]
    · simp [Category.assoc, hki, hkj]

/-- Multiplication by two on the specified factor, with the other factors fixed. -/
abbrev relativePowerDouble (m : ℕ) (i : Fin m) : relativePower A m ⟶ relativePower A m :=
  relativePowerMultiply A m i 2

/-- The projections of the multiplication by two on a factor. -/
theorem relativePowerDouble_projection (m : ℕ) (i j : Fin m) :
    relativePowerDouble A m i ≫ relativePowerProjection A m j =
      if j = i then
        relativePowerProjection A m j ≫ (groupHom (multiplication A 2)).hom.hom
      else relativePowerProjection A m j :=
  relativePowerMultiply_projection A m i j 2

/-- The permutation map has coordinate `j` equal to the original coordinate
`σ j`, the convention for contravariant pullback on cohomology. -/
def relativePowerPermute (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    relativePower A m ⟶ relativePower A m :=
  relativePowerLift A m fun j => relativePowerProjection A m (σ j)

@[reassoc (attr := simp)]
theorem relativePowerPermute_projection (m : ℕ) (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    relativePowerPermute A m σ ≫ relativePowerProjection A m j =
      relativePowerProjection A m (σ j) :=
  relativePowerLift_projection A _ _ _

@[simp]
theorem relativePowerPermute_one (m : ℕ) :
    relativePowerPermute A m 1 = 𝟙 _ := by
  apply relativePower_hom_ext A
  intro i
  simp

theorem relativePowerPermute_comp (m : ℕ) (σ τ : Equiv.Perm (Fin m)) :
    relativePowerPermute A m σ ≫ relativePowerPermute A m τ =
      relativePowerPermute A m (σ * τ) := by
  apply relativePower_hom_ext A
  intro i
  simp [Category.assoc]

/-- Permuting factors transports the multiplication to the corresponding input factor. -/
theorem relativePowerPermute_multiply (m : ℕ) (σ : Equiv.Perm (Fin m)) (i : Fin m) (a : ℤ) :
    relativePowerPermute A m σ ≫ relativePowerMultiply A m i a =
      relativePowerMultiply A m (σ i) a ≫ relativePowerPermute A m σ := by
  apply relativePower_hom_ext A
  intro j
  by_cases hji : j = i <;> simp [Category.assoc, hji]

end Langlands.AbelianScheme
