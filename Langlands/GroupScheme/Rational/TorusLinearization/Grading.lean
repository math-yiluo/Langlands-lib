import Langlands.GroupScheme.Rational.TorusLinearization.PointAction
import Langlands.GroupScheme.Torus.CharacterActionGrading

/-! # The weight grading of an abstract split torus action -/

noncomputable section

universe u

open MvPolynomial

namespace Langlands.GroupScheme.TorusLinearization.PointAction

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {I : Type u} {n : ℕ}
  (a : PointAction k K I n)

/-- The action of a family of units over a `K`-algebra, with `k`-structure through `K`. -/
def actK {C : Type u} [CommRing C] [Algebra K C] (τ : I → Cˣ) (y : Fin n → C) : Fin n → C :=
  let _ : Algebra k C := ((algebraMap K C).comp (algebraMap k K)).toAlgebra
  have _ : IsScalarTower k K C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  a.act (a.σ τ) y

theorem actK_one {C : Type u} [CommRing C] [Algebra K C] (y : Fin n → C) :
    a.actK (1 : I → Cˣ) y = y := by
  let _ : Algebra k C := ((algebraMap K C).comp (algebraMap k K)).toAlgebra
  have _ : IsScalarTower k K C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact a.act_σ_one y

theorem actK_mul {C : Type u} [CommRing C] [Algebra K C] (τ τ' : I → Cˣ) (y : Fin n → C) :
    a.actK (τ * τ') y = a.actK τ (a.actK τ' y) := by
  let _ : Algebra k C := ((algebraMap K C).comp (algebraMap k K)).toAlgebra
  have _ : IsScalarTower k K C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact a.act_σ_mul τ τ' y

theorem actK_map {C D : Type u} [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]
    (f : C →ₐ[K] D) (τ : I → Cˣ) (y : Fin n → C) :
    a.actK (fun i => Units.map f.toRingHom.toMonoidHom (τ i)) (f ∘ y) = f ∘ a.actK τ y := by
  let _ : Algebra k C := ((algebraMap K C).comp (algebraMap k K)).toAlgebra
  have _ : IsScalarTower k K C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra k D := ((algebraMap K D).comp (algebraMap k K)).toAlgebra
  have _ : IsScalarTower k K D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  change a.act (a.σ _) _ = f ∘ a.act (a.σ τ) y
  rw [← a.map_σ f τ]
  exact a.act_map (f.restrictScalars k) (a.σ τ) y

section CharacterAction

open CategoryTheory

variable [DecidableEq I]

/-- The coordinate units of a character of `I → ℤ`. -/
def unitsOf {C : Type u} [CommRing C] (τ : Multiplicative (I → ℤ) →* Cˣ) : I → Cˣ :=
  fun i => τ (Multiplicative.ofAdd (Pi.single i 1))

/-- The character action of the split torus on the polynomial algebra over `K`. -/
def charAction : CharacterAction.Action (R := CommRingCat.of K) (M := I → ℤ)
    (CommAlgCat.of (CommRingCat.of K) (MvPolynomial (Fin n) K)) where
  act {C} τ x := CommAlgCat.ofHom (aeval (a.actK (unitsOf τ) (fun j => x.hom (X j))))
  one {C} x := by
    ext1
    apply MvPolynomial.algHom_ext
    intro j
    have h1 : unitsOf (1 : Multiplicative (I → ℤ) →* Cˣ) = 1 := rfl
    simp [h1, actK_one]
  mul {C} τ s x := by
    ext1
    apply MvPolynomial.algHom_ext
    intro j
    have h1 : unitsOf (τ * s) = unitsOf τ * unitsOf s := rfl
    simp [h1, actK_mul]
  naturality {C D} f τ x := by
    ext1
    apply MvPolynomial.algHom_ext
    intro j
    have h1 : unitsOf (CharacterAction.mapCharacter f τ) =
        fun i => Units.map f.hom.toRingHom.toMonoidHom (unitsOf τ i) := rfl
    have h2 := congrFun (a.actK_map f.hom (unitsOf τ) (fun j => x.hom (X j))) j
    simp only [CommAlgCat.hom_ofHom, CommAlgCat.hom_comp, aeval_X, AlgHom.comp_apply, h1]
    exact h2

end CharacterAction

/-- The action through a splitting does not depend on the chosen `k`-structure. -/
theorem actK_eq {C : Type u} [CommRing C] [Algebra k C] [Algebra K C] [IsScalarTower k K C]
    (τ : I → Cˣ) (y : Fin n → C) : a.actK τ y = a.act (a.σ τ) y := by
  have h : ((algebraMap K C).comp (algebraMap k K)).toAlgebra = ‹Algebra k C› :=
    Algebra.algebra_ext _ _ fun r => (IsScalarTower.algebraMap_apply k K C r).symm
  subst h
  rfl

section Components

open CategoryTheory

/-- Evaluation of a group algebra, written as a finite sum. -/
theorem evaluate_apply {M : Type u} [AddCommGroup M] {B C : CommAlgCat.{u} (CommRingCat.of K)}
    (x : B ⟶ C) (t : Multiplicative M →* Cˣ) (y : AddMonoidAlgebra B M) :
    (CharacterAction.evaluate x t).hom y =
      y.coeff.sum fun m b => x.hom b * (t (Multiplicative.ofAdd m) : C) := by
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add y z hy hz =>
    rw [map_add, hy, hz, AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index']
    · intro m
      simp
    · intro m b b'
      rw [map_add, add_mul]
  | single m b =>
    rw [CharacterAction.evaluate_single, AddMonoidAlgebra.coeff_single,
      Finsupp.sum_single_index]
    simp

variable [DecidableEq I]

/-- The coaction of the split torus on the polynomial algebra over `K`. -/
def coact : MvPolynomial (Fin n) K →ₐ[K] AddMonoidAlgebra (MvPolynomial (Fin n) K) (I → ℤ) :=
  (CharacterAction.coaction a.charAction).hom

/-- The component of weight `χ` of a polynomial over `K`. -/
def comp (χ : I → ℤ) : MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K where
  toFun f := (a.coact f).coeff χ
  map_add' f g := by
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  map_smul' c f := by
    rw [map_smul, AddMonoidAlgebra.coeff_smul_apply]
    rfl

theorem comp_apply (χ : I → ℤ) (f : MvPolynomial (Fin n) K) :
    a.comp χ f = (a.coact f).coeff χ := rfl

/-- Each component is homogeneous of its weight. -/
theorem coact_comp (χ : I → ℤ) (f : MvPolynomial (Fin n) K) :
    a.coact (a.comp χ f) = AddMonoidAlgebra.single χ (a.comp χ f) :=
  CharacterAction.coaction_coefficient_homogeneous a.charAction f χ

open Classical in
theorem comp_comp (χ ψ : I → ℤ) (f : MvPolynomial (Fin n) K) :
    a.comp ψ (a.comp χ f) = if χ = ψ then a.comp χ f else 0 := by
  rw [comp_apply, coact_comp, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- A polynomial is the sum of its components. -/
theorem sum_comp (f : MvPolynomial (Fin n) K) {s : Finset (I → ℤ)}
    (hs : (a.coact f).coeff.support ⊆ s) : ∑ χ ∈ s, a.comp χ f = f := by
  have h := congrArg (fun g => g.hom f) (CharacterAction.coaction_counit a.charAction)
  simp only [CommAlgCat.hom_comp, AlgHom.comp_apply, CommAlgCat.hom_id, AlgHom.id_apply] at h
  rw [evaluate_apply] at h
  change ((a.coact f).coeff.sum fun m b => (𝟙 _ : CommAlgCat.of (CommRingCat.of K)
    (MvPolynomial (Fin n) K) ⟶ _).hom b * _) = f at h
  rw [Finsupp.sum_of_support_subset _ hs _ (fun _ _ => by simp)] at h
  simpa [comp_apply] using h

/-- The point action is evaluation of the coaction, as a finite sum. -/
theorem charAction_act_apply {C : CommAlgCat.{u} (CommRingCat.of K)}
    (τ : Multiplicative (I → ℤ) →* Cˣ)
    (x : CommAlgCat.of (CommRingCat.of K) (MvPolynomial (Fin n) K) ⟶ C)
    (f : MvPolynomial (Fin n) K) {s : Finset (I → ℤ)} (hs : (a.coact f).coeff.support ⊆ s) :
    (a.charAction.act τ x).hom f =
      ∑ χ ∈ s, x.hom (a.comp χ f) * (τ (Multiplicative.ofAdd χ) : C) := by
  rw [CharacterAction.act_eq_coaction_evaluate, CommAlgCat.hom_comp, AlgHom.comp_apply,
    evaluate_apply]
  change ((a.coact f).coeff.sum fun m b => x.hom b * _) = _
  rw [Finsupp.sum_of_support_subset _ hs _ (fun _ _ => by simp)]
  rfl

section Frobenius

variable (p : ℕ) [Fact p.Prime] [CharP K p]

open Classical in
/-- The components of a `p`-th power are `p`-th powers of components, in `p` times the weight. -/
theorem comp_pow_char (χ : I → ℤ) (f : MvPolynomial (Fin n) K) :
    a.comp χ (f ^ p) = ∑ ψ ∈ (a.coact f).coeff.support,
      if p • ψ = χ then a.comp ψ f ^ p else 0 := by
  have : CharP (AddMonoidAlgebra (MvPolynomial (Fin n) K) (I → ℤ)) p :=
    charP_of_injective_algebraMap (algebraMap K _).injective p
  have hf : a.coact f = ∑ ψ ∈ (a.coact f).coeff.support,
      AddMonoidAlgebra.single ψ (a.comp ψ f) := by
    conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single (a.coact f)]
    rfl
  set s := (a.coact f).coeff.support
  rw [comp_apply, map_pow, hf, sum_pow_char, AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem comp_pow_char_smul (χ : I → ℤ) (f : MvPolynomial (Fin n) K) :
    a.comp (p • χ) (f ^ p) = a.comp χ f ^ p := by
  classical
  have hinj : ∀ ψ : I → ℤ, p • ψ = p • χ ↔ ψ = χ := by
    intro ψ
    refine ⟨fun h => funext fun i => ?_, fun h => h ▸ rfl⟩
    have h' := congrFun h i
    simp only [Pi.smul_apply, nsmul_eq_mul] at h'
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h'
  rw [comp_pow_char]
  simp_rw [hinj]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [comp_apply, Finsupp.notMem_support_iff.mp h,
      zero_pow (Fact.out : p.Prime).ne_zero]

theorem comp_pow_char_eq_zero (χ : I → ℤ) (hχ : ∀ ψ : I → ℤ, p • ψ ≠ χ)
    (f : MvPolynomial (Fin n) K) : a.comp χ (f ^ p) = 0 := by
  classical
  rw [comp_pow_char]
  exact Finset.sum_eq_zero fun ψ _ => ite_eq_right_iff.mpr fun h => absurd h (hχ ψ)

end Frobenius

end Components

section Characters

variable [Fintype I]

/-- The character of `I → ℤ` with given coordinate units. -/
def charOf {C : Type u} [CommRing C] (τ : I → Cˣ) : Multiplicative (I → ℤ) →* Cˣ where
  toFun χ := ∏ i, τ i ^ (Multiplicative.toAdd χ i)
  map_one' := by simp
  map_mul' χ ψ := by
    simp only [toAdd_mul, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem unitsOf_charOf [DecidableEq I] {C : Type u} [CommRing C] (τ : I → Cˣ) :
    unitsOf (charOf τ) = τ := by
  funext i
  change ∏ j, τ j ^ ((Pi.single i 1 : I → ℤ) j) = τ i
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem map_charOf {C D : Type u} [CommRing C] [CommRing D] (f : C →+* D) (τ : I → Cˣ)
    (χ : Multiplicative (I → ℤ)) :
    Units.map f.toMonoidHom (charOf τ χ) = charOf (fun i => Units.map f.toMonoidHom (τ i)) χ := by
  simp [charOf, map_prod, map_zpow]

end Characters

/-- The action of a point over a `K`-algebra on polynomials over `K`. -/
def pullK {C : Type u} [CommRing C] [Algebra k C] [Algebra K C] [IsScalarTower k K C]
    (t : a.Pt C) : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) C :=
  aeval (a.poly t)

theorem pullK_map {C : Type u} [CommRing C] [Algebra k C] [Algebra K C] [IsScalarTower k K C]
    (t : a.Pt C) (f : MvPolynomial (Fin n) k) :
    a.pullK t (MvPolynomial.map (algebraMap k K) f) = a.pull t f := by
  rw [pullK, pull, aeval_map_algebraMap]

/-- Through the splitting, the action on polynomials over `K` is given by the components. -/
theorem pullK_σ [Fintype I] [DecidableEq I] {C : Type u} [CommRing C] [Algebra k C]
    [Algebra K C] [IsScalarTower k K C] (τ : I → Cˣ) (h : MvPolynomial (Fin n) K)
    {s : Finset (I → ℤ)} (hs : (a.coact h).coeff.support ⊆ s) :
    a.pullK (a.σ τ) h = ∑ χ ∈ s, MvPolynomial.C ((charOf τ (Multiplicative.ofAdd χ) : Cˣ) : C) *
      MvPolynomial.map (algebraMap K C) (a.comp χ h) := by
  let D : CommAlgCat.{u} (CommRingCat.of K) :=
    CommAlgCat.of (CommRingCat.of K) (MvPolynomial (Fin n) C)
  let x : CommAlgCat.of (CommRingCat.of K) (MvPolynomial (Fin n) K) ⟶ D :=
    CommAlgCat.ofHom (MvPolynomial.mapAlgHom (Algebra.ofId K C))
  let τ' : Multiplicative (I → ℤ) →* Dˣ :=
    charOf (fun i => Units.map (algebraMap C (MvPolynomial (Fin n) C)).toMonoidHom (τ i))
  have h3 : a.poly (a.σ τ) = a.act (a.σ (fun i =>
      Units.map (algebraMap C (MvPolynomial (Fin n) C)).toMonoidHom (τ i))) X := by
    have := a.map_σ (IsScalarTower.toAlgHom K C (MvPolynomial (Fin n) C)) τ
    exact congrArg (fun t => a.act t X) this
  have h2 : (a.charAction.act τ' x).hom h = a.pullK (a.σ τ) h := by
    change aeval (a.actK (unitsOf τ') (fun j => x.hom (X j))) h = aeval (a.poly (a.σ τ)) h
    have hx : (fun j => x.hom (X j)) = X := funext fun j => by
      exact (MvPolynomial.mapAlgHom_apply _ _).trans (MvPolynomial.map_X _ _)
    rw [unitsOf_charOf, hx, h3]
    exact congrArg (fun y => aeval y h) (a.actK_eq _ _)
  rw [← h2, a.charAction_act_apply τ' x h hs]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [mul_comm]
  congr 1
  have h4 := congrArg Units.val
    (map_charOf (algebraMap C (MvPolynomial (Fin n) C)) τ (Multiplicative.ofAdd χ))
  exact h4.symm

end Langlands.GroupScheme.TorusLinearization.PointAction
