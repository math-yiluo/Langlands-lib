import Langlands.AbelianScheme.Basic
import Langlands.AbelianScheme.Tate.PrimeAdic

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.AbelianScheme.Tate.PrimeAdic
universe u
variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S) (p : ℕ) [Fact p.Prime]

/-- Actual prime-power torsion sections of the abelian scheme. -/
abbrev Level (n : ℕ) := GroupScheme.Tate.Level A.toGrp T (p ^ n)

/-- The integral prime-adic Tate module of the bundled abelian scheme. -/
abbrev Integral := GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p

/-- Its scalar extension to the p-adic field. -/
abbrev Rational := GroupScheme.Tate.PrimeAdic.Rational A.toGrp T p

/-- Identify points of the actual multiplication kernel with the level. -/
abbrev kernelLevelEquiv (n : ℕ) :
    Additive (T ⟶ (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (p ^ n))).X) ≃+
      Level A T p n :=
  GroupScheme.Tate.kernelLevelEquiv A.toGrp T (p ^ n)

/-- The transition from exponent m to exponent n. -/
abbrev transition {n m : ℕ} (h : n ≤ m) : Level A T p m →+ Level A T p n :=
  GroupScheme.Tate.transition A.toGrp T (pow_dvd_pow p h)

lemma transition_smul {n m : ℕ} (h : n ≤ m) (a : ℤ_[p]) (x : Level A T p m) :
    transition A T p h (a • x) = a • transition A T p h x :=
  GroupScheme.Tate.PrimeAdic.transition_smul A.toGrp T p h a x

/-- Linear projection to an actual torsion level. -/
abbrev evaluation (n : ℕ) : Integral A T p →ₗ[ℤ_[p]] Level A T p n :=
  GroupScheme.Tate.PrimeAdic.evaluation A.toGrp T p n

lemma evaluation_smul (n : ℕ) (a : ℤ_[p]) (x : Integral A T p) :
    evaluation A T p n (a • x) =
      PadicInt.toZModPow n a • evaluation A T p n x := rfl

lemma evaluation_transition (n : ℕ) (x : Integral A T p) :
    transition A T p (Nat.le_succ n) (evaluation A T p (n + 1) x) =
      evaluation A T p n x :=
  GroupScheme.Tate.PrimeAdic.evaluation_transition A.toGrp T p n x

lemma continuous_evaluation (n : ℕ) : Continuous (evaluation A T p n) :=
  GroupScheme.Tate.PrimeAdic.continuous_evaluation A.toGrp T p n

/-- The universal linear map of a compatible family of torsion coordinates. -/
abbrev lift {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    (f : ∀ n : ℕ, M →ₗ[ℤ_[p]] Level A T p n)
    (hf : ∀ n x, transition A T p (Nat.le_succ n) (f (n + 1) x) = f n x) :
    M →ₗ[ℤ_[p]] Integral A T p :=
  GroupScheme.Tate.PrimeAdic.lift A.toGrp T p f hf

@[simp]
lemma evaluation_lift {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    (f : ∀ n : ℕ, M →ₗ[ℤ_[p]] Level A T p n) (hf) (n : ℕ) (x : M) :
    evaluation A T p n (lift A T p f hf x) = f n x := rfl

lemma lift_unique {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    (f : ∀ n : ℕ, M →ₗ[ℤ_[p]] Level A T p n) (hf)
    (g : M →ₗ[ℤ_[p]] Integral A T p)
    (hg : ∀ n x, evaluation A T p n (g x) = f n x) : g = lift A T p f hf :=
  GroupScheme.Tate.PrimeAdic.lift_unique A.toGrp T p f hf g hg

lemma continuous_lift {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [TopologicalSpace M]
    (f : ∀ n : ℕ, M →ₗ[ℤ_[p]] Level A T p n) (hf)
    (hc : ∀ n, Continuous (f n)) : Continuous (lift A T p f hf) :=
  GroupScheme.Tate.PrimeAdic.continuous_lift A.toGrp T p f hf hc

variable {A} {B C : AbelianScheme S}

abbrev levelMapLinear (f : A ⟶ B) (n : ℕ) :
    Level A T p n →ₗ[ℤ_[p]] Level B T p n :=
  GroupScheme.Tate.PrimeAdic.levelMapLinear T p (AbelianScheme.groupHom f) n

/-- An actual abelian-scheme homomorphism acts on compatible torsion sections. -/
abbrev map (f : A ⟶ B) : Integral A T p →ₗ[ℤ_[p]] Integral B T p :=
  GroupScheme.Tate.PrimeAdic.map T p (AbelianScheme.groupHom f)

@[simp]
lemma evaluation_map (f : A ⟶ B) (n : ℕ) (x : Integral A T p) :
    evaluation B T p n (map T p f x) =
      levelMapLinear T p f n (evaluation A T p n x) := rfl

@[simp]
lemma map_id : map T p (𝟙 A) = LinearMap.id :=
  GroupScheme.Tate.PrimeAdic.map_id T p

lemma map_comp (f : A ⟶ B) (g : B ⟶ C) :
    map T p (f ≫ g) = (map T p g).comp (map T p f) :=
  GroupScheme.Tate.PrimeAdic.map_comp T p (AbelianScheme.groupHom f) (AbelianScheme.groupHom g)

lemma map_add (f g : A ⟶ B) : map T p (f + g) = map T p f + map T p g :=
  GroupScheme.Tate.PrimeAdic.map_mul T p (AbelianScheme.groupHom f) (AbelianScheme.groupHom g)

lemma continuous_map (f : A ⟶ B) : Continuous (map T p f) :=
  GroupScheme.Tate.PrimeAdic.continuous_map T p (AbelianScheme.groupHom f)

/-- Rational scalar extension of the actual induced map. -/
abbrev rationalMap (f : A ⟶ B) : Rational A T p →ₗ[ℚ_[p]] Rational B T p :=
  GroupScheme.Tate.PrimeAdic.rationalMap T p (AbelianScheme.groupHom f)

@[simp]
lemma rationalMap_tmul (f : A ⟶ B) (a : ℚ_[p]) (x : Integral A T p) :
    rationalMap T p f (a ⊗ₜ[ℤ_[p]] x) = a ⊗ₜ[ℤ_[p]] map T p f x :=
  GroupScheme.Tate.PrimeAdic.rationalMap_tmul T p (AbelianScheme.groupHom f) a x

@[simp]
lemma rationalMap_id : rationalMap T p (𝟙 A) = LinearMap.id :=
  GroupScheme.Tate.PrimeAdic.rationalMap_id T p

lemma rationalMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    rationalMap T p (f ≫ g) = (rationalMap T p g).comp (rationalMap T p f) :=
  GroupScheme.Tate.PrimeAdic.rationalMap_comp T p
    (AbelianScheme.groupHom f) (AbelianScheme.groupHom g)

lemma rationalMap_add (f g : A ⟶ B) :
    rationalMap T p (f + g) = rationalMap T p f + rationalMap T p g :=
  GroupScheme.Tate.PrimeAdic.rationalMap_mul T p
    (AbelianScheme.groupHom f) (AbelianScheme.groupHom g)

variable (A)

/-- Sections of the actual pullback torsion kernel identify with the level. -/
abbrev fibreLevelEquiv {U : Scheme.{u}} (s : U ⟶ S) (n : ℕ) :
    (Over.mk (𝟙 U) ⟶
      (Over.pullback s).obj (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (p ^ n))).X) ≃
        Level A (Over.mk s) p n :=
  GroupScheme.Tate.fibreLevelEquiv A.toGrp s (p ^ n)

/-- Integral Tate module at an actual field-valued point. -/
abbrev IntegralAt {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S) :=
  Integral A (Over.mk s) p

/-- Rational Tate module at an actual field-valued point. -/
abbrev RationalAt {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S) :=
  Rational A (Over.mk s) p

end Langlands.AbelianScheme.Tate.PrimeAdic
