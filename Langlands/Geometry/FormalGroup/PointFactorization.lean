import Langlands.Geometry.FormalGroup.FlatPointDescent
import Langlands.Geometry.FormalGroup.ModuleHomOfPoints
import Langlands.Geometry.FormalGroup.FiniteKernel

/-! # Factoring formal homomorphisms through fppf-locally surjective ones -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace Hom

/-- fppf-locally surjective homomorphisms are epimorphisms of formal modules. -/
theorem IsFppfLocallySurjective.comp_right_cancel {f : Hom M N}
    (hf : f.IsFppfLocallySurjective) {a b : Hom N P} (h : a.comp f = b.comp f) : a = b := by
  apply ext_onAlgebraPoints
  intro A y
  obtain ⟨B, φ, hφ, -, x, hx⟩ := hf A y
  apply P.algebraMapPoints_injective φ hφ
  rw [onAlgebraPoints_natural, onAlgebraPoints_natural, ← hx, ← onAlgebraPoints_comp,
    ← onAlgebraPoints_comp, h]

variable (f : Hom M N) (h : Hom M P)

/-- `w` is a value at `y` of a factorization of `h` through `f`: every lift of `y` along
every algebra map is sent by `h` to the corresponding image of `w`. -/
def IsFactorValue {A : CommAlgCat.{v} R} (y : N.AlgebraPoint A) (w : P.AlgebraPoint A) :
    Prop :=
  ∀ (C : CommAlgCat.{v} R) (α : A ⟶ C) (x : M.AlgebraPoint C),
    f.onAlgebraPoints x = N.algebraMapPoints α.hom y →
      h.onAlgebraPoints x = P.algebraMapPoints α.hom w

variable {f h}

/-- Two points with the same `f`-image have the same `h`-image. -/
theorem eq_of_kernel_le
    (hker : ∀ (A : CommAlgCat.{v} R) (x : M.AlgebraPoint A),
      f.onAlgebraPoints x = 0 → h.onAlgebraPoints x = 0)
    {A : CommAlgCat.{v} R} {x x' : M.AlgebraPoint A}
    (hx : f.onAlgebraPoints x = f.onAlgebraPoints x') :
    h.onAlgebraPoints x = h.onAlgebraPoints x' := by
  have := hker A (x - x') (by rw [map_sub, hx, sub_self])
  rwa [map_sub, sub_eq_zero] at this

/-- Factor values exist and are unique. -/
theorem existsUnique_isFactorValue (hf : f.IsFppfLocallySurjective)
    (hker : ∀ (A : CommAlgCat.{v} R) (x : M.AlgebraPoint A),
      f.onAlgebraPoints x = 0 → h.onAlgebraPoints x = 0)
    {A : CommAlgCat.{v} R} (y : N.AlgebraPoint A) :
    ∃! w : P.AlgebraPoint A, IsFactorValue f h y w := by
  obtain ⟨B, φ, hφ, -, xB, hxB⟩ := hf A y
  obtain ⟨w, hw⟩ := P.exists_algebraMapPoints_eq φ hφ (h.onAlgebraPoints xB) (by
    intro C α β hαβ
    rw [onAlgebraPoints_natural, onAlgebraPoints_natural]
    apply eq_of_kernel_le hker
    rw [← onAlgebraPoints_natural, ← onAlgebraPoints_natural, hxB,
      ← N.algebraMapPoints_comp, ← N.algebraMapPoints_comp]
    exact congrArg (fun γ : A ⟶ C => N.algebraMapPoints γ.hom y) hαβ)
  refine ⟨w, ?_, ?_⟩
  · intro C α x hx
    let T := pushout φ α
    have hinr := pushoutInr_faithfullyFlat φ α hφ
    apply P.algebraMapPoints_injective (pushoutInr φ α) hinr
    rw [onAlgebraPoints_natural, ← P.algebraMapPoints_comp]
    change _ = P.algebraMapPoints (α ≫ pushoutInr φ α).hom w
    rw [← pushout_comm, CommAlgCat.hom_comp, P.algebraMapPoints_comp, hw,
      onAlgebraPoints_natural]
    apply eq_of_kernel_le hker
    rw [← onAlgebraPoints_natural, ← onAlgebraPoints_natural, hx, hxB,
      ← N.algebraMapPoints_comp, ← N.algebraMapPoints_comp]
    exact congrArg (fun γ : A ⟶ T => N.algebraMapPoints γ.hom y) (pushout_comm φ α).symm
  · intro w' hw'
    apply P.algebraMapPoints_injective φ hφ
    rw [hw, ← hw' B φ xB hxB]

/-- A factor value can be recognized on one faithfully flat cover where `y` lifts. -/
theorem IsFactorValue.eq (hf : f.IsFppfLocallySurjective)
    (hker : ∀ (A : CommAlgCat.{v} R) (x : M.AlgebraPoint A),
      f.onAlgebraPoints x = 0 → h.onAlgebraPoints x = 0)
    {A : CommAlgCat.{v} R} {y : N.AlgebraPoint A} {w w' : P.AlgebraPoint A}
    (hw : IsFactorValue f h y w) (hw' : IsFactorValue f h y w') : w = w' :=
  (existsUnique_isFactorValue hf hker y).unique hw hw'

variable (f h)

/-- The pointwise factorization of `h` through `f`. -/
def factorPoints (hf : f.IsFppfLocallySurjective)
    (hker : ∀ (A : CommAlgCat.{v} R) (x : M.AlgebraPoint A),
      f.onAlgebraPoints x = 0 → h.onAlgebraPoints x = 0)
    (A : CommAlgCat.{v} R) (y : N.AlgebraPoint A) : P.AlgebraPoint A :=
  (existsUnique_isFactorValue hf hker y).exists.choose

variable {f h}

theorem isFactorValue_factorPoints (hf : f.IsFppfLocallySurjective)
    (hker : ∀ (A : CommAlgCat.{v} R) (x : M.AlgebraPoint A),
      f.onAlgebraPoints x = 0 → h.onAlgebraPoints x = 0)
    {A : CommAlgCat.{v} R} (y : N.AlgebraPoint A) :
    IsFactorValue f h y (factorPoints f h hf hker A y) :=
  (existsUnique_isFactorValue hf hker y).exists.choose_spec

/-- The factor exists as an actual formal O-module homomorphism. -/
theorem exists_comp_eq (hf : f.IsFppfLocallySurjective)
    (hker : ∀ (A : CommAlgCat.{v} R) (x : M.AlgebraPoint A),
      f.onAlgebraPoints x = 0 → h.onAlgebraPoints x = 0) :
    ∃ g : Hom N P, g.comp f = h := by
  let Φ := factorPoints f h hf hker
  have hΦ := fun {A : CommAlgCat.{v} R} (y : N.AlgebraPoint A) =>
    isFactorValue_factorPoints hf hker y
  have hnat : IsNaturalOnPoints Φ := by
    intro A A' ψ y
    refine IsFactorValue.eq hf hker ?_ (hΦ _)
    intro C α x hx
    rw [← P.algebraMapPoints_comp]
    rw [← N.algebraMapPoints_comp] at hx
    exact hΦ y C (ψ ≫ α) x hx
  have hadd : ∀ (A : CommAlgCat.{v} R) (y y' : N.AlgebraPoint A),
      Φ A (y + y') = Φ A y + Φ A y' := by
    intro A y y'
    refine IsFactorValue.eq hf hker (hΦ _) ?_
    intro C α x hx
    obtain ⟨C₁, γ, hγ, -, x₁, hx₁⟩ := hf C (N.algebraMapPoints α.hom y)
    apply P.algebraMapPoints_injective γ hγ
    rw [onAlgebraPoints_natural, ← P.algebraMapPoints_comp, map_add,
      ← sub_add_cancel (M.algebraMapPoints γ.hom x) x₁, map_add, add_comm]
    rw [← N.algebraMapPoints_comp] at hx₁
    rw [hΦ y C₁ (α ≫ γ) x₁ hx₁]
    congr 1
    apply hΦ y' C₁ (α ≫ γ)
    rw [map_sub, ← onAlgebraPoints_natural, hx, hx₁]
    simp only [CommAlgCat.hom_comp, N.algebraMapPoints_comp, map_add, add_sub_cancel_left]
  have hsmul : ∀ (A : CommAlgCat.{v} R) (a : O) (y : N.AlgebraPoint A),
      Φ A (a • y) = a • Φ A y := by
    intro A a y
    refine IsFactorValue.eq hf hker (hΦ _) ?_
    intro C α x hx
    obtain ⟨C₁, γ, hγ, -, x₁, hx₁⟩ := hf C (N.algebraMapPoints α.hom y)
    apply P.algebraMapPoints_injective γ hγ
    rw [onAlgebraPoints_natural, map_smul, map_smul, ← P.algebraMapPoints_comp]
    rw [← N.algebraMapPoints_comp] at hx₁
    have e := hΦ y C₁ (α ≫ γ) x₁ hx₁
    simp only [CommAlgCat.hom_comp] at e
    rw [← e, ← map_smul]
    apply eq_of_kernel_le hker
    rw [map_smul, hx₁, ← onAlgebraPoints_natural, hx, map_smul, map_smul,
      N.algebraMapPoints_comp]
  refine ⟨ofNatural Φ hnat hadd hsmul, ?_⟩
  apply ext_onAlgebraPoints
  intro A x
  rw [onAlgebraPoints_comp, onAlgebraPoints_ofNatural]
  refine IsFactorValue.eq hf hker (hΦ _) ?_
  intro C α x' hx'
  rw [onAlgebraPoints_natural]
  apply eq_of_kernel_le hker
  rw [hx', onAlgebraPoints_natural]

end Hom

end Langlands.FormalGroup.ModuleLaw
