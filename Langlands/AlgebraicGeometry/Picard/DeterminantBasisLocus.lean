import Langlands.AlgebraicGeometry.Picard.DeterminantSections
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Basis tests for actual determinant generation opens -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

/-- A finite tuple is a basis precisely when its coordinate determinant is a unit. -/
theorem basisTuple_bijective_iff_isUnit_det
    {A N : Type u} [CommRing A] [AddCommGroup N] [Module A N]
    {k : ℕ} (b : Module.Basis (Fin k) A N) (s : Fin k → N) :
    (Function.Bijective fun v : Fin k → A ↦ ∑ j, v j • s j) ↔
      IsUnit (b.toMatrix s).det := by
  have hcoord : b.equivFun ∘ (fun v : Fin k → A ↦ ∑ j, v j • s j) =
      (b.toMatrix s).mulVec := by
    funext v
    ext i
    simp [Function.comp_apply, Matrix.mulVec, dotProduct,
      Module.Basis.toMatrix_apply, Module.Basis.equivFun_apply, mul_comm]
  rw [← Function.Bijective.of_comp_iff' b.equivFun.bijective, hcoord,
    ← Matrix.isUnit_iff_isUnit_det]
  exact ⟨fun h ↦ Matrix.mulVec_surjective_iff_isUnit.mp h.2,
    fun h ↦ ⟨Matrix.mulVec_injective_of_isUnit h,
      Matrix.mulVec_surjective_iff_isUnit.mpr h⟩⟩

/-- Invertibility of a restricted section detects inclusion in its basic open. -/
theorem le_basicOpen_iff_isUnit_restrict
    {X : Scheme.{u}} {U V : X.Opens} (hVU : V ≤ U) (f : Γ(X, U)) :
    V ≤ X.basicOpen f ↔ IsUnit (X.presheaf.map (homOfLE hVU).op f) := by
  constructor
  · intro h
    have hunit := (X.presheaf.map (homOfLE h).op).hom.isUnit_map
      (X.toRingedSpace.isUnit_res_basicOpen f)
    have hres : X.presheaf.map (homOfLE h).op
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) =
        X.presheaf.map (homOfLE hVU).op f := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    change IsUnit (X.presheaf.map (homOfLE h).op
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f)) at hunit
    rwa [hres] at hunit
  · intro h
    have heq := X.basicOpen_res f (homOfLE hVU).op
    rw [X.basicOpen_of_isUnit h] at heq
    exact heq.le.trans inf_le_right

/-- Equality of opens contained in a fixed open can be checked on affine subopens. -/
theorem opens_eq_of_affine_tests
    {X : Scheme.{u}} {T U V : X.Opens} (hU : U ≤ T) (hV : V ≤ T)
    (h : ∀ W : X.Opens, IsAffineOpen W → W ≤ T → (W ≤ U ↔ W ≤ V)) : U = V := by
  apply le_antisymm
  · intro x hx
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    exact ((h W hW (hWU.trans hU)).mp hWU) hxW
  · intro x hx
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
    exact ((h W hW (hWV.trans hV)).mpr hWV) hxW

namespace VariableDeterminantFrames

variable {X : Scheme.{u}} {M : X.Modules} {ι : Type u} {T : ι → X.Opens}
  {k : ℕ}
  (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i))
    (ULift.{u} (Fin k)) ≅ M.over (T i))

/-- The determinant section generates on an open exactly when its tuple is a basis
there in the actual module of sections. -/
theorem le_basicOpen_determinantCoefficient_iff
    (s : Fin k → Γ(M, ⊤)) (i : ι) {W : X.Opens} (hW : W ≤ T i) :
    W ≤ X.basicOpen (determinantCoefficient e s i le_rfl) ↔
      Function.Bijective (fun v : Fin k → Γ(X, W) ↦
        ∑ j, v j • M.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (s j)) := by
  rw [le_basicOpen_iff_isUnit_restrict hW, determinantCoefficient_restrict]
  exact (basisTuple_bijective_iff_isUnit_det (basis e i hW) _).symm

/-- Affine-local basis tests identify the actual determinant coefficient open. -/
theorem basicOpen_determinantCoefficient_eq_of_affine_tests
    (s : Fin k → Γ(M, ⊤)) (U : X.Opens)
    (h : ∀ (W : X.Opens), IsAffineOpen W → ∀ i, W ≤ T i →
      (Function.Bijective (fun v : Fin k → Γ(X, W) ↦
        ∑ j, v j • M.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (s j)) ↔
          W ≤ U)) (i : ι) :
    X.basicOpen (determinantCoefficient e s i le_rfl) = T i ⊓ U := by
  apply opens_eq_of_affine_tests (X.basicOpen_le _) inf_le_left
  intro W hW hi
  rw [le_basicOpen_determinantCoefficient_iff e s i hi, le_inf_iff]
  exact (h W hW i hi).trans (and_iff_right hi).symm

/-- An affine cover identified by basis tests makes the actual determinant ample. -/
theorem isAmple_of_affine_basis_tests
    (hT : (⨆ i, T i) = ⊤) [CompactSpace X]
    {α : Type u} (U : α → X.Opens) (hcover : (⨆ a, U a) = ⊤)
    (haffine : ∀ a, IsAffineOpen (U a)) (s : α → Fin k → Γ(M, ⊤))
    (hbasis : ∀ a (W : X.Opens), IsAffineOpen W → ∀ i, W ≤ T i →
      (Function.Bijective (fun v : Fin k → Γ(X, W) ↦
        ∑ j, v j • M.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (s a j)) ↔
          W ≤ U a)) :
    (lineBundle e hT).IsAmple :=
  isAmple_of_affine_basisLoci e hT U hcover haffine s
    (fun a i ↦ basicOpen_determinantCoefficient_eq_of_affine_tests e (s a) (U a)
      (hbasis a) i)

end VariableDeterminantFrames

/-- The affine-local basis criterion for the standard finite locally free determinant. -/
theorem finiteLocallyFreeDeterminant_isAmple_of_affine_basis_tests
    {X : Scheme.{u}} [CompactSpace X] {M : X.Modules}
    (hM : Langlands.Scheme.Modules.HasFiniteLocalBasis M)
    {ι : Type u} {T : ι → X.Opens} {k : ℕ}
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i))
      (ULift.{u} (Fin k)) ≅ M.over (T i))
    (hT : (⨆ i, T i) = ⊤)
    {α : Type u} (U : α → X.Opens) (hcover : (⨆ a, U a) = ⊤)
    (haffine : ∀ a, IsAffineOpen (U a)) (s : α → Fin k → Γ(M, ⊤))
    (hbasis : ∀ a (W : X.Opens), IsAffineOpen W → ∀ i, W ≤ T i →
      (Function.Bijective (fun v : Fin k → Γ(X, W) ↦
        ∑ j, v j • M.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (s a j)) ↔
          W ≤ U a)) :
    (finiteLocallyFreeDeterminant hM).IsAmple :=
  finiteLocallyFreeDeterminant_isAmple_of_affine_basisLoci hM e hT U hcover
    haffine s (fun a i ↦
      VariableDeterminantFrames.basicOpen_determinantCoefficient_eq_of_affine_tests
        e (s a) (U a) (hbasis a) i)

end Langlands.AlgebraicGeometry.Picard
