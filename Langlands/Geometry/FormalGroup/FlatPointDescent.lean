import Langlands.Geometry.FormalGroup.TruncatedPoints
import Langlands.Geometry.FormalGroup.NilpotentAlgebras
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-! # Descent of formal points along faithfully flat algebra maps -/

noncomputable section

universe u v

namespace Langlands.FormalGroup

open CategoryTheory

namespace SeriesPoint

variable {A B : Type*} [CommRing A] [CommRing B] {σ : Type}

/-- The constant coefficient of a coordinate of a base-changed point. -/
@[simp]
theorem constantCoeff_map_val (φ : A →+* B) (x : SeriesPoint A σ Empty) (i : σ) :
    MvPowerSeries.constantCoeff ((x.map φ).val i) =
      φ (MvPowerSeries.constantCoeff (x.val i)) :=
  MvPowerSeries.constantCoeff_map φ (x.val i)

/-- Base change of points along an injective ring map is injective. -/
theorem map_injective (φ : A →+* B) (hφ : Function.Injective φ) :
    Function.Injective (SeriesPoint.map φ : SeriesPoint A σ Empty → SeriesPoint B σ Empty) := by
  intro x y h
  apply SeriesPoint.ext_constantCoeff
  intro i
  apply hφ
  have := congrArg (fun p : SeriesPoint B σ Empty => MvPowerSeries.constantCoeff (p.val i)) h
  simpa only [constantCoeff_map_val] using this

variable [Finite σ]

/-- A point over `B` whose coordinates come from an injective ring map `A → B`
comes from a point over `A`; nilpotence descends by injectivity. -/
theorem exists_map_eq (φ : A →+* B) (hφ : Function.Injective φ) (x : SeriesPoint B σ Empty)
    (hx : ∀ i, MvPowerSeries.constantCoeff (x.val i) ∈ Set.range φ) :
    ∃ w : SeriesPoint A σ Empty, w.map φ = x := by
  choose a ha using hx
  have hnil : ∀ i, IsNilpotent (a i) := by
    intro i
    rw [← IsNilpotent.map_iff hφ, ha i]
    exact x.property.const_coeff i
  refine ⟨SeriesPoint.nilpotentEquiv.symm ⟨a, hnil⟩, ?_⟩
  apply SeriesPoint.ext_constantCoeff
  intro i
  rw [constantCoeff_map_val, ← ha i]
  congr 1

end SeriesPoint

namespace ModuleLaw

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]
variable (M : ModuleLaw O R σ)

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Faithfully flat algebra maps are injective on actual points. -/
theorem algebraMapPoints_injective {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (hφ : φ.hom.toRingHom.FaithfullyFlat) :
    Function.Injective (M.algebraMapPoints φ.hom) :=
  SeriesPoint.map_injective φ.hom.toRingHom hφ.injective

/-- The pushout `B ⊗[A] C` of two coefficient algebra maps out of `A`. -/
def pushout {A B C : CommAlgCat.{v} R} (φ : A ⟶ B) (ψ : A ⟶ C) : CommAlgCat.{v} R :=
  letI : Algebra A B := φ.hom.toRingHom.toAlgebra
  letI : Algebra A C := ψ.hom.toRingHom.toAlgebra
  letI : Algebra R (TensorProduct A B C) :=
    ((algebraMap A (TensorProduct A B C)).comp (algebraMap R A)).toAlgebra
  CommAlgCat.of R (TensorProduct A B C)

/-- The left inclusion `B ⟶ B ⊗[A] C`. -/
def pushoutInl {A B C : CommAlgCat.{v} R} (φ : A ⟶ B) (ψ : A ⟶ C) : B ⟶ pushout φ ψ :=
  letI : Algebra A B := φ.hom.toRingHom.toAlgebra
  letI : Algebra A C := ψ.hom.toRingHom.toAlgebra
  letI : Algebra R (TensorProduct A B C) :=
    ((algebraMap A (TensorProduct A B C)).comp (algebraMap R A)).toAlgebra
  CommAlgCat.ofHom
    { toRingHom := Algebra.TensorProduct.includeLeftRingHom
      commutes' := fun r => by
        change Algebra.TensorProduct.includeLeftRingHom (algebraMap R B r) =
          algebraMap A (TensorProduct A B C) (algebraMap R A r)
        rw [← φ.hom.commutes r]
        exact (Algebra.TensorProduct.includeLeft (R := A) (S := A) (B := C)).commutes
          (algebraMap R A r) }

/-- The right inclusion `C ⟶ B ⊗[A] C`. -/
def pushoutInr {A B C : CommAlgCat.{v} R} (φ : A ⟶ B) (ψ : A ⟶ C) : C ⟶ pushout φ ψ :=
  letI : Algebra A B := φ.hom.toRingHom.toAlgebra
  letI : Algebra A C := ψ.hom.toRingHom.toAlgebra
  letI : Algebra R (TensorProduct A B C) :=
    ((algebraMap A (TensorProduct A B C)).comp (algebraMap R A)).toAlgebra
  CommAlgCat.ofHom
    { toRingHom := (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom
      commutes' := fun r => by
        change (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C))
            (algebraMap R C r) = algebraMap A (TensorProduct A B C) (algebraMap R A r)
        rw [← ψ.hom.commutes r]
        exact (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).commutes
          (algebraMap R A r) }

theorem pushout_comm {A B C : CommAlgCat.{v} R} (φ : A ⟶ B) (ψ : A ⟶ C) :
    φ ≫ pushoutInl φ ψ = ψ ≫ pushoutInr φ ψ := by
  let _ : Algebra A B := φ.hom.toRingHom.toAlgebra
  let _ : Algebra A C := ψ.hom.toRingHom.toAlgebra
  ext a
  change Algebra.TensorProduct.includeLeftRingHom (algebraMap A B a) =
    (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)) (algebraMap A C a)
  exact ((Algebra.TensorProduct.includeLeft (R := A) (S := A) (B := C)).commutes a).trans
    ((Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).commutes a).symm

/-- The left inclusion of a pushout is faithfully flat when the right leg is. -/
theorem pushoutInl_faithfullyFlat {A B C : CommAlgCat.{v} R} (φ : A ⟶ B) (ψ : A ⟶ C)
    (hψ : ψ.hom.toRingHom.FaithfullyFlat) :
    (pushoutInl φ ψ).hom.toRingHom.FaithfullyFlat := by
  let _ : Algebra A B := φ.hom.toRingHom.toAlgebra
  let _ : Algebra A C := ψ.hom.toRingHom.toAlgebra
  have _ : Module.FaithfullyFlat A C := hψ
  have h : (algebraMap B (TensorProduct A B C)).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  exact h

/-- The right inclusion of a pushout is faithfully flat when the left leg is. -/
theorem pushoutInr_faithfullyFlat {A B C : CommAlgCat.{v} R} (φ : A ⟶ B) (ψ : A ⟶ C)
    (hφ : φ.hom.toRingHom.FaithfullyFlat) :
    (pushoutInr φ ψ).hom.toRingHom.FaithfullyFlat := by
  let _ : Algebra A B := φ.hom.toRingHom.toAlgebra
  let _ : Algebra A C := ψ.hom.toRingHom.toAlgebra
  have _ : Module.FaithfullyFlat A B := hφ
  have h : (algebraMap C (TensorProduct A C B)).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have h2 : (Algebra.TensorProduct.comm A C B).toRingEquiv.toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective (Algebra.TensorProduct.comm A C B).bijective
  have e : (pushoutInr φ ψ).hom.toRingHom =
      (Algebra.TensorProduct.comm A C B).toRingEquiv.toRingHom.comp
        (algebraMap C (TensorProduct A C B)) := by
    ext c
    change (1 : B) ⊗ₜ[A] c = Algebra.TensorProduct.comm A C B (algebraMap C _ c)
    rw [Algebra.TensorProduct.algebraMap_apply]
    rfl
  rw [e]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _ h h2

/-- Effective descent of actual points along a faithfully flat algebra map: a point
over `B` whose two pullbacks agree under every pair of maps equalized by `φ` comes
from a point over `A`. -/
theorem exists_algebraMapPoints_eq {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (hφ : φ.hom.toRingHom.FaithfullyFlat) (x : M.AlgebraPoint B)
    (hx : ∀ (C : CommAlgCat.{v} R) (α β : B ⟶ C), φ ≫ α = φ ≫ β →
      M.algebraMapPoints α.hom x = M.algebraMapPoints β.hom x) :
    ∃ w : M.AlgebraPoint A, M.algebraMapPoints φ.hom w = x := by
  let _ : Algebra A B := φ.hom.toRingHom.toAlgebra
  have _ : Module.FaithfullyFlat A B := hφ
  have heq := hx _ _ _ (pushout_comm φ φ)
  change SeriesPoint B σ Empty at x
  refine SeriesPoint.exists_map_eq φ.hom.toRingHom hφ.injective x fun i => ?_
  have hi := congrArg (fun p : SeriesPoint _ σ Empty => MvPowerSeries.constantCoeff (p.val i)) heq
  change MvPowerSeries.constantCoeff (((x : SeriesPoint B σ Empty).map
      (pushoutInl φ φ).hom.toRingHom).val i) =
    MvPowerSeries.constantCoeff (((x : SeriesPoint B σ Empty).map
      (pushoutInr φ φ).hom.toRingHom).val i) at hi
  simp only [SeriesPoint.constantCoeff_map_val] at hi
  have hmem := (Algebra.IsEffective.of_faithfullyFlat (R := A) (S := B)).eqLocus_includeLeft_includeRight
  have : MvPowerSeries.constantCoeff (x.val i) ∈
      Algebra.TensorProduct.includeLeftRingHom.eqLocus
        Algebra.TensorProduct.includeRight.toRingHom (S := TensorProduct A B B) := hi
  rw [← SetLike.mem_coe, hmem] at this
  exact this

/-- Unique descent: the descended point is unique. -/
theorem existsUnique_algebraMapPoints_eq {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (hφ : φ.hom.toRingHom.FaithfullyFlat) (x : M.AlgebraPoint B)
    (hx : ∀ (C : CommAlgCat.{v} R) (α β : B ⟶ C), φ ≫ α = φ ≫ β →
      M.algebraMapPoints α.hom x = M.algebraMapPoints β.hom x) :
    ∃! w : M.AlgebraPoint A, M.algebraMapPoints φ.hom w = x := by
  obtain ⟨w, hw⟩ := M.exists_algebraMapPoints_eq φ hφ x hx
  exact ⟨w, hw, fun w' hw' => M.algebraMapPoints_injective φ hφ (hw'.trans hw.symm)⟩

end ModuleLaw

end Langlands.FormalGroup
